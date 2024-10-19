from typing import (
    NewType,
    Generator,
    NamedTuple,
    Iterable,
    Callable,
    TypeVar,
    Sequence,
    Self,
)
from pathlib import Path
from multiprocessing import Process

DEFAULT_RECURSION_FUEL = 1_000_000
VERBOSE = False

#### BEGIN BASIC DEFINITIONS ####
Lit = NewType("Lit", int)
Clause = NewType("Clause", frozenset[Lit])
Cnf = NewType("Cnf", frozenset[Clause])


def neg(l: Lit) -> Lit:
    return Lit(-l)


def cnf(*clauses: Iterable[int]) -> Cnf:
    return Cnf(
        frozenset(Clause(frozenset(Lit(l) for l in clause))
                  for clause in clauses)
    )


def show_clause(clause: Clause) -> str:
    return "∨".join(map(str, clause))


def show_cnf(cnf: Cnf) -> str:
    return "∧".join("(" + show_clause(clause) + ")" for clause in cnf)


class Model:
    class Item(NamedTuple):
        lit: Lit
        deps: frozenset[Lit] | None
        """
        If present, the variables which made this term take the current value.

        Empty dependencies is not the same as having no dependencies. Having no
        dependencies means that this assignment was made with no particular
        purpose. It marks the assignment as a decision. If there are dependencies,
        it means this assignment was the result of either a unit propagation or a
        backtracked decision.

        These are needed in order to learn the conflicting clauses. In particular,
        we have that all(m(l) is False for l in deps), and therefore
        all(m(l) is False for l in deps) ==> m(lit) is True
        """

        def __repr__(self) -> str:
            dep_str = "" if not self.deps else "(" + ",".join(map(str, self.deps)) + ")"
            return f"{self.lit}" + dep_str

    _data: list[Item] = []

    #### BEGIN CACHE ####
    _items_cache: dict[Lit, tuple[bool, frozenset[Lit] | None]]
    _pos_cache: dict[Lit, int]

    def _extend_pos_cache(self, items: Sequence[Item], offset: int) -> None:
        self._pos_cache |= {it.lit: offset + i for i, it in enumerate(items)} | {
            Lit(-it.lit): offset + i for i, it in enumerate(items)
        }

    def _invalidate_pos_cache(self, keys: Iterable[Lit]) -> None:
        for key in keys:
            self._pos_cache.pop(key)
            self._pos_cache.pop(neg(key))

    def _extend_items_cache(self, items: Sequence[Item]) -> None:
        self._items_cache |= {it.lit: (True, it.deps) for it in items} | {
            Lit(-it.lit): (False, it.deps) for it in items
        }

    def _invalidate_items_cache(self, keys: Iterable[Lit]) -> None:
        for key in keys:
            self._items_cache.pop(key)
            self._items_cache.pop(neg(key))

    def _extend(self, items: Sequence[Item]) -> "Model":
        n = len(self._data)
        self._extend_pos_cache(items, offset=n)
        self._extend_items_cache(items)
        self._data.extend(items)
        assert all(
            self(it.lit) != self(neg(it.lit)) for it in items
        ), f"Contradiction in the assignment of a literal in {items}"
        assert all(
            self.deps(it.lit) == self.deps(neg(it.lit)) for it in items
        ), f"Contradiction in status of literal in {items}"
        return self

    #### END CACHE ####

    #### BEGIN BUILDERS ####
    @classmethod
    def from_lits(cls, *lits: int) -> Self:
        data = [cls.Item(Lit(l), None) for l in lits]
        return cls(data)

    def __init__(self, data: list[Item] = list()) -> None:
        self._data = []
        self._items_cache = {}
        self._pos_cache = {}
        self._extend(data)

    #### END BUILDERS ####

    #### BEGIN DATA PROXY ####
    def __repr__(self) -> str:
        return repr(self._data)

    def __iter__(self) -> Generator[Item, None, None]:
        yield from self._data

    def __len__(self) -> int:
        return len(self._data)

    def __getitem__(self, i: int) -> Item:
        return self._data[i]

    #### END DATA PROXY ####

    #### BEGIN MODEL API ####
    def __call__(self, q: Lit) -> bool | None:
        entry = self._items_cache.get(q, None)
        if entry is not None:
            return entry[0]

    def pos(self, q: Lit) -> int:
        return self._pos_cache.get(q, None) or self._pos_cache[Lit(-q)]

    def deps(self, q: Lit) -> frozenset[Lit] | None:
        entry = self._items_cache.get(q, None)
        if entry is not None:
            return entry[1]

    def decide(self, lit: Lit) -> "Model":
        """Adds a new literal assignment, without dependencies."""
        it = Model.Item(lit=lit, deps=None)
        return self._extend([it])

    def propagate(self, items: Iterable[tuple[Lit, frozenset[Lit]]]) -> "Model":
        """Adds a new literal assignment, with some dependencies on why this literal was chosen."""
        propagated = [Model.Item(lit=lit, deps=deps) for lit, deps in items]
        self._extend(propagated)
        return self

    def backtrack(self, size: int) -> "Model":
        """Backtracks until the given choice"""
        assert size >= 0, "Cannot resize to negative value"
        invalidated_keys = [key for key, _ in self._data[size:]]
        self._invalidate_pos_cache(invalidated_keys)
        self._invalidate_items_cache(invalidated_keys)
        self._data = self._data[:size]
        return self

    def weak_eq(self, other: "Model") -> bool:
        """Equality without considering decided or undecided literals."""
        self_literals = {it.lit for it in self._data}
        other_literals = {it.lit for it in other._data}
        return self_literals == other_literals

    def to_clause(self) -> Clause:
        """Give the clause which characterizes the state."""
        return Clause(frozenset(it.lit for it in self._data))

    #### END MODEL API ####


#### END BASIC DEFINITIONS ####

#### BEGIN CDCL IMPLEMENTATION ####
T = TypeVar("T")


def fixpoint(f: Callable[[T], T], init: T, fuel: int = DEFAULT_RECURSION_FUEL) -> T:
    x = init
    for _ in range(fuel):
        y = f(x)
        if x == y:
            return x
        else:
            x = y
    raise TimeoutError(f"Couldn't find fix point in {fuel} iterations")


def unit_propagation(f: Cnf, m: Model, fuel: int = DEFAULT_RECURSION_FUEL) -> Model:
    for _ in range(fuel):
        undecided_clauses = [
            clause
            for clause in f
            if not all(m(l) for l in clause) and any(m(l) is None for l in clause)
        ]
        unassigned_per_clause = [
            [l for l in clause if m(l) is None] for clause in undecided_clauses
        ]
        can_propagate = {
            unassigned[0]: clause - {unassigned[0]}
            for clause, unassigned in zip(undecided_clauses, unassigned_per_clause)
            if len(unassigned) == 1
        }
        conflicts = {
            abs(lit) for lit in can_propagate.keys() if neg(lit) in can_propagate
        }
        to_propagate = [
            (lit, deps) for lit, deps in can_propagate.items() if lit not in conflicts
        ]
        if not to_propagate:
            return m
        m.propagate(to_propagate)
    return m


def analyze_conflict(
    conflict: Iterable[Lit], m: Model
) -> tuple[int, frozenset[Lit]] | None:
    to_process = [l for l in conflict]
    decided_literals: list[Lit] = []
    while to_process:
        # if len(to_process) == 1:
        #     # We could stop the search here and learn this clause.
        #     return frozenset(decided_literals + to_process)
        processing = to_process
        to_process = []
        while processing:
            curr = processing.pop()
            deps = m.deps(curr)
            if deps is None:
                decided_literals.append(curr)
            else:
                to_process.extend(deps)
    if decided_literals:
        new_size = max(p for lit in decided_literals if (p := m.pos(lit)) is not None)
        return new_size, frozenset(decided_literals)
    # If there are no decided literals, it means we have reached a contradiction


def decide(m: Model, f: Cnf) -> Model:
    # We need to make sure that we try all possibilities
    # in the end. Do we have a rule to keep track of whether
    # we used 1 or 0 when backtracking?
    lit = next((lit for clause in f for lit in clause if m(lit) is None), None)
    assert lit is not None, "Can't decide for a model which is already decide"
    return m.decide(lit)


def find_conflict(f: Cnf, m: Model) -> Clause | None:
    return next((clause for clause in f if all(m(l) is False for l in clause)), None)


def find_undecided_literal(f: Cnf, m: Model) -> Lit | None:
    return next(
        (
            lit
            for clause in f
            if not any(m(l) is True for l in clause)
            and (lit := next((l for l in clause if m(l) is None), None))
        ),
        None,
    )


def nb_vars(f: Cnf) -> int:
    return len({abs(l) for clause in f for l in clause})


def cdcl(f: Cnf, fuel: int = DEFAULT_RECURSION_FUEL) -> Model | None:
    m = unit_propagation(f, Model(), fuel=fuel)
    for _ in range(fuel):
        while conflict := find_conflict(f, m):
            if VERBOSE:
                print(f"Found conflict {show_clause(conflict)}")
            conflict_recovery = analyze_conflict(conflict, m)
            if not conflict_recovery:
                return None
            kept_literals, learned_clause = conflict_recovery
            if VERBOSE:
                print(f"Learned {show_clause(learned_clause)}")
            f = Cnf(f | {Clause(learned_clause)})
            m.backtrack(kept_literals)
            m = unit_propagation(f, m, fuel=fuel)

        lit = find_undecided_literal(f, m)
        if lit is not None:
            if VERBOSE:
                print(f"Decided {lit}")
            m.decide(lit)
            m = decide(m, f)
            m = unit_propagation(f, m, fuel=fuel)
        else:
            return m
    raise TimeoutError(f"Couldn't find satisfiable formula with {fuel} iterations")


#### END CDCL IMPLEMENTATION ####


#### BEGIN CDCL TESTING ####
def test_1() -> None:
    f = cnf((1, 2), (-2, 3), (-3, 4), (-4, 5), (6, 7))
    m = Model.from_lits(-1)
    m = unit_propagation(f, m, fuel=1)
    assert m.weak_eq(Model.from_lits(-1, 2)), f"{m}"
    m = unit_propagation(f, m, fuel=1)
    assert m.weak_eq(Model.from_lits(-1, 2, 3)), f"{m}"
    m = unit_propagation(f, m, fuel=1)
    assert m.weak_eq(Model.from_lits(-1, 2, 3, 4)), f"{m}"
    m = unit_propagation(f, m, fuel=1)
    assert m.weak_eq(Model.from_lits(-1, 2, 3, 4, 5)), f"{m}"
    m = unit_propagation(f, m, fuel=1)
    assert m.weak_eq(Model.from_lits(-1, 2, 3, 4, 5)), f"{m}"


def test_2() -> None:
    f = cnf((1, 2), (-2, 3), (-3, 1))
    m = Model.from_lits(-1)
    m = unit_propagation(f, m)
    conflict_recovery = analyze_conflict((Lit(-2), Lit(3)), m)
    assert conflict_recovery, "This conflict should have been recoverable"
    actual = conflict_recovery[1]
    assert actual == frozenset([Lit(1)]), f"{actual}"


def test_3() -> None:
    f = cnf(
        (-1, 2), (-1, 3, 5), (-2, 4), (-3, -4), (1, 5, -2), (2, 3), (2, -3, 7), (6, -5)
    )
    m = Model.from_lits(1, -6, -7)
    m = unit_propagation(f, m)
    conflict = find_conflict(f, m)
    assert conflict
    assert conflict == Clause(frozenset((Lit(-3), Lit(-4))))
    conflict_recovery = analyze_conflict(conflict, m)
    assert conflict_recovery
    kept_literals, learned_clause = conflict_recovery
    assert kept_literals == 1
    expected = frozenset({Lit(-1), Lit(6)})
    assert learned_clause == expected


def ok_pahts() -> Iterable[Path]:
    tests = Path(".") / "tests/"
    ok_tests = tests / "OK"
    yield from ok_tests.rglob("*.cnf")


def ko_pahts() -> Iterable[Path]:
    tests = Path(".") / "tests/"
    ko_tests = tests / "KO"
    yield from ko_tests.rglob("*.cnf")


def read_dimacs(file: Path) -> Cnf:
    with file.open() as f:
        return cnf(
            *[
                map(int, line.strip().split()[:-1])
                for line in f.readlines()[1:]
                if not line.startswith("c") and not line.startswith("p")
            ]
        )


def paths_by_size() -> Iterable[tuple[Path, bool]]:
    ok_paths = [*ok_pahts()]
    ko_paths = [*ko_pahts()]
    yield from sorted(
        (
            (p, veredict)
            for paths in (
                zip([*ok_paths], [True] * len(ok_paths)),
                zip([*ko_paths], [False] * len(ko_paths)),
            )
            for p, veredict in paths
        ),
        key=lambda p: p[0].stat().st_size,
    )


def run_test(p: Path, success: bool) -> bool | None:
    try:
        model = cdcl(read_dimacs(p))
    except TimeoutError:
        return None

    if success:
        return model is not None
    else:
        return model is None


def test_all(fuel: int = DEFAULT_RECURSION_FUEL) -> None:
    for path, veredict in paths_by_size():
        print(path)
        res = run_test(path, veredict)
        if res is None:
            print("⏰")
        elif res is True:
            print("✅")
        elif res is False:
            print("❌")


def test_with_timeout(timeout: float = 5.0) -> None:
    for path, veredict in paths_by_size():
        print(path)
        def target() -> None:
            res = run_test(path, veredict)
            if res is None:
                print(f"⏰Timed out. {timeout=}s")
            elif res is True:
                print("✅")
            elif res is False:
                print("❌")
        f = Process(target=target)
        f.start()
        f.join(timeout=timeout)
        if f.exitcode is None:
            print(f"⏰Timed out. {timeout=}s")
#### END CDCL TESTING ####


def main() -> None:
    import sys

    if 1 < len(sys.argv):
        test = Path(sys.argv[1])
        model = cdcl(read_dimacs(test))
        print(model)
        return

    # unit_propagation
    print("test_1")
    test_1()

    # analyze_conflict
    print("test_2")
    test_2()
    print("test_3")
    test_3()

    # Exhaustive
    test_with_timeout(timeout=5.0)


if __name__ == "__main__":
    main()
