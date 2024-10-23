"""Module providing an implementation of CDCL"""

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
import random


DEFAULT_RECURSION_FUEL = 1_000_000
VERBOSE = False

#### BEGIN BASIC DEFINITIONS ####
Lit = NewType("Lit", int)
Clause = NewType("Clause", frozenset[Lit])
Cnf = NewType("Cnf", frozenset[Clause])


def neg(lit: Lit) -> Lit:
    """
    Negation of lit.
    x -> ¬x
    ¬x -> x
    """
    return Lit(-lit)


def cnf(*clauses: Iterable[int]) -> Cnf:
    return Cnf(
        frozenset(Clause(frozenset(Lit(lit) for lit in clause))
                  for clause in clauses)
    )


def show_clause(clause: Clause) -> str:
    return "∨".join(map(str, clause))


def show_cnf(cnf: Cnf) -> str:
    return "∧".join("(" + show_clause(clause) + ")" for clause in cnf)


class Model:
    """
    Partial model in propositional logic
    """
    class Item(NamedTuple):
        """
        An assigned literal and its dependencies.

        Attirbutes
        ----------
        lit : Lit
        deps : Optional[set[Lit]]
            a list of literals whose falsity entailed llit's value

            Empty dependencies is not the same as having no dependencies.
            Having no dependencies means that this assignment was made with
            no particular purpose. It marks the assignment as a decision. If
            there are dependencies, it means this assignment was the result of
            either a unit propagation or a backtracked decision.

            These are needed in order to learn the conflicting clauses. In
            particular, we have that all(m(l) is False for l in deps), and
            therefore all(m(l) is False for l in deps) ==> m(lit) is True.
        """
        lit: Lit
        deps: frozenset[Lit] | None

        def __repr__(self) -> str:
            dep_str = ""
            if self.deps:
                dep_str = "(" + ",".join(map(str, self.deps)) + ")"
            return f"{self.lit}" + dep_str

    _data: list[Item] = []

    #### BEGIN CACHE ####
    _items_cache: dict[Lit, tuple[bool, frozenset[Lit] | None]]
    _pos_cache: dict[Lit, int]

    def _extend_pos_cache(self, items: Sequence[Item], offset: int) -> None:
        self._pos_cache |= {
            it.lit: offset + i for i, it in enumerate(items)
        }
        self._pos_cache |= {
            neg(it.lit): offset + i for i, it in enumerate(items)
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
        data = [cls.Item(Lit(lit), None) for lit in lits]
        return cls(data)

    @classmethod
    def from_file(cls, path: Path) -> Self:
        with path.open("r") as f:
            n = f.readline()
            lits_str = f.readline().split()
            data = []
            for i, lit_str in enumerate(lits_str):
                lit: Lit
                match lit_str:
                    case "1":
                        lit = i
                    case "0":
                        lit = -i
                    case "?":
                        continue
                data.append(cls.Item(lit, None))
            data = list(map(int, lits_str))
            return cls(data)

    def __init__(self, data: list[Item] | None = None) -> None:
        self._data = []
        self._items_cache = {}
        self._pos_cache = {}
        if data is not None:
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
        """
        Return the truth value of q under the partial assignment, or None if q
        is not assigned.
        """
        entry = self._items_cache.get(q, None)
        if entry is not None:
            return entry[0]
        return None

    def pos(self, q: Lit) -> int:
        return self._pos_cache.get(q, None) or self._pos_cache[neg(q)]

    def deps(self, q: Lit) -> frozenset[Lit] | None:
        """
        Given a literal q, return the list of falsified literals which led to
        its assignment.

        Precondtions:
            - q is assigned in the model.
        """
        _, dependencies = self._items_cache.get(q, None)
        return dependencies

    def decide(self, lit: Lit) -> "Model":
        """Adds a new literal assignment, without dependencies."""
        it = Model.Item(lit=lit, deps=None)
        return self._extend([it])

    def propagate(
        self,
        items: Iterable[tuple[Lit, frozenset[Lit]]]
    ) -> "Model":
        """
        Adds a new literal assignment, with some dependencies on why this
        literal was chosen.
        """
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

    def entails(self, f: set[frozenset[Lit]]) -> bool | None:
        for clause in f:
            clause_entailed = False
            for lit in clause:
                if self(lit) is True:
                    clause_entailed = True
                    break
                if self(lit) is None:
                    return None
            if not clause_entailed:
                return False
        return True

    def __str__(self) -> str:
        num_var = max(abs(lit) for lit, _ in self._data)
        res = f"{num_var}\n"
        for var in range(1, num_var+1):
            res += " "
            if self(var) is False:
                res += "0"
            elif self(var) is True:
                res += "1"
            else:
                res += "?"
        return res

    #### END MODEL API ####


class TwoWatchList:
    """
    Keeps track of each clause by indexing precisely two literals.
    Doesn't support clauses with only one literal.

    Methods
    -------
    watch_clause(self, clause):
        use once for every clause with at least two literals
    get_clauses(self, lit: Lit)
    get_literals(self, lit: Lit)

    Usage
    -----
    To iterate over the indexed clauses, just do
    ...
    for clause in watch_list:
        ...
    """
    def __init__(self, literals: list[Lit] | None):
        self.lit_to_clauses: dict[Lit, set[frozenset[Lit]]] = {}
        self.clause_to_lits: dict[frozenset[Lit], set[Lit]] = {}
        for lit in literals:
            self.lit_to_clauses[lit] = set()
            self.lit_to_clauses[neg(lit)] = set()

    def watch_clause(self, clause):
        """
        Indexes two literals in a clause.
        """
        if len(clause) < 2:
            raise ValueError("A clause cannot be indexed if it has only one or"
                             " zero literal")
        l1, l2, *_ = clause
        self.lit_to_clauses[l1].add(clause)
        self.lit_to_clauses[l2].add(clause)
        self.clause_to_lits[clause] = {l1, l2}

    def change_watched(self, clause, old_lit, new_lit):
        """
        Removes clause from the indexing of old_lit that got assigned false to
        add it to new_lit.
        """
        self.lit_to_clauses[old_lit].remove(clause)
        self.clause_to_lits[clause].remove(old_lit)
        self.lit_to_clauses[new_lit].add(clause)
        self.clause_to_lits[clause].add(new_lit)

    def get_clauses(self, lit: Lit) -> set[frozenset[Lit]]:
        """
        Returns a set of all clauses which are watched using lit.
        """
        return self.lit_to_clauses[lit]

    def get_lits(self, clause) -> set[Lit]:
        """
        Returns a set containing the two literals watched in clause.
        """
        return self.clause_to_lits[clause]

    def __iter__(self):
        return iter(self.clause_to_lits.keys())


#### END BASIC DEFINITIONS ####

#### BEGIN CDCL IMPLEMENTATION ####
T = TypeVar("T")


def fixpoint(
    f: Callable[[T], T],
    init: T,
    fuel: int = DEFAULT_RECURSION_FUEL
) -> T:
    x = init
    for _ in range(fuel):
        y = f(x)
        if x == y:
            return x
        x = y
    raise TimeoutError(f"Couldn't find fix point in {fuel} iterations")


def choose_watched(model, watch_list, clause) -> Lit | None:
    """
    Chooses a new literal to watch. We want it to be unassigned,
    and it must not already be watched.
    """
    for lit in clause:
        if (model(lit) is not False
                and clause not in watch_list.get_clauses(lit)):
            return lit
    return None


def unit_propagation(
    m: Model,
    watch_list: TwoWatchList,
    entry_point: Lit
):
    """
    Finds all conclusions from a model given a formula encoded as a watch
    data structure.
    @pre for each clause c in the formula, there are precisely two literals l
    such that c is in watch[l]. Those literals are unassigned in m except
    entry_point which is false.
    @post All consequences from the current argument given the formula encoded
    in watch are found.
    """
    def unit(clause: Clause) -> Lit | None:
        """
        Returns the unassigned literal if the clause is a unit.
        If it's not, returns None.
        """
        unassigned_literal = None
        for lit in clause:
            if m(lit) is True:  # If there's a true literal, it is not a unit
                return None
            if m(lit) is None and unassigned_literal is None:
                # First unassigned literal, we keep it in memory
                unassigned_literal = lit
            elif m(lit) is None:
                # This is the second unassigned literal, not a unit clause
                return None
        return unassigned_literal

    to_swap = []
    to_propagate = []
    for clause in watch_list.get_clauses(entry_point):
        u = unit(clause)
        if u is None:  # The clause is not a unit
            # If possible, we watch another literal because we don't want to
            # watch false literals when others are unassigned.
            to_swap.append(clause)
        else:  # The clause is a unit and u is unassigned
            to_propagate.append((u, clause-{u}))

    for clause in to_swap:  # Literals from non-unit clauses
        lit = choose_watched(m, watch_list, clause)
        if lit is None:  # We reached a contradiction
            continue
        watch_list.change_watched(clause, entry_point, lit)

    for u, deps in to_propagate:  # Literals from unit clauses
        if m(u) is not None:
            continue
        if VERBOSE:
            print(f"Propagated {u}({deps})")
        m.propagate([(u, deps)])
        unit_propagation(m, watch_list, neg(u))


def analyze_conflict(
    conflict: Iterable[Lit],
    m: Model
) -> tuple[int, frozenset[Lit]] | None:
    to_process = list(conflict)
    decided_literals: list[Lit] = []
    while to_process:
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
        new_size = min(p for lit in decided_literals
                       if (p := m.pos(lit)) is not None)
        return new_size, frozenset(decided_literals)
    # If there are no decided literals, it means we have reached a
    # contradiction


def find_conflict(m: Model, watch_list: TwoWatchList) -> Clause | None:
    """
    Efficiently identify a clause whose literals are all false by testing only
    two literals in it.
    """
    for clause in watch_list:
        l1, l2 = watch_list.get_lits(clause)
        if m(l1) is False and m(l2) is False:
            return clause
    return None


def find_undecided_literal(
    literals: list[Lit],
    m: Model, watch_list
) -> Lit | None:
    """
    Chooses a unassigned literal under partial model m according to some
    heuristic. If all literals are assigned, return None.
    """
    best = []
    best_length = float('-inf')
    for lit in literals:
        if m(lit) is not None:
            continue
        watched_clauses = len(watch_list.get_clauses(lit))
        if watched_clauses > best_length:
            best_length = watched_clauses
            best = [lit]
        elif watched_clauses == best_length:
            best.append(lit)
    if not best:
        return None
    return -random.choice(best)


def watch_clause(watch, clause_watched, clause):
    """
    Selects to literals in clause and watch them.
    """
    l1, l2, *_ = clause
    watch[l1].add(clause)
    watch[l2].add(clause)
    clause_watched[clause] = {l1, l2}


def propagate_units(m: Model, units, watch_list):
    """
    Set every literal u in units to true and propagate. No literal can be false
    """
    for u in units:
        if m(u) is True:
            continue
        if VERBOSE:
            print(f"Found {u} (unit)")
        m.propagate([(u, frozenset())])
        unit_propagation(m, watch_list, neg(u))


def get_model(f: Cnf, fuel: int = DEFAULT_RECURSION_FUEL) -> Model | None:
    """
    Returns a model satisfying f is f is SAT and None otherwise.
    fuel gives a threshold on the maximum number of iterations of CDCL.
    """
    m = Model()

    literals = [lit for clause in f for lit in clause]
    watch_list = TwoWatchList(literals)
    units = []
    for clause in f:
        try:
            watch_list.watch_clause(clause)
        except ValueError:  # There is only one literal in clause
            u, *_ = clause
            units.append(u)

    propagate_units(m, units, watch_list)

    for _ in range(fuel):
        while conflict := find_conflict(m, watch_list):  # Backtracking
            conflict_recovery = analyze_conflict(conflict, m)
            if not conflict_recovery:
                return None
            kept_literals, learned_clause = conflict_recovery
            f |= frozenset({learned_clause})  # Add the clause to f
            m.backtrack(kept_literals)
            try:  # Take care of watching the new clause.
                watch_list.watch_clause(learned_clause)
            except ValueError:
                u, *_ = learned_clause
                propagate_units(m, [u], watch_list)

            if VERBOSE:
                print(f"Found conflict {conflict}")
                print(f"Learned {learned_clause}")

        # Take any literal, set it to True, propagate.
        lit = find_undecided_literal(literals, m, watch_list)
        if lit is None:  # We decided every literal! Yeepi
            return m
        if VERBOSE:
            print(f"Decided {lit}")
        m.decide(lit)
        unit_propagation(m, watch_list, neg(lit))
    raise TimeoutError("Couldn't find satisfiable formula with"
                       f"{fuel} iterations")


#### END CDCL IMPLEMENTATION ####


#### BEGIN CDCL TESTING ####
def read_dimacs(file: Path) -> Cnf:
    with file.open() as f:
        return cnf(
            *[
                map(int, line.strip().split()[:-1])
                for line in f.readlines()[1:]
                if not line.startswith("c") and not line.startswith("p")
            ]
        )
#### END CDCL TESTING ####


if __name__ == "__main__":
    pass
