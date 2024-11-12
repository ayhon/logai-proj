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


DEFAULT_RECURSION_FUEL = 10_000_000
VERBOSE = False

#### BEGIN BASIC DEFINITIONS ####
Lit = NewType("Lit", int)
Clause = NewType("Clause", frozenset[Lit])
Cnf = NewType("Cnf", set[Clause])


def neg(lit: Lit) -> Lit:
    """
    Negation of lit.
    x -> ¬x
    ¬x -> x
    """
    return Lit(-lit)


def cnf(*clauses: Iterable[int]) -> Cnf:
    return Cnf(
        set(Clause(frozenset(Lit(lit) for lit in clause))
            for clause in clauses)
    )


def show_clause(clause: Clause) -> str:
    return "∨".join(map(str, clause))


def show_cnf(f: Cnf) -> str:
    return "∧".join("(" + show_clause(clause) + ")" for clause in f)


class Model:
    """
    Represents a partial model, i.e. an assignment of a subset of the
    variables to True or False. Variables not assigned are considered "None".
    """
    def __init__(self, literals: Iterable[Lit]):
        self.assigned_lits: set[Lit] = set()
        self.unassigned_lits = set()
        for lit in literals:
            self.unassigned_lits.add(lit)
            self.unassigned_lits.add(neg(lit))
        # Literals making this literal true
        self.dependencies: dict[Lit, set[Lit]] = {}
        # Literals made true by this literal
        self.dependent_lits: dict[Lit, set[Lit]] = {}
        self.positions: dict[Lit, int] = {}
        self.number_decided = 0

    def entails(self, f: Cnf):
        """
        Checks that all clauses of f are True under the model.
        """
        return all(
            any(lit in self.assigned_lits for lit in clause) for clause in f
        )

    def get_dependencies(self, lit: Lit):
        """
        Return the dependencies of a lit assigned to False, i.e. the literals
        responsible for its falseness.
        """
        return self.dependencies[neg(lit)]

    def decide(self, lit: Lit):
        """
        We make a literal true without any constraint forcing us to do us.
        It has no dependencies (it wasn't made true by any lit), but can make
        other literals true.
        """
        assert self(lit) is None
        self.assigned_lits.add(lit)
        self.dependencies[lit] = None
        self.dependent_lits[lit] = set()
        self.unassigned_lits.remove(lit)
        self.unassigned_lits.remove(neg(lit))

        self.positions[lit] = self.number_decided
        self.number_decided += 1

    def propagate(self, lit: Lit, parents: Iterable[Lit]):
        """
        A literal lit was made true by parents. It will inherit its parents
        dependencies. It cannot have literals depending on it.
        """
        assert self(lit) is None
        self.assigned_lits.add(lit)
        # Inheriting of dependencies
        deps = set()
        for p in parents:
            p_deps = self.dependencies[neg(p)]
            if p_deps is None:  # Parent was decided
                deps.add(p)
            else:
                deps |= p_deps
        self.dependencies[lit] = deps
        # Tracking dependencies
        for dep in deps:
            assert self(dep) is False, "Dep is not False"
            self.dependent_lits[neg(dep)].add(lit)
        self.dependent_lits[lit] = None
        self.unassigned_lits.remove(lit)
        self.unassigned_lits.remove(neg(lit))
        self.positions[lit] = None

    def backtrack(self, lits: Iterable[Lit]):
        """
        Takes a list of literals whose falsity produced a conflict and
        unassign them. It also unassigns literals depending on them.
        """
        for lit in lits:
            self.number_decided -= 1
            to_remove = neg(lit)
            self.assigned_lits.remove(to_remove)
            self.unassigned_lits.add(to_remove)
            self.unassigned_lits.add(neg(to_remove))
            for child in self.dependent_lits[to_remove].copy():
                for dep in self.dependencies[child]:
                    self.dependent_lits[neg(dep)].remove(child)
                self.unassigned_lits.add(child)
                self.unassigned_lits.add(neg(child))
                self.assigned_lits.remove(child)

    @classmethod
    def from_file(cls, path: Path) -> Self:
        with path.open("r") as f:
            n = int(f.readline())
            m = Model(range(1, n+1))
            lits_str = f.readline().split()
            for i, lit_str in enumerate(lits_str):
                match lit_str:
                    case "1":
                        m.decide(Lit(i+1))
                    case "0":
                        m.decide(neg(Lit(i+1)))
                    case "?":
                        continue
            return m

    def __call__(self, lit: Lit):
        if lit in self.assigned_lits:
            return True
        if neg(lit) in self.assigned_lits:
            return False
        return None

    def __str__(self):
        literals = ({abs(lit) for lit in self.assigned_lits}
                    | {abs(lit) for lit in self.unassigned_lits})
        n = max(literals)
        return f"{n}\n" + " ".join(
                ("1" if lit in self.assigned_lits else "0")
                for lit in range(1, n+1)
            )


class TwoWatchList:
    """
    Keeps track of each clause by indexing precisely two literals.
    Doesn't support clauses with only one literal.

    Methods
    -------
    watch_clause(self, clause):
        use once for every clause with at least two literals
    get_clauses(self, lit: Lit)
        set of clauses in which lit is watched
    get_literals(self, lit: Lit)
        set of watched literals in the clause
    change_watched(self, clause, old_lit, new_lit)
        updates a watched literal in the clause
    """
    def __init__(self, literals: list[Lit]) -> None:
        self.lit_to_clauses: dict[Lit, set[Clause]] = {}
        self.clause_to_lits: dict[Clause, set[Lit]] = {}
        for lit in literals:
            self.lit_to_clauses[lit] = set()
            self.lit_to_clauses[neg(lit)] = set()

    def watch_learned_clause(self, clause: Clause, m: Model) -> None:
        if len(clause) < 2:
            raise ValueError("A clause cannot be indexed if it has only one or"
                             " zero literal")
        l1 = None
        for lit in clause:
            if m(lit) is not False:
                l1 = lit
                break
        l2 = None
        for lit in clause:
            if lit == l1:
                continue
            l2 = lit
            if m(lit) is not False:
                break
        assert l1 is not None and l2 is not None
        self.lit_to_clauses[l1].add(clause)
        self.lit_to_clauses[l2].add(clause)
        self.clause_to_lits[clause] = {l1, l2}

    def watch_clause(self, clause: Clause) -> None:
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

    def change_watched(self,
                       clause: Clause,
                       old_lit: Lit,
                       new_lit: Lit) -> None:
        """
        Removes clause from the indexing of old_lit that got assigned false to
        add it to new_lit.
        """
        self.lit_to_clauses[old_lit].remove(clause)
        self.clause_to_lits[clause].remove(old_lit)
        self.lit_to_clauses[new_lit].add(clause)
        self.clause_to_lits[clause].add(new_lit)

    def get_clauses(self, lit: Lit) -> set[Clause]:
        """
        Returns a set of all clauses which are watched using lit.
        """
        return self.lit_to_clauses[lit]

    def get_lits(self, clause: Clause) -> set[Lit]:
        """
        Returns a set containing the two literals watched in clause.
        """
        return self.clause_to_lits[clause]

    def clauses(self) -> set[Clause]:
        return set(self.clause_to_lits.keys())

    def literals(self) -> set[Lit]:
        return set(self.lit_to_clauses.keys())

    def __iter__(self) -> Generator[Clause, None, None]:
        yield from iter(self.clause_to_lits.keys())


#### END BASIC DEFINITIONS ####

#### BEGIN CDCL IMPLEMENTATION ####


def unit_propagation(
    m: Model,
    watch_list: TwoWatchList,
    entry_point: Lit,
    conflicts=None
) -> set[Clause]:
    """
    Finds all conclusions from a model given a formula encoded as a watch
    data structure.
    @pre for each clause c in the formula, there are precisely two literals l
    such that c is in watch[l]. Those literals are unassigned in m except
    entry_point which is false.
    @post All consequences from the current argument given the formula encoded
    in watch are found.
    """
    def find_unwatched(clause: Clause) -> tuple[Lit | None, bool | None]:
        """
        Returns a non-False literal if it exists and information about the
        clause. The second value is None if a True literal is in the  clause.
        Otherwise, it returns True if exactly one literal is None and False
        otherwise.
        If there are many literals assigned to None, it is guarenteed that if
        one is returned, it is not watched.
        """
        l1, l2 = watch_list.get_lits(clause)
        ml1 = m(l1)
        ml2 = m(l2)
        if ml1 is True:
            return l1, None
        if ml2 is True:
            return l2, None
        unassigned_lit: Lit | None = None
        watched_lits = watch_list.get_lits(clause)
        alone = True
        for lit in clause:
            mlit = m(lit)
            if mlit is True:
                return lit, None
            if mlit is None:
                if unassigned_lit is not None:
                    alone = False
                    if lit not in watched_lits:
                        unassigned_lit = lit
                else:
                    unassigned_lit = lit
        return unassigned_lit, alone

    if conflicts is None:
        conflicts = set()
    for clause in watch_list.get_clauses(entry_point).copy():
        if entry_point not in watch_list.get_lits(clause):
            continue
        lit, alone = find_unwatched(clause)
        if lit is None:
            conflicts.add(clause)
        else:
            if lit not in watch_list.get_lits(clause):
                watch_list.change_watched(clause, entry_point, lit)
            if alone is True:
                deps = clause - {lit}
                m.propagate(lit, deps)
                unit_propagation(m, watch_list, neg(lit), conflicts)

    return conflicts


def analyze_conflict(
    conflict: Iterable[Lit],
    m: Model,
) -> Clause:
    assert all(m(lit) is False for lit in conflict), "Clause is not False"
    deps = set()
    for lit in conflict:
        lit_deps = m.get_dependencies(lit)
        if lit_deps is None:
            deps.add(lit)
        else:
            deps |= lit_deps
    return frozenset(deps)


def find_conflict(
    m: Model,
    watch_list: TwoWatchList,
    clauses: Cnf
):
    """
    Efficiently identify a clause whose literals are all false by testing only
    two literals in it.
    """
    for clause in clauses:
        l1, l2 = watch_list.get_lits(clause)
        ml1, ml2 = m(l1), m(l2)
        if ml1 is False and ml2 is False:
            if any(m(lit) is not False for lit in clause):
                lit = next(lit for lit in clause if m(lit) is not False)
                watch_list.change_watched(clause, l1, lit)
                continue
            return clause
    return None


def find_undecided_literal(
    literals: list[Lit],
    m: Model,
    watch_list: TwoWatchList,
    heuristic: str = "NONE"
) -> Lit | None:
    """
    Chooses a unassigned literal under partial model m according to some
    heuristic. If all literals are assigned, return None.
    """

    def DLIS() -> Lit | None:
        """
        Implements Dynamic Largest Individual Sum variant for 2WL.
        We just take one of the literals with the most watched clauses.
        """
        best = []
        best_length = float('-inf')
        for lit in m.unassigned_lits:
            num_clauses = len(watch_list.get_clauses(lit))
            if num_clauses > best_length:
                best_length = num_clauses
                best = [lit]
            elif num_clauses == best_length:
                best.append(lit)
        if not best:
            return None
        return random.choice(best)

    def jeroslow_wang() -> Lit | None:
        """
        Implements Jeroslow-Wang heuristic variant for 2WL. We exponentially
        favors literals in shorter clauses.
        """
        best = []
        best_length = float('-inf')
        for lit in m.unassigned_lits:
            weight = 0
            for clause in watch_list.get_clauses(lit):
                clause_size = len(clause)
                weight += 2**(-clause_size)
            if weight > best_length:
                best_length = weight
                best = [lit]
            elif weight == best_length:
                best.append(lit)
        if not best:
            return None
        return random.choice(best)

    match heuristic:
        case "DLIS":
            return DLIS()
        case "JW":
            return jeroslow_wang()
        case "NONE":
            return (None if not m.unassigned_lits
                    else random.choice(list(m.unassigned_lits)))
        case _:
            raise ValueError("Invalid Heuristic")


def propagate_units(
    m: Model,
    units: Iterable[Lit],
    watch_list: TwoWatchList
) -> None:
    """
    Set every literal u in units to true and propagate. No literal can be false
    """
    conflicts = set()
    for u in units:
        if m(u) is True:
            continue
        if m(u) is False:
            conflicts.add({u})
            continue
        if VERBOSE:
            print(f"Found {u} (unit)")
        m.propagate(u, frozenset())
        conflicts |= unit_propagation(m, watch_list, neg(u))
    return conflicts


def get_model(f: Cnf, fuel: int = DEFAULT_RECURSION_FUEL) -> Model | None:
    """
    Returns a model satisfying f is f is SAT and None otherwise.
    fuel gives a threshold on the maximum number of iterations of CDCL.
    """
    literals = [lit for clause in f for lit in clause]
    m = Model(literals)

    watch_list = TwoWatchList(literals)
    units = []
    for clause in f:
        try:
            watch_list.watch_clause(clause)
        except ValueError:  # There is only one literal in clause
            u, *_ = clause
            units.append(u)

    conflicts = propagate_units(m, units, watch_list)
    if conflicts:
        return None

    for _ in range(fuel):
        # Backtracking
        while conflict := find_conflict(m, watch_list, conflicts):
            learned_clause = analyze_conflict(conflict, m)
            if not learned_clause:
                return None
            f.add(learned_clause)  # Add the clause to f
            lit = random.choice(list(learned_clause))
            m.backtrack([lit])

            try:  # Take care of watching the new clause.
                watch_list.watch_learned_clause(learned_clause, m)
                m.propagate(lit, learned_clause-{lit})
                unit_propagation(m, watch_list, neg(lit), conflicts)

            except ValueError:
                u, *_ = learned_clause
                conflicts |= propagate_units(m, [u], watch_list)

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
        conflicts = unit_propagation(m, watch_list, neg(lit))
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
