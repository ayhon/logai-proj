from pathlib import Path
from multiprocessing import Process

from typing import Iterable

from cdcl.cdcl import get_model, read_dimacs

TIMEOUT = 60.


def ok_pahts() -> Iterable[Path]:
    tests = Path(".") / "tests/"
    ok_tests = tests / "OK"
    yield from ok_tests.rglob("*.cnf")


def ko_pahts() -> Iterable[Path]:
    tests = Path(".") / "tests/"
    ko_tests = tests / "KO"
    yield from ko_tests.rglob("*.cnf")


def paths_by_size() -> Iterable[tuple[Path, bool]]:
    ok_paths = [*ok_pahts()]
    ko_paths = [*ko_pahts()]
    yield from sorted(
        (
            (p, sat)
            for paths in (
                zip([*ok_paths], [True] * len(ok_paths)),
                zip([*ko_paths], [False] * len(ko_paths)),
            )
            for p, sat in paths
        ),
        key=lambda p: p[0].stat().st_size,
    )


def run_test(p: Path, satisfiable: bool) -> bool | None:
    """
    Tests whether CDCL works correctly on the instance located at path p.

    Return None if CDCL times out, True if it founds a model of f (or founds
    that f is unsat), False if the result is incorrect.
    """
    f = read_dimacs(p)
    try:
        model = get_model(f)
    except TimeoutError:
        return None

    if not satisfiable:
        return model is None
    if model is None:
        return False
    return model.entails(f)


def main():
    def build_target(path, sat):
        def target() -> None:
            res = run_test(path, sat)
            if res is None:
                print(f"⏰Timed out. {TIMEOUT=}s")
            elif res is True:
                print("✅")
            elif res is False:
                print("❌")
        return target

    for path, sat in paths_by_size():
        print(path)
        f = Process(target=build_target(path, sat))
        f.start()
        f.join(timeout=TIMEOUT)
        if f.exitcode is None:
            print(f"⏰Timed out. {TIMEOUT=}s")


if __name__ == "__main__":
    main()
