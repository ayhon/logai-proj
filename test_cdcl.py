from pathlib import Path
from multiprocessing import Process

from typing import Iterable

from cdcl.cdcl import get_model, read_dimacs

TIMEOUT = 30.


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


def run_test(p: Path, success: bool) -> bool | None:
    try:
        model = get_model(read_dimacs(p))
    except TimeoutError:
        return None

    if success:
        return model is not None
    return model is None


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
