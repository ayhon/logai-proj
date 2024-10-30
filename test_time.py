import cProfile
from pathlib import Path

from cdcl.cdcl import read_dimacs, get_model

instances = ["tests/OK/MISC/ok_50_80.cnf", "tests/KO/PHOLE/hole6.cnf"]
for instance in instances:
    f = read_dimacs(Path(instance))
    print(f"Instance: {instance} (strat {strat})")
    cProfile.run("get_model(f)", sort="cumtime")
