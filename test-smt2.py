from z3 import *

test_file = "maze1-bmc.smt2"

ss = Solver()

ss.from_file(test_file)

breakpoint()
