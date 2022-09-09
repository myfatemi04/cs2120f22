from z3 import *

T, S, C = Ints('T S C')

solver = Solver()
solver.add(T + S + C == 10)
solver.add(C + S - T == 6)
solver.add(C + T - S == 4)

if solver.check() == sat:
    print(solver.model())
