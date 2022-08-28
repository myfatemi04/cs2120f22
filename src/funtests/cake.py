from z3 import *

d, a, t, v_i, v_f = Reals('d a t v__i v__f')

equations = [
   d == v_i * t + (a*t**2)/2,
   v_f == v_i + a*t,
]
print("Kinematic equations:")
print(equations)

# Given v_i, v_f and a, find d
problem = [
    v_i == 30,
    v_f == 0,
    a   == -8
]
print("Problem:")
print(problem)

print("Solution:")
solve(equations + problem)

solver = Solver()
solver.add(*equations)
solver.add(*problem)
print("Check:", solver.check()) # must be done before calling model
print("Model:", solver.model())
