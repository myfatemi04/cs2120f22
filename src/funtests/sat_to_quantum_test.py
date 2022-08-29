import qiskit
from qiskit import Aer
from qiskit.tools.visualization import plot_histogram

from z3 import *

# Create Quantum circuit based on a SAT problem
# Question: How can we create Quantum circuits if we are not guaranteed to measure the right outcome?
# Maybe we can increase the probability of measuring the correct outcome.
# Maybe there's also a way to optimize the circuit once it's made.

a, b, c = Bools('a b c')

# Expression: "(a & !b) | (b & c) | (a & b & c)"
expression = Or(And(a, Not(b)), And(b, c), And(a, b, c))

# These are the only values we need:
# print(expression)
# print(expression.children())
# print(expression.decl().name())

circ = qiskit.QuantumCircuit(10, 4)

# Iterate through the tree. Create a stack.
# AND gates can be simulated through Toffoli gates.
# OR gates can be simulated through a bunch of Toffoli gates and De Morgan.
# Output from each expression is put into one of the auxiliary qubits.

qa, qb, qc = 0, 1, 2

test = None
# test = [1, 0, 1]

if test is not None:
    for (idx, val) in zip([qa, qb, qc], test):
        if val:
            circ.x(idx)
else:
    # initialize first few qubits to uniform superposition
    circ.h(qa)
    circ.h(qb)
    circ.h(qc)

circ.barrier()

# (a & !b): 4
#   !b: 3
# (b & c): 5
# (a & b & c): 7
#   (a & b): 6
# OR-ing them all together: 9
#   OR-ing the first two: 8
circ.cnot(qb, 3)
circ.x(3)
circ.toffoli(qa, 3, 4)
circ.toffoli(qb, qc, 5)
circ.toffoli(qa, qb, 6)
circ.toffoli(6, qc, 7)
circ.barrier()

# OR them all together
circ.x(4)
circ.x(5)
circ.toffoli(4, 5, 8)
circ.x(8)

circ.barrier()

circ.x(8)
circ.x(7)
circ.toffoli(8, 7, 9)
circ.x(9)

# Output is at 9
circ.measure(9, 0)

circ.barrier()

# Measure results
circ.measure(qa, 1)
circ.measure(qb, 2)
circ.measure(qc, 3)

print(circ)

simulator = Aer.get_backend('aer_simulator')
circ = qiskit.transpile(circ, simulator)

# Run and get counts
result = simulator.run(circ).result()
counts = result.get_counts(circ)
plot_histogram(counts, title='Bell-State counts')

print("Solutions from Quantum Simulator")
# make sure bits are in the order we intend
counts = {key[::-1]: counts[key] for key in counts.keys()}
for i, count in sorted(counts.items()):
    print(i[0], i[1:], count)
        
print("Solutions from Z3")
solver = Solver()
solver.add(expression)

while solver.check() == z3.sat:  
    solution = "False"
    m = solver.model()
    for i in m:
        solution = f"Or(({i} != {m[i]}), {solution})"
    f2 = eval(solution)
    solver.add(f2)
    print(m)
    
# Top: 100, 110, 010, 000

import matplotlib.pyplot as plt
plt.show()
