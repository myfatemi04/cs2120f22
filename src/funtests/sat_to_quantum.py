import qiskit
from qiskit import Aer
from qiskit.tools.visualization import plot_histogram
from qiskit.circuit.library import AND, OR

from z3 import *

import numpy as np

def generate_circuit_for_arbitrary_bitstring():
    bitstring = [0,1,0,0,1,1,1,1,0]
    circ = qiskit.QuantumCircuit(2*len(bitstring)-sum(bitstring)+1, len(bitstring)+1)
    cnot_counter = len(bitstring)
    and_ins = []
    for i in range(len(bitstring)):
        circ.h(i)
        if 1-bitstring[i]:
            circ.cnot(i,cnot_counter)
            and_ins.append(cnot_counter)
            cnot_counter+=1
        else:
            and_ins.append(i)

    AndGate = qiskit.circuit.library.AND(len(bitstring))
    circ.append(AndGate,[*and_ins, 2*len(bitstring)-sum(bitstring)])

    circ.measure(2*len(bitstring)-sum(bitstring),0)
    for i in range(len(bitstring)):
        circ.measure(i,i+1)

# From QISKIT
# Link: https://qiskit.org/textbook/ch-algorithms/grover.html#5.2-Uncomputing,-and-Completing-the-Oracle
def diffuser(nqubits):
    qc = qiskit.QuantumCircuit(nqubits)
    # Apply transformation |s> -> |00..0> (H-gates)
    for qubit in range(nqubits):
        qc.h(qubit)
    # Apply transformation |00..0> -> |11..1> (X-gates)
    for qubit in range(nqubits):
        qc.x(qubit)
    # Do multi-controlled-Z gate
    qc.h(nqubits-1)
    qc.mct(list(range(nqubits-1)), nqubits-1)  # multi-controlled-toffoli
    qc.h(nqubits-1)
    # Apply transformation |11..1> -> |00..0>
    for qubit in range(nqubits):
        qc.x(qubit)
    # Apply transformation |00..0> -> |s>
    for qubit in range(nqubits):
        qc.h(qubit)
    # We will return the diffuser as a gate
    U_s = qc.to_gate()
    U_s.name = "U$_s$"
    return U_s

# Create Quantum circuit based on a SAT problem
# Question: How can we create Quantum circuits if we are not guaranteed to measure the right outcome?
# Maybe we can increase the probability of measuring the correct outcome.
# Maybe there's also a way to optimize the circuit once it's made.

a, b, c = Bools('a b c')

# Expression: "(a & !b) | (b & c) | (a & b & c)"
expression = Or(And(a, Not(b)), And(b, c), And(a, b, c))
# expression = Or(And(b, c), And(a, b, c))

# These are the only values we need:
# print(expression)
# print(expression.children())
# print(expression.decl().name())

# OK. Traverse the tree. For each node, we have another storage qubit.
# Maybe there can be a cache to prevent repetition.

def build_circuit(expression, expression_to_qubit: dict):
    # Returns the order of functions to call and the arguments to use.
    # In order to calculate any node, we need to know the values of all its children.
    if expression.decl().name() not in ['or', 'and', 'not']:
        return [], expression_to_qubit[expression.decl().name()]
    
    spec = []
    child_qubits = []
    for child in expression.children():
        child_spec, child_out_qubit = build_circuit(child, expression_to_qubit)
        spec.extend(child_spec)
        child_qubits.append(child_out_qubit)
    
    out_qubit = len(expression_to_qubit)
    
    if expression.decl().name() == 'or':
        spec.append(('append', OR(len(child_qubits)), [*child_qubits, out_qubit]))
    elif expression.decl().name() == 'and':
        spec.append(('append', AND(len(child_qubits)), [*child_qubits, out_qubit]))
    elif expression.decl().name() == 'not':
        assert len(child_qubits) == 1
        spec.append(('cnot', child_qubits[0], out_qubit))
        spec.append(('x', out_qubit))
    
    expression_to_qubit[str(expression)] = out_qubit
    
    return spec, out_qubit

vars = ['a', 'b', 'c']

spec, out_qubit = build_circuit(expression, {vars[i]: i for i in range(len(vars))})
oracle = qiskit.QuantumCircuit(out_qubit + 1)
for cmd, *args in [*spec, *spec[:-1]]:
    # Includes uncomputation
    getattr(oracle, cmd)(*args)

# COOL! https://qiskit.org/textbook/ch-algorithms/grover.html#5.-Solving-Sudoku-using-Grover's-Algorithm-
circ = qiskit.QuantumCircuit(out_qubit + 1, 3)

# Initialize 'out0' in state |->
circ.initialize([1, -1]/np.sqrt(2), out_qubit)

# Initialize qubits
for i in range(len(vars)):
    circ.h(i)

circ.barrier()

print(oracle)

# Run oracle
circ.append(oracle, [*range(out_qubit + 1)])
# circ.append(diffuser(3), [0,1,2])

# circ.append(oracle, [*range(out_qubit + 1)])
# circ.append(diffuser(3), [0,1,2])

# for i in range(len(vars)):
#     circ.measure(i, i)

print(circ)

# Iterate through the tree. Create a stack.
# AND gates can be simulated through Toffoli gates.
# OR gates can be simulated through a bunch of Toffoli gates and De Morgan.
# Output from each expression is put into one of the auxiliary qubits.

simulator = Aer.get_backend('statevector_simulator')
circ = qiskit.transpile(circ, simulator)

# Run and get counts
result = simulator.run(circ, shots=1).result()
sv = result.get_statevector()
sva = np.array(sv).reshape(sv.dims())
print(sv.to_dict())
# print(sva.shape)
exit()
counts = result.get_counts(circ)
plot_histogram(counts, title='Bell-State counts')

print("Solutions from Quantum Simulator")
# make sure bits are in the order we intend
counts = {key[::-1]: counts[key] for key in counts.keys()}
for i, count in sorted(counts.items()):
    print(i, count)
        
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
    print({'a': m[a], 'b': m[b], 'c': m[c]})
    
# Top: 100, 110, 010, 000

import matplotlib.pyplot as plt
plt.show()
