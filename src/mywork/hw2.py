from z3 import *

x, y, z = Bools('x y z')

C1 = Implies(And(Or(x, y), x), Not(y))
# Affirming the disjunct: If X or Y is true, and X is true, then Y is not true.
# This rule is invalid because it assumes that X and Y cannot both be true at the same time.
# If the OR were replaced with an exclusive OR (XOR), then it would be valid.
# Counterexample: X = true, Y = true
# For example: I know how to make eggs or I know how to make toast.
# I know how to make eggs; but that doesn't mean I don't know how to make toast too.

C2 = Implies(And(x, y), And(x, y))
# And introduction: Given that X is true and Y is true, then (X and Y) is true
# Seems valid.

C3 = Implies(And(x, y), x)
# And elimination left: Given that X is true and Y is true, then X is true
# Seems valid.

C4 = Implies(And(x, y), y)
# And elimination right: Given that X is true and Y is true, then Y is true
# Seems valid.

C5 = Implies(Not(Not(x)), x)
# Negation elimination: If Not (Not X) is true, then X is true.
# Seems valid.

C6 = Not(And(x, Not(x)))
# No contradiction: X and not X cannot both be true.
# Seems valid.

C6_ = Implies(x, Or(x, y))
# Or introduction left: If X is true, the X or Y is true.
# Seems valid.

C7 = Implies(y, Or(x, y))
# Or introduction right: If Y is true, the X or Y is true.
# Seems valid.

C8 = Implies(And(Implies(x, y), Not(x)), Not(y))
# Denying the antecedent: If X implies Y, then Y can only be true if X is true.
# This rule is invalid because X implying Y does not mean that Y necessarily implies X.
# Counterexample: X = false, Y = true
# For example: Rainy weather means that the ground is wet.
# It isn't raining outside, but the ground can still be wet.

C9 = Implies(And(Implies(x, y), Implies(y, x)), x == y)
# Iff: If X implies Y, and Y implies X, then X is true IFF Y is true.
# This also means that the statements are logically equivalent.
# Seems valid.

C10 = Implies(x == y, Implies(x, y))
# Iff elimination left: If X is true if and only if Y is true,
# then X being true implies that Y is true.
# Seems valid.

C11 = Implies(x == y, Implies(y, x))
# Iff elimination right: If X is true if and only if Y is true,
# then Y being true implies that X is true.
# Seems valid.

C12 = Implies(And(Or(x, y), Implies(x, z), Implies(y, z)), z)
# Or elimination: If X or Y is true, and both X and Y can separately imply Z, then Z is true.
# Seems valid.

C13 = Implies(And(Implies(x, y), y), x)
# Affirming the conclusion: If X implies Y, and Y is true, then X is true.
# This rule is invalid because Y being true does not guarantee that X is true.
# Y may be true regardless of the value of X.
# Counterexample: X = false, Y = true
# For example: If 10 people come over, I will not have enough snacks.
# I don't have enough snacks, but that doesn't mean that 10 people came over.

C14 = Implies(And(Implies(x, y), x), y)
# Arrow elimination: If X implies Y, and X is true, then Y is true.
# Seems valid.

C15 = Implies(And(Implies(x, y), Implies(y, z)), Implies(x, z))
# Transitivity of "implies": If X implies Y, and Y implies Z, then X implies Z.
# Seems valid.

C16 = Implies(Implies(x, y), Implies(y, x))
# Converse: If X implies Y, then Y implies X.
# This ruel is invalid because causality is not necessarily bidirectional.
# Counterexample: X = false, Y = true
# For example: If a tree falls on my house, then I will not be able
# to hang out with my friends that night. However, if I am not able
# to hang out with my friends one night, that does not mean that a
# tree will fall on my house as a result.

C17 = Implies(Implies(x, y), Implies(Not(y), Not(x)))
# Contrapositive: If X implies Y, then Y not being true implies that X cannot be true.
# Seems valid.

C18 = Not(Or(x, y)) == And(Not(x), Not(y))
# DeMorgan #1 (Distribution of OR): If neither X or Y is true, then both not X and not Y are true.
# Seems valid.

C19 = Not(And(x, y)) == Or(Not(x), Not(y))
# DeMorgan #2 (Distribution of AND): If X and Y are not both true, then either X is false or Y is false.
# Seems valid.

rules = [
    C1, C2, C3, C4, C5,
    C6, C6_, C7, C8, C9,
    C10, C11, C12, C13, C14,
    C15, C16, C17, C18, C19
]

# Rule C1 (affirming the disjunct) is invalid because it
# assumes that either X or Y is true, but not both. In a
# logical OR, it is okay for more than one of them to be
# true.

# Rule C8 (denying the antecedent) is invalid because it
# assumes that X must equal Y for X to imply Y. Y can be
# true even if X is false.

# Rule C13 (affirming the conclusion) is invalid because
# it assumes that if the conclusion is true, the context
# must be true.

# Rule C16 (converse) is invalid it assumes that if X
# implies Y, then Y implies X.

solver = Solver()

def is_valid(rule):
    solver.reset()
    solver.add(Not(rule))
    return solver.check() == unsat

name = lambda x: f"C{x}" if x <= 6 else ("C6_" if x == 7 else f"C{x - 1}")

for i, rule in zip(range(1, len(rules) + 1), rules):
    if is_valid(rule):
        print(name(i), "is valid")
    else:
        print(name(i), "is invalid:", solver.model())
