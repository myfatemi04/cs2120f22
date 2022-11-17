/-
Functions in Lean

Looking back at relations.
A relation, r, from α to β, is just a subset of α ⨯ β.
A relation *could* be as simple as r = {(1, a)}, or as expansive as the entire set.

One example is the set of friend relations on Facebook, or the set of people who like
a particular post.

Because the relation is a set, it can be written as α → β → Prop.

Now, functions.
A function is a single-valued relation. A value of α cannot have any more than one
value of β. In essence, ∀ (a: α) (b c: β), r a b → r a c → b = c.
These are many-to-one relations.
You can turn a one-to-many relation into a function by turning it into a one-to-one set relation.
α → (β → Prop) is the same as α → Set(β).
-/

import logic.relation

namespace cs2120

section functions

universes u v

variables
	{α: Sort u}
	{β: Sort v}
	(r: α → β → Prop)

def single_valued := ∀ (a: α) (b c: β), r a b → r a c → b = c

/-
Suppose that r is single-valued.

Person         SSN
	α --> (f) --> β

One person cannot have more than one SSN.
With the pure definition of a function, two people could have the same SSN.
Therefore, a single-valued relation can be a many-to-one function.
Usually, though, we want to add the constraint that the function is one-to-one.

Being one-to-one is a property of functions that we often really care about.
A function that has no two outputs the same is called an *injective* function.

Injective functions must pass the _horizontal_ line test.
-/

def injective := ∀ (a b: α) (c: β), r a c → r b c → a = b

/-
What is a total function? A total function where for every input, there is an output.
-/
def total_function := single_valued r → (∀ a, ∃ b, r a b)

/-
Every function is partial.
However, for it to be *strictly* partial, there
must be some input that has no corresponding output.
-/
def strictly_partial := single_valued r → (∃ a, ¬∃ b, r a b)

/-
For surjective functions,
If I take the entire input domain and map it through the function, I get the entire output domain.
Every element of the output set has some element of the input set that goes to it.
This does *not* require the entire input set to be mapped to the output set.

The function from person to SSN is NOT surjective, if we consider the universal set of SSNs to be ℕ.
-/
def surjective := single_valued r → (∀ b, ∃ a, r a b)

/-
Bijective functions are both injective and surjective.
There are no two colliding output values, and the entire output
space is mapped to an element of the input space.

Essentially, every element in the output space is a single corresponding
value in the input space. The output space has a shadow in the input space.

I'm guessing that the input space also needs to be fully covered? The function
must be total?

To have a bijection, the sets have to be the same size.
You could also say that the sets are isomorphic.

The inverse of a bijective function is also a function.
-/
def bijective := surjective r ∧ injective r

/-
The inverse of a relation is just the set of pairs where every pair is flopped.
-/
def inverse (r: α → β → Prop) := λ (b: β) (a: α), r a b

/-
Let's say we have this function:
	a1 → b2
	a2 → b1
	a3 → b1
The inverse of this relation is:
	b2 → a1
	b1 → a2
	b1 → a3
The inverse is not single-valued.
-/

/-
Some examples
-/
def square(x: ℕ) := x * x


-- Let's define a relation between people and natural numbers.
inductive Person: Type
| p1
| p2
| p3

-- So we don't have to type Person.{p1 p2 p3}
open Person

-- In Lean, every function must be defined to be total. If we remove
-- one of these cases, then we get an error telling us that we have
-- not defined a value. A *computable* function must be total.
def id_number: Person → ℕ
| p1 := 1
| p2 := 2
| p3 := 3

-- Let's define this in proof format.
-- id_number' is a subtype of Person → ℕ → Prop.
-- Possible values are the propositions that have valid proofs.
inductive id_number': Person → ℕ → Prop
| pf1: id_number' p1 1
| pf2: id_number' p2 2
| pf3: id_number' p3 3

-- These two types are the same.
#check Person → ℕ
#check ∀ (p: Person), ℕ

end functions

end cs2120
