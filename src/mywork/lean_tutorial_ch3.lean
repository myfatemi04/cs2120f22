namespace hidden

/-

# Propositions as types

We can use this typing language to create an extensive proof framework!

-/

constant and: Prop → Prop → Prop
constant or: Prop → Prop → Prop
constant not: Prop → Prop
constant implies: Prop → Prop → Prop

variables p q r: Prop
#check and p q
#check or (and p q) r
#check implies (and p q) (and q p)

-- We can now introduce, for each element `p: Prop`, another type `Proof p`, for the type
-- of proofs of `p`.

constant Proof: Prop → Type
-- Given some propositions, we can construct a proof ...
constant and_comm: Π p q: Prop, Proof (implies (and p q) (and q p))

-- If we have a proof of p → q, then given a proof of p, we can construct a proof of q
constant modus_ponens: Π p q: Prop, Proof (implies p q) → Proof p → Proof q 

-- Proofs in Lean are equal regardless of the information that was used to create them.
-- No fact is relevant besides the fact that the proof has enough information to be proven.

end hidden

namespace hidden2

/-

## Working with propositions as types

-/

constants p q: Prop
theorem t0: p → q → p := λ hp: p, λ hq: q, hp

theorem t0': p → q → p :=
assume hp: p,
assume hq: q,
hp

theorem t0'': p → q → p :=
assume hp,
assume hq,
show p, from hp

-- You can also use the term `lemma` instead of `theorem`.

theorem t1 (hp: p) (hq: q): p := hp
theorem t1' (p q: Prop) (hp: p) (hq: q): p := hp
#check t1

-- Let's say we have a proof of p
axiom hp: p
theorem t2: q → p := t1 hp

#check assume (hp: p) (hq: q), and.intro hp hq

-- Disjunction
example (hp: p): p ∨ q := or.intro_left q hp
example (hq: q): p ∨ q := or.intro_right p hq
example (h: p ∨ q): q ∨ p :=
-- Goes through the cases
or.elim h (assume hp: p, show q ∨ p, from or.intro_right q hp)
					(assume hq: q, show q ∨ p, from or.intro_left p hq)

-- Conjunction
example (h: p ∧ q): q ∧ p := ⟨h.right, h.left⟩

variable l: list ℕ

#check list.head l
#check l.head

-- Negation and falsity
example (hpq: p → q) (hnq: ¬q): ¬p :=
assume hp: p, -- ¬p ↔ p → false
show false, from hnq (hpq hp)

end hidden2
