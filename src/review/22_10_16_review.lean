example: ∀ (P Q R: Prop), P ∨ Q → ((P → R) → (Q → R) → R) :=
begin
assume P Q R,
assume (h: P ∨ Q), -- Allows you to document your reasoning more thoroughly.
apply or.elim h,

-- First case: assume P
assume (p: P), -- Arrow introduction
assume (pr: P → R),
assume (qr: Q → R),
exact (pr p),

-- Second case: assume Q
assume (q: Q),
assume (pr: P → R),
assume (qr: Q → R),

exact (qr q),
end

#check or.inl
#check or.inr

-- What does the unfold command do?

def x := 5

theorem foo: x + 1 = 6 :=
begin
unfold x, -- Unfolds the definition of x (replaces x with 5)
end

-- Axiom of the excluded middle
def m := ∀ P, P ∨ ¬P

theorem bar: m :=
begin
unfold m, -- Just replaces a name with its meaning
assume P,
apply classical.em
end

-- How do I work with iff?
-- Iff is called a bi-implication
-- You can prove this through iff.intro

example: ∀ (P Q: Prop), P ↔ Q :=
begin
assume P Q,
let pq: P → Q := sorry,
let qp: Q → P := sorry,
apply iff.intro pq qp,
end

-- English language proof of a bi-implication
-- It would suffice to have a proof of P → Q and a proof of Q → P
-- Let's take the forward direction first (...), then let's
-- go in the other direction (...)

variables (P Q: Prop)
variables (pq: P → Q) (qp: Q → P)
example: P ↔ Q := iff.intro pq qp

-- There are slightly weird things about the names of elimination rules.

variable piffq: P ↔ Q

example: P → Q := iff.mp piffq
example: Q → P := iff.mpr piffq

theorem my_and_elim: ∀ (P Q), P ∧ Q → P :=
begin
-- We want to prove a for-all here. We do this by assuming the
-- premises are given, and then showing that what follows is a
-- proof of the conclusion.
assume P Q,

-- Assume that the premise is true. (If we want to prove an implication,
-- it suffices to assume the context and prove the conclusion.)
assume pq: P ∧ Q,

-- Cases for "and" are called "and.elim_left" and "and.elim_right"
cases pq,
exact pq_left,
end

variables (Smoke Fire Light Good: Prop)
variables (sf: Smoke → Fire) (fl: Fire → Light) (lg: Light → Good)
variable (s: Smoke)

example: ∀ (S F L G: Prop), (S → F) → (F → L) → (L → G) → S → G :=
begin
assume S F L G,
assume sf fl lg,

-- This is taken from what we're trying to prove (the S → G)
assume s,
exact lg (fl (sf s))
end

-- Some review for negation elimination
-- It's really helpful to remember the truth table for NOT.

example: ∀ P, ¬(P ∧ ¬P) :=
begin
assume P,

-- This is the "mistake" that we're trying to prove doesn't happen.
-- Because of this, we will be able to construct a proof of false.
assume (h: P ∧ ¬P),

cases h with p not_p,
-- Remember: ¬P is the same as P → false
apply not_p p,
end
