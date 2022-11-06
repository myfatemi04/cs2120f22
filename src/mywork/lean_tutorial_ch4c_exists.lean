import data.nat.basic

-- # Existential quantifier

/-
∃ x: α, p x
There exists an α (named "x") such that the predicate "p" is true for x.
There are also introduction and elimination rules for this.

For introductions: It suffices to provide any example.
-/

example: ∃ x: ℕ, x > 0 :=
begin
have h: 1 > 0,
from nat.zero_lt_succ 0,
-- exists.intro requires the term and the proof of its predicate
apply exists.intro 1 h,
end

example (x: ℕ) (h: x > 0): ∃ y, y < x :=
begin
apply exists.intro 0 h,
end

example (x y z: ℕ) (hxy: x < y) (hyz: y < z):
	∃ w, (x < w) ∧ (w < z) :=
exists.intro y (and.intro hxy hyz)

#check @exists.intro

-- Shorthand for exists.intro t h is ⟨t, h⟩
example: ∃ x: ℕ, x > 0 :=
⟨1, nat.zero_lt_succ 0⟩

example (x: ℕ) (h: x > 0): ∃ y, y < x :=
⟨0, h⟩

-- If there are more required hypotheses, we put them after
example (x y z: ℕ) (hxy: x < y) (hyz: y < z):
	∃ w, (x < w) ∧ (w < z) :=
⟨y, hxy, hyz⟩

-- Note: exists.intro has implicit arguments.
-- Lean must infer the predicate p

variables (α: Type*) (p q: α → Prop)

-- The existential elimination rule allows us to proof q
-- from ∃ x: α, p x by showing that q follows from p x in
-- every situation.
example (h: ∃ x, p x ∧ q x): ∃ x, q x ∧ p x :=
begin
apply exists.elim h _,
assume w,
assume hw,
apply exists.intro w (and.intro hw.right hw.left),
end

-- The existential elimination rule is like the or-elimination
-- rule. The assertion ∃ x: α, p x can be thought of as a big
-- disjunction of the propositions p a across any a ∈ α.

-- There's a more convenient way to eliminate from an existential
-- quantifier, and this is with the `match` statement. What this
-- does is give us w and hw from the assumption (`h`), which we
-- can then use to construct our desired proof.
example (h: ∃ x, p x ∧ q x): ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ := ⟨w, hw.right, hw.left⟩
end

-- Here, match can even be used to deconstruct the conjunction
example (h: ∃ x, p x ∧ q x): ∃ x, q x ∧ p x :=
match h with ⟨w, hpw, hqw⟩ := ⟨w, hqw, hpw⟩
end

-- Let is used to deconstruct the assumed hypothesis
example (h: ∃ x, p x ∧ q x): ∃ x, q x ∧ p x :=
let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

-- Assume is used to deconstruct the context
example: (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

-- Proving even numbers add up to even numbers
def is_even(a: ℕ) := ∃ b, a = 2 * b

theorem even_plus_even {a b: ℕ}
	(h1: is_even a) (h2: is_even b): is_even (a + b) :=
begin
apply exists.elim h1 _,
assume w1,
assume hw1: a = 2 * w1,
apply exists.elim h2 _,
assume w2,
assume hw2: b = 2 * w2,
apply exists.intro (w1 + w2) _,
exact (calc
	a + b = 2 * w1 + 2 * w2: by rw [hw1, hw2]
	... = 2 * (w1 + w2): by rw mul_add)
end

theorem even_plus_even' {a b: ℕ}
	(h1: is_even a) (h2: is_even b): is_even (a + b) :=
match h1, h2 with
	⟨w1, (hw1: a = 2 * w1)⟩,
	⟨w2, (hw2: b = 2 * w2)⟩ :=
	-- Shorthand for ∃
	⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
end
