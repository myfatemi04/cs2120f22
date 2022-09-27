theorem

-- name of proof
and_commutes:

-- what we want to prove
∀ (P Q : Prop), P ∧ Q → Q ∧ P

-- what we want to prove
:=
begin
	-- or assume P Q
	intros P Q,

	-- Lean knows that I'm talking about P ∧ Q
	-- Assume will just assume that you have ea proof of the premise.
	-- P ∧ Q is the premise here.
	assume h,

	let p := and.elim_left h,
	let q := and.elim_right h,

	-- You can also say:
	let pp: P := and.elim_left h,
	let qq: Q := and.elim_right h,

	-- And that can verify that you're proving the right thing

	apply and.intro q p
end

/-

Theorem: Logical and is commutative.

-/
