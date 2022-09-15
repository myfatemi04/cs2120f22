theorem

-- name of proof
and_commutes:

-- what we want to prove
∀ (P Q : Prop), P ∧ Q → Q ∧ P

-- what we want to prove
:=
begin
	intros P Q,

	-- Lean knows that I'm talking about P ∧ Q
	-- Assume will just assume that you have ea proof of the premise.
	-- P ∧ Q is the premise here.
	assume h,

	let p := and.elim_left h,
	let q := and.elim_right h,

	apply and.intro q p
end
