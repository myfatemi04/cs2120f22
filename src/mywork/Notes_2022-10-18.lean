def dm1: Prop := ∀ (A B: Prop), ¬(A ∧ B) ↔ ¬A ∨ ¬B

example: dm1 :=
begin
assume A B,
apply iff.intro,

-- Proving the forward direction
assume h: ¬(A ∧ B),
cases classical.em A with a na,
-- Case for A being true
cases classical.em B with b nb,
-- Case for B being true
let nh := h (and.intro a b), contradiction,
-- Case for B being false
right, assumption,
-- Case for A being false
left, assumption,

-- Proving the backward direction
assume h: ¬A ∨ ¬B,
cases h,
-- ¬A is true
-- Our goal is to show that A ∧ B is false. Therefore,
-- create a contradiction when A ∧ B is true.
assume h1: A ∧ B,
cases h1, contradiction,

assume h1: A ∧ B,
cases h1, contradiction,
end

example: ∀ (P Q: Prop), ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
begin
assume P Q,
apply iff.intro,
-- Forward direction
assume h1,
apply and.intro,
assume p,
have nh1 := or.intro_left Q p, contradiction,
assume q,
have nh1 := or.intro_right P q, contradiction,

assume h1,
assume p_or_q,
cases p_or_q,
apply and.elim_left h1, assumption,
apply and.elim_right h1, assumption,
end
