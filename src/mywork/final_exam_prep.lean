/-
Practice with machines
-/

import tactic.ring

-- the number → result at 0 → (number n, result at n → result at n + 1)
#check @nat.rec_on

def exponent(base: ℕ) (power: ℕ): ℕ :=
	nat.rec_on power
		1
		(λ n r, base * r)
#eval exponent 5 4 -- 625

def x: ℕ := nat.rec_on 8 1 (λ n r, 2 * r)
#eval x -- 256

-- Inductive proofs

def consecutive_sum(n: ℕ): ℕ :=
	nat.rec_on n
		0
		(λ n r, r + n.succ)
		
def consecutive_sum': ℕ → ℕ
| 0 := 0
| (nat.succ n) := n.succ + (consecutive_sum' n)

#eval consecutive_sum' 10

variables n: ℕ

/-
This property seems difficult to prove in the beginning. However,
it's completely possible! It's a LOT easier, though, if we break
it up into subproblems.
-/
def our_property(n: ℕ) := 2 * consecutive_sum' n = n * (n.succ)

-- Proof that it works for 0
lemma sum_zero: our_property 0 := refl 0
lemma sum_next(n: ℕ) (h: our_property n): our_property (n.succ) :=
begin
unfold our_property,
-- We can apply unfold consecutive_sum'
unfold consecutive_sum',
ring,
unfold our_property at h,
rw h,
ring,
end

lemma sum_all: ∀ n: ℕ, our_property n :=
begin
assume n,
induction n with n ih,
exact sum_zero,
exact sum_next n ih,
end
