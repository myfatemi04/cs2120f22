import data.int.basic

variables a b c d: ℤ

example: a + 0 = a := add_zero a
example: 0 + a = a := zero_add a
example: a * 1 = a := mul_one a
example: 1 * a = a := one_mul a
example: -a + a = 0 := neg_add_self a
example: a + -a = 0 := add_neg_self a
example: a - a = 0 := sub_self a
example: a + b = b + a := add_comm a b
example: a + b + c = a + (b + c) := add_assoc a b c
example: a * b = b * a := mul_comm a b
example: a * b * c = a * (b * c) := mul_assoc a b c
example: a * (b + c) = a * b + a * c := mul_add a b c
example: a * (b + c) = a * b + a * c := left_distrib a b c

-- # Calculational Proofs

variable e: ℤ

variable h1: a = b
variable h2: b = c + 1
variable h3: c = d
variable h4: e = 1 + d

theorem T: a = e :=
calc
	a = b: h1
	... = c + 1: h2
	... = d + 1: congr_arg _ h3
	... = 1 + d: add_comm d 1
	... = e: eq.symm h4

-- To use the "rw" keyword, you need to "include" the required hypotheses
include h1 h2 h3 h4

theorem T': a = e :=
calc
	a = b: by rw h1
	... = c + 1: by rw h2
	... = d + 1: by rw h3
	... = 1 + d: by rw add_comm
	... = e: by rw h4

theorem T'': a = e :=
calc
	a = d + 1: by rw [h1, h2, h3]
	... = 1 + d: by rw add_comm
	... = e: by rw h4

theorem T''': a = e := by rw [h1, h2, h3, add_comm, h4]

-- We can also use the "simp" tactic, which rewrites the goal
-- by applying the given identities repeatedly, in any order,
-- anywhere they are applicable in a term
theorem T'''': a = e := by simp [h1, h2, h3, h4, add_comm]

-- "calc" can also be used for <, ≤, >, ≥

example (x y: ℕ):
	(x + y) * (x + y) = x * x + y * x + x * y + y * y :=
calc
	(x + y) * (x + y) = (x + y) * x + (x + y) * y: by rw mul_add
	... = x * x + y * x + (x + y) * y: by rw add_mul
	... = x * x + y * x + (x * y + y * y): by rw add_mul
	... = x * x + y * x + x * y + y * y: by rw ←add_assoc
-- The ← says to apply in the opposite order

-- Even faster:
example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by rw [mul_add, add_mul, add_mul, ←add_assoc]

example (x y : ℕ) :
  (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
by simp [mul_add, add_mul, add_assoc, add_left_comm]


