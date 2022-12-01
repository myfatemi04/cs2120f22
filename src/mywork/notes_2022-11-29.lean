/-
November 29:
Induction

∀ n, sum{i, 0, n}[i] = n * (n + 1) / 2
∀ b, bnot(bnot(b)) = b

inductive bool: Type
| ff: bool
| tt: bool

-/

#check @bool.rec_on

/-
bool.rec_on:
	Π {motive: bool → Sort u_1}
	(n: bool)
	motive ff → motive tt → motive n
-/

example: ∀ (n: bool), bnot (bnot n) = n :=
begin
assume n,
cases n,
exact rfl,
exact rfl,
end


example: ∀ (n: bool), bnot (bnot n) = n :=
begin
assume n,
apply bool.rec_on n,
exact rfl,
exact rfl,
end

-- In induction, we start with a base case and then
-- use the "successor" constructor

def zero := nat.zero
def one := nat.succ zero
def two := nat.succ one
def three := nat.succ two

def inc(n': ℕ): ℕ := nat.succ n'

#eval inc 3
#eval inc three

def dec: ℕ → ℕ
| (nat.succ n') := n'
| 0 := 0

#eval dec 3
#eval dec 0

def x(n: ℕ): ℕ := begin
cases n with succ,
exact 0,
exact succ,
end

#eval x 10

#check nat.add

/-
3 + 0 = 3
n + 0 = n
n + (1 + m) = nat.succ (n + m)
-/

def add: ℕ → ℕ → ℕ
| n 0 := n
| n (nat.succ m) := nat.succ (add n m)

#eval add 2 12

/-
Multiplication!
-/

def mul: ℕ → ℕ → ℕ
| n 0 := 0
| n (nat.succ m) := add n (mul n m)

#eval mul 20 20

/-
Basically, what we're doing here is
creating a recursive way to make all
of these definitions.

This is inherently very cacheable, and
might lead to a really big hardware speedup
for non-trivial functions.
-/

def exp: ℕ → ℕ → ℕ
| n 0 := 1
| n (nat.succ m) := mul n (exp n m)

#eval exp 2 2

/-
What about @nat.rec_on, is it analogous to @bool.rec_on?

This requires that some property be satisfied on all natural numbers.

The way this is done is through inductive proof. First, you must
prove that it works for 0. Then, you must prove that it works for
the successor of any natural number, given that we have a proof for
that natural number.
-/

#check @nat.rec_on

def factorial: ℕ → ℕ
| 0 := 1
| (nat.succ n) := mul (nat.succ n) (factorial n)

#eval factorial 7

def factorial': ℕ → ℕ :=
begin
assume n,
induction n with zero successor,
exact 1,
exact (n + 1) * (factorial n)
end

#eval factorial' 5
