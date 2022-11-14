import data.set

universes u v   -- Universe levels, don't worry

/-
Homework #6: Functions, Sets, Relations
-/


/- #1. Basic Functions [35 points]-/


/- A [5 points].

Write a function, isZero, using "by cases" syntax, 
that takes any natural number, n, as an argument and 
returns a Boolean result, true if n = 0 and false if
n > 0 (i.e., n = n' + 1 = (nat.succ n') for some n').
(Don't get distracted by unnecessary details.)
-/

-- Answer
def isZero: ℕ → bool
| 0 := tt
| (nat.succ n') := ff

-- These test cases should pass except the last 
example : isZero 0 = tt := rfl
example : isZero 1 = ff := rfl
example : isZero 2 = ff := rfl
example : isZero 3 = tt := rfl    -- tester tester



/- B [10 points].

Here's a function, fib, using "by cases" syntax, that
takes any natural number, n, as an argument and that
returns the n'th Fibonacci number. The n'th Fibonacci
number is defined by cases: when n is 0, it's 0; when
n is 1 (nat.succ nat.zero), it's 1, otherwise, in the
case where n = n' + 2, it's fib n' + fib n'+1
-/

def fib : ℕ → ℕ 
| 0 := 0
| 1 := 1
| (n' + 2) := fib n' + fib (n' + 1)

-- These test cases should pass except the last 
example : fib 0 = 0 := rfl
example : fib 1 = 1 := rfl 
example : fib 2 = 1 := rfl
example : fib 3 = 2 := rfl
example : fib 4 = 3 := rfl
example : fib 5 = 5 := rfl
example : fib 10 = 55 := rfl
example : fib 2 = 2 := rfl    -- tester tester



/- C [10 points]
Write a function, add, that takes two natural 
numbers and computes their sum. You may *not*
use the addition function that Lean defines in
its libraries. Your addition function should 
be defined by cases. Given arguments n and m,
if m is zero, just return n; otherwise, if m
is (m' + 1), return the sum of n and m' plus
one. (That's still the right answer, right!)
-/

def add : ℕ → ℕ → ℕ 
| n 0 := n
| n (m' + 1) := (n + m') + 1

-- These test cases should pass except the last 
example : add 0 0 = 0 := rfl
example : add 5 0 = 5 := rfl
example : add 0 5 = 5 := rfl
example : add 1 1 = 2 := rfl
example : add 1 2 = 3 := rfl
example : add 2 2 = 4 := rfl
example : add 3 2 = 4 := rfl  -- tester tester


/- D [10 points]

A function is said to be involutive, or an
involution, if applying it twice to *any* value
(of the right type) returns that original value. 
For example, if f is a function, and a is any
argument, then f is involutive if f (f a) = a.
Formally define involutive as a property of
any function, f : α → α. 
-/

def involutive {α : Sort u} (f : α → α) := 
  ∀ a : α, f (f a) = a

/-
Now prove the proposition that the Boolean negation 
function, called bnot in Lean, is an involution. The
trick here is simply to pick the right proof strategy.
Ask, how can I prove it? Hint: It's just a bool!
-/

example : involutive bnot :=
begin
unfold involutive,
assume a,
cases a,
  apply eq.refl,
  apply eq.refl,
end 


/- 2 Sets [35 points] -/


/- A [5 points].

Formally define a predicate, perfectSquare,
satisfied by any natural number that is the 
square of some other natural number. 25 is a
perfect square, for example, because it's the
square of the natural number 5. Fill in both
underscores in the following skeleton to give
your answer. Remember: Predicates take values
to propositions. 
-/

def perfectSquare (n : ℕ) : Prop := ∃ (n': ℕ), n = n' * n'


/- B [5 points].

Define the set of all perfect squares using
set comprehension (set builder) notation and
the perfectSquare predicate.
-/

def perfectSquares : set ℕ := {n: ℕ | perfectSquare n}


/- C [5 point].

State and prove the proposition that 25 is in
the set of perfect squares. Use set membership
notation in writing your proposition.
-/


example : 25 ∈ perfectSquares :=
begin
unfold perfectSquares,
unfold perfectSquare,
apply exists.intro 5 _,
apply rfl,
end


/- D [20 points].
Consider the following sets of natural numbers:

X = { 2, 3, 4}
Y = { 4, 5, 6}
-/

def X : set ℕ := { 2, 3, 4 }
def Y : set ℕ := { 4, 5, 6 }

/-
Formally state and prove the following propositions
using set and set operator notations.

1. 4 is "in" the intersection of X and Y
2. 4 is in the union of X and Y
3. 4 is not in the set difference, X \ Y
4. 10 is in the complement of X
-/

#reduce X

-- 1. intersection
example : 4 ∈ (X ∩ Y) :=
begin
apply and.intro,
show X 4,
unfold X,
right,
right,
apply eq.refl,
show Y 4,
unfold Y,
left,
apply eq.refl,
end

#reduce 4 ∈ (X ∪ Y)

-- 2. union
example : 4 ∈ (X ∪ Y) :=
begin
unfold X Y,
right,
left,
apply rfl,
end


-- 3. difference
/-
Hint: At some point, you might want to 
use the "obviously" true fact that 4 ∈ 
{4, 5, 6} without stopping to prove it. 
Here's a nice trick: 

let n : 4 ∈ {4, 5, 6} := _

This will put the assumption, n, in your
context, but with a "note attached" saying
that you still need a proof of it (that is
you get a new subgoal). Don't worry about 
the crazy-looking goals after you use this 
hint (if you do). Just look at the top-level
goal and proceed accordingly.  
-/

#reduce 4 ∉ (X \ Y)

#reduce set

-- 3. difference
example : 4 ∉ (X \ Y) :=
begin
unfold X Y,
assume h, -- 4 in X AND 4 not in Y
cases h,
-- generates a lot of stuff, but we just want to set up a
-- proof of 4 in {4 5 6} so we can create a contradiction
let n: 4 ∈ {4, 5, 6} := _,
apply h_right n,
left,
apply rfl,
end

example : 4 ∉ (X \ Y) :=
begin
unfold X Y,
simp,
end


-- 4. complement
example : 10 ∈ Xᶜ :=
begin
unfold X,
assume h,
-- cases h,
-- cases h, -- To prove that not(10 = 2)
-- cases h,
-- cases h,
-- cases h,
repeat {cases h},
end 

-- 4. complement
example : 10 ∈ Xᶜ :=
begin
unfold X,
assume h,
cases h, -- Splits into 10 = 2 and 10 ∈ {3, 4}
cases h, -- To prove that not(10 = 2)
cases h, -- Splits 10 ∈ {3, 4} into 10 = 3 and 10 ∈ {4}
cases h, -- To prove that not(10 = 3)
cases h, -- To prove that not(10 ∈ 4)
end 

-- Alternative way
example : 10 ∈ Xᶜ :=
begin
unfold X,
simp,
end 



/- 3. Relations [30 points] -/

/- A [15 points].

In this problem, you will formally define
what it means for a relation to be single-
valued, you will define a particular relation,
and you will prove that it is single-valued.

Part #1 [5 point].

Formally define single-valuedness for any 
binary relation r : α → β → Prop so that r 
being single valued means that (r x) can 
have (be satisfied by) two values, say y 
and z, only if y = z. Think about this hard 
enough that it really makes sense to you! 
In other words, if r x y ... You can fill
in the rest!
-/

def single_valued   -- predicate on relations
{α β : Type} 
(r : α → β → Prop) 
: Prop := ∀ (x : α) (y z : β), r x y → r x z → y = z

/- Part #2 [5 points]

Define a relation, sqrs : ℕ → ℕ → Prop, where 
sq x y is satisfied iff y is the square of x. 
-/

def sqrs : ℕ → ℕ → Prop 
| x y := y = x * x

/- Part #3 [5 points] 

Now formally prove the proposition that the 
sqrs relation is single-valued.
-/

example : single_valued sqrs :=
begin
unfold single_valued,
assume x y z,
unfold sqrs,
assume xy,
assume xz,
rw xy,
rw xz,
end


/- B [5 points]

A mathematical function, f : α → β, is said 
to be injective if it never relates different 
α (first) values to the same β (second) value. 
The only way an injective function f can relate 
a to x and also b to x, is if a = b. A function
that satisfies this constraint is injective.
-/

def injective 
(α : Sort u)        -- any type from any universe
(β : Sort v)        -- any type from any universe
(r : α → β → Prop)  -- any relation on α and β 
(a b : α)           -- any two arbitrary α values
(x : β) :           -- any β value
Prop := r a x → r b x → a = b


/- C [10 points].

A mathematical function, f : α → β, is said to be 
a total function if it's defined (there is some 
β value) for *all* α values: ∀ (a : α), β. Indeed,
this is the meaning of the notation α → β in Lean
and similar logics. The upshot is that functions 
in Lean can only be total.  Complete the following
proof that every function in Lean is total.
-/

example : 
  ∀ (α β : Type) 
  (f : α → β), 
    ∀ (a : α), 
      ∃ (b : β), 
        f a = b :=
begin
assume α β f a,
-- this guarantees that x is a β value (because f is α → β)
let x := f a,
-- then prove that this value of x corresponds to (f a)
apply exists.intro x,
refl,
end

