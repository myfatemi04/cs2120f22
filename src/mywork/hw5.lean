/-
The following line imports a tactic for
simplfying algebraic expressions of a certain
kind. We explain it in more detail below.
-/
import tactic.ring

/-
This assignment has three multi-part problems.
The first two problems will develop and test 
your understanding of exists introduction; and 
the third, of exist elimination. Problems that
ask you to state and prove a proposition will
get half credit for a correct proposition and
the other half for a correct proof. 
-/


/- *** Exists introduction *** -/

/- #1A.

State and prove the proposition that there's some
natural number whose square is 144.
-/

example: ∃ (n: ℕ), n * n = 144 :=
begin
apply exists.intro,
apply eq.refl (12 * 12),
end


/- #1B.
State and prove the proposition that there is 
some string, s, such that s ++ "!" is the string, 
"I love logic!." Note: In Lean, ++ is notation
for string.append, the function for gluing two
strings together into one.
-/

example : ∃ (s: string), (s ++ "!") = "I love logic!" :=
begin
apply exists.intro,
apply eq.refl ("I love logic" ++ "!"),
end

/- #1C.

Formally state and prove the proposition that
there are three natural numbers, x, y, and z, 
such that x*x + y*y = z*z. Hint: exists.intro
takes just one witness as a time, so you will
have to apply it more than once.
-/

-- We have two options here.

example: ∃ (x y z: ℕ), x * x + y * y = z * z :=
begin
use 3,
use 4,
use 5,
apply eq.refl,
end

example: ∃ (x y z: ℕ), x * x + y * y = z * z :=
begin
apply exists.intro 3,
apply exists.intro 4,
apply exists.intro 5,
apply eq.refl,
end

/- #1D
Define predicate called pythag_triple taking
three natural number arguments, x, y, and z,
yielding the proposition that x*x + y*y = z*z.
-/

def pythag_triple (x y z : ℕ) := x * x + y * y = z * z

/- #1E
State the proposition that there exist x, y, z, 
natural numbers, that satisfy the pythag_triple, 
predicate, then prove it. (Use "example : ...")
-/

-- We have two options here.

example: ∃ (x y z: ℕ), pythag_triple x y z :=
begin
use 3,
use 4,
use 5,
apply eq.refl,
end

example: ∃ (x y z: ℕ), pythag_triple x y z :=
begin
apply exists.intro 3,
apply exists.intro 4,
apply exists.intro 5,
apply eq.refl,
end

/- #2A

Define a predicate, (multiple_of n m), where
n and m are natural numbers and where the
proposition is true if and only if n is a 
multiple of m. Hint: What has to be true for 
n to be a multiple of m? There has to be some
other number involved, right?
-/

def multiple_of (n m : ℕ) := ∃ k, n = m * k  

/- #2B

Using the predicate multiple_of, state and 
prove the proposition that every natural number 
that is a multiple of 6 is also a multiple of 3. 

Hint: you can use "unfold multiple_of at h,"
to expand the definition of multiple_of in the
hypothesis, h (assuming you call it that).

Hint: Put the argument you will give to exists
intro in parentheses (needed for correct syntax).

Hint: You might end up with n = 3 * (2 * w) 
as a goal. The "ring" tactic in Lean will 
simplify this expression to n = 6 * w. 

Before you do the work, let's talk a little
more about the "ring" tactic. First, where does
the name come from? Second, what does it do?

A "ring" in college-level algebra (and beyond)
is any set of values (such as natural numbers) 
with + and * operations that satisfy the usual 
rules of arithmetic (such as the distributive
laws, the associativity of + and *, etc). Not
only the natural numbers form a ring, but so
do polynomials and many other kinds of "math"
objects as well.

The ring tactic is used to put any expression 
involing any ring into a "normal" form. What 
"normal" means in this context is that if you 
put two mathematically equivalent but different 
expressions into normal form, then you get the 
same "normalized" expression in both cases,
making it easy to test them for equality. 

So, in particular, if you want to know whether 
a+(b+c)=(a+b)+c, put both expresions in normal
form and see if they are equal (which again they 
are if + is addition in any "ring").

A good English translation of the use of the 
ring tactic is "by basic algebra."
-/


/-
Here's an example. Is ℕ addition associative? 
You know it is. Prove it formally and then fill
in the English language proof below. 
-/

example (n m k : ℕ) : n + (m + k) = (n + k) + m := 
begin 
ring,
end  
-- Enlish proof (it's short!): We know this through basic algebra

/-
Whoa! It's so easy to prove addition associative? 
Yep. Thankfully someone else wrote this beautiful 
tactic so you don't have to do the algebra yourself.
-/

/-
As a small aside on Lean syntax, if a tactic script 
is just one tactic long, you can use "by <tactic>" 
instead wrapping the tactic in a begin-end block.
-/
example (n m k : ℕ) : n + (m + k) = (n + k) + m := by ring

/-
Ok, with that background in place, let's 
return to the problem we were discussing. 
Is it true that if any natural number is
a multiple of 6 then it's also a multiple 
of 3?

Before you even consider writing a proof, 
whether in Lean or in English, figure out 
yourself whether the proposition appears to 
be true or not. Try to prove it "mentally"
to yourself first. 

The key question here is, what does it even 
mean for a  number, n, to be a multiple of 6. 
Well, n is a multiple of 6 if there's some 
number, say k, such that n = k * 6, right? 

Now you should be able to formally write, and 
then prove, the proposition on the table. Is 
it true that for any n, if n is a multiple of 
6 then it's a multiple of 3? 

What would it mean to be a multiple of 3? It
means there's some *other* number such that n
is that number times 3. The trick to this kind
of question is to figure out what that number
has to be. Also, be sure to use multiple_of in
formally stating the proposition to be proved.
-/

example: ∀ (x: ℕ), multiple_of x 6 → multiple_of x 3 :=
begin
assume x,
unfold multiple_of,
assume h1,
cases h1 with w1 hw1,
apply exists.intro (2 * w1) _,
let equ: x = 3 * (2 * w1) := (calc x = 6 * w1: hw1 ... = 3 * (2 * w1): by ring),
exact equ,
end 


/- #2C.

Is it true that if n is a multiple of h, and h
is a multiple of k, that n is a multiple of k? 
Formally state and then prove the proposition.

In writing this proof, you might need to use one
of the two axioms of equality, via the "rewrite" 
tactic (abbreviated rw) in Lean. Here's the idea.

If you've already proved/know, and so have in 
your context a proof of, an equality, such as 
pf : m = k, and if m appears in your goal, then
you can replace the m with k by using "rw pf",
and your goal will mean exactly the same thing.
The rewrite tactic uses the axiom that states
that you can replace equals by equals without
changing the truth values of propositions. 
-/

example (n h k : ℕ):
(multiple_of n h ∧ multiple_of h k) → multiple_of n k :=
begin
unfold multiple_of,
assume h1,
-- https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html
-- We extract the constants and predicates from n | h and h | k
-- Then, we say that the constants multiply through associativity
-- n = hc1
-- h = kc2
-- n = (kc2)c1
-- n = k(c2c1)
-- Then, we use exists.intro
-- This "let" statement says, we are letting the values c1, nh and c2, hk be defined
-- by h1.left and h1.right, and then plugging them into the next statement
exact (let ⟨c1, nh⟩ := h1.left, ⟨c2, hk⟩ := h1.right in
-- Construct a proof that n = c1 * c2 * h
⟨c2 * c1, calc
		n = h * c1: nh
		... = k * c2 * c1: congr_arg _ hk
		... = k * (c2 * c1): by ring⟩ -- or `by rw ←mul_assoc`
),
end



/- *** exists.elimination *** -/

/- #3A

Formally state and prove that if everyone 
who knows logic is cool and someone knows 
logic, then *someone is cool*. We set up 
everything you need to formally state this
conclusion (first hole/underscore). All 
you then have to do is to fill in is the
proof (second _).

Exists elimination: If anything exists with a certain
property, and we know that that property implies
another preposition, then we can prove the other
preposition.
-/

example 
  (Person : Type)
  (KnowsLogic : Person → Prop)
  (isCool : Person → Prop)
  (LogicMakesCool : ∀ (p), KnowsLogic p → isCool p)
  (SomeoneKnowsLogic : ∃ (p), KnowsLogic p) :
	∃ p, isCool p :=
begin
apply exists.elim SomeoneKnowsLogic _,
assume P P_knows_logic,
apply exists.intro P ((LogicMakesCool P) P_knows_logic),
end

example 
  (Person : Type)
  (KnowsLogic : Person → Prop)
  (isCool : Person → Prop)
  (LogicMakesCool : ∀ (p), KnowsLogic p → isCool p)
  (SomeoneKnowsLogic : ∃ (p), KnowsLogic p) :
	∃ p, isCool p :=
begin
apply exists.elim SomeoneKnowsLogic _,
assume P P_knows_logic,
exact ⟨P, (LogicMakesCool P) P_knows_logic⟩,
end


/- #3B

Formally state and prove the proposition that if
someone is not happy then not everyone is happy.
-/

-- We're proving this by contradiction
-- We pick our unhappy person, insert it into our "for all" statement,
-- and show that a contradiction is created when the conclusion of our
-- "for all" statement is brought to the "this person being happy would
-- cause the universe to explode" statement
example 
  (Person : Type)
  (Happy : Person → Prop) :
  (∃ (p: Person), ¬(Happy p)) → ¬(∀ (q: Person), Happy q)
  :=
begin
assume h1,
cases h1 with unhappy_person unhappy_person_is_unhappy,
assume h2,
apply unhappy_person_is_unhappy (h2 unhappy_person),
end

/- #3C

Formally state and prove that  
"everyone is happy" is *equivalent*
(iff) to "no one is unhappy." 

Hint: In one direction, you might need 
to use classical reasoning; and remember
you can get a proposition (on which to do
classical case anaysis) by applying a
predicate to the right arguments. And
a final hint: Sometimes you have to use
information you have to prove something 
you don't yet have in order to make it
clear that there's a contradiction in
your set of assumptions. 
-/
example 
  (α : Type)
  (P : α → Prop) :
  (∀ (p: α), P p) ↔ (¬∃ (q: α), ¬(P q)) :=
begin
split,
assume h1,
assume h2,
cases h2 with person person_is_unhappy,
exact person_is_unhappy (h1 person),

-- nobody is unhappy
assume h1,
-- now prove that all people are happy.
assume happy_person,
-- someone is either happy or they aren't.
cases classical.em (P happy_person),
-- if they are happy, then we rest our case
assumption,
-- if they are unhappy, we can show a contradiction
apply false.elim,
-- this unhappy person shows that there is at least
-- one unhappy person, which directly contradicts
-- our assumption
let h1c: ∃ (q: α), ¬P q := ⟨happy_person, h⟩,
apply h1 h1c,
end 



/- #3D

Formally state and prove the proposition
that if there doesn't exist an object of
some type T with some property, P, then
any object of that type has the property
¬P. Hint: We represent a "property" of 
objects of a certain type as a predicate
taking objects of that type.
-/

-- Not going to write notes on this because it's very similar to
-- what was done above
example 
  (T : Type)
  (P : T → Prop) :
  ¬(∃ o, P o) → ∀ o, ¬(P o) :=
begin
assume h1,
assume obj,
cases classical.em (P obj),
let h1c: ∃ o, P o := ⟨obj, h⟩,
apply false.elim (h1 h1c),
assumption,
end


/- #3E
Formally state and prove the proposition
that if there's an object with the property 
of having property P or property Q then 
there's an object with property P or there's 
an object with property with property Q.
-/

example 
  (α : Type)
  (P : α → Prop)
  (Q : α → Prop): 
  (∃ (o), P o ∨ Q o) → (∃ (o), P o) ∨ (∃ (o), Q o) :=
begin
-- Assume that there exists some object with other
-- property P or property Q
assume h,
-- We take the object and the knowledge that it has
-- either the property P or Q
cases h with o P_or_Q,
-- We do a case analysis; it could be property P or
-- property Q that is true, let's divide and conquer
cases P_or_Q with Po Qo,
-- The case where it's property P that's true
let Po_exists: ∃ (o), P o := ⟨o, Po⟩,
apply or.intro_left,
exact Po_exists,
-- The case where it's property Q that's true
let Qo_exists: ∃ (o), Q o := ⟨o, Qo⟩,
apply or.intro_right,
exact Qo_exists,
end

