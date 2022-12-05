import data.set

/- #1

Formally prove that if there's an object, a, of some 
type, α, having some property (satisfying a predicate), 
P, then not every object of type α fails to have property, 
P. Add a brief comment before each line of your proof 
script to provide what amounts to the outline of a good
English language proof.
-/

example (α : Type) (P : α → Prop) : (∃ a, P a) → (¬(∀ x, ¬ P x)) :=
begin
  -- Assume we have something that satisfies the property
  assume h,
  -- Do a proof by negation. What would happen if every
  -- object violated the property?
  assume h2,
  -- Select our object that satisfies the property
  -- and a proof that it does
  cases h,
  -- We have a contradiction. We have something that satisfies
  -- the property, but we also have something that violates the
  -- property.
  exact (h2 h_w) h_h,
end


/- Extra credit. 

The converse of this proposition is clasically true. If
not every object lacks propery, P, then there must be some
object that has it. If you try to prove the converse in
our constructive logic, what happens? Show you work, and
then briefly but clearly explain exactly what goes wrong.
-/



/- #2

Consider the following binary relation, r, with domain
and co-domain both being ℕ. For each following question,
answer yes/no then briefly justify your answer.

( domain = ℕ, r = {(0,0),(1,1),(2,2)}, co-domain=ℕ )

A. Is this relation reflexive? Yes -- every element is linked to itself
B. Is this relation symmetric? Yes -- every relation's inverse exists
C. Is this relation transitive? Yes -- every relation is linked to itself
D. Is this relation an equivalence relation? Yes -- all three are true
-/



/- #3

A binary relation, r, is said to be *anti-symmetric* 
if, for all values in its domain, a and b, if r a b 
and if r b a then a = b. Give an example of a familiar
arithmetic relation that's anti-symmetric, and briefly
explain why it's so.

Subtraction: (a - b) and (b - a) are additive inverses of
each other. For them to be the same, a and b must be equal.
-/


/- #4
A binary relation, r, is said to be *asymmetric* if
whenever, for any a and b, if r a b then ¬ r b a. Be
careful to note that asymmetry and antisymmetry are
different properties.  Answer each of the following 
sub-questions. We give you a formal definition of anti
-/

def is_asymmetric 
  {α : Type} 
  (r : α → α → Prop) : Prop 
  := ∀ (a b : α), r a b → ¬ r b a 

/- A.

Name a familar arithmetic relation that's asymmetric
and briefly explain why you think it's asymmetric.

Answer here: Greater than. If `a` is greater than `b`,
then `b` cannot be greater than `a`.
-/

/- C: 

An object cannot be related to itself in an asymmetric
relation. First, complete the following informal proof
of this statement.

Proof: Assume α, r, and a are as given (and in particular
assume that r is asymmetric). Now assume r a a. <finish
the proof>.

Answer here (rest of proof): This is because `r a a` would
imply `¬ r a a`, which is false.
-/

/- D.

Now prove a closely related proposition formally. 
Add a comment to each line of your formal proof 
so as to construct a good skeleton for a fluent 
English language proof.
-/

example
  (α : Type) 
  (r : α → α → Prop)
  (h : is_asymmetric r) :
¬ ∃ (a : α), r a a :=
begin
-- proof by negation
assume h2,
-- select our object that is related to itself
cases h2 with a h2,
-- show that given h (our knowledge of asymmetry),
-- r a a implies ¬r a a
have h3 := h a a,
-- apply (r a a → ¬r a a) to r a a, to get ¬r a a
-- then, demonstrate the contradiction
exact (h3 h2) h2,
end


/- #5
Prove that equality on an inhabited (non-empty) type 
is not assymetric. In the following formalization we
assume there is a value (a : α), which establishes 
that α is inhabited.
-/

example (α : Type) (a : α): ¬ is_asymmetric (@eq α) :=
begin
-- proof by negation
assume h,
-- show that anything is equal to itself
have h2: eq a a := rfl,
-- show that according to our asymmetry assumption,
-- eq a a implies ¬eq a a
have h3 := h a a,
-- using h3, show that eq a a implies ¬eq a a
have h4 := h3 h2,
-- show that eq a a is both true and not true, which
-- is a contradiction
contradiction,
end

/- Extra credit: What exactly goes wrong in a formal 
proof if you drop the "inhibitedness" condition? Give
as much of a formal proof as you can then explain why
it can't be completed (if it can't!).
-/



/- #6
Two natural numbers, p and q, are said to be 
"equivalent mod m" if p % m = q % m, which makes
"equivalence mod m" a binary relation on natural
numbers. Here's a formal definition of this binary
relation on the natural numbers (given an m).
-/

def equiv_mod_m (m : ℕ) : ℕ → ℕ → Prop := 
  λ p q : ℕ, p % m = q % m

/-
Prove using Lean's definition of "equivalence" that 
equiv_mod_m is an equivalence relation for any natural
number, m. Here you'll also use Lean's definitions of
reflexive, symmetric, and transitive. They are as we
have covered in class. 
-/

example : ∀ m : ℕ, equivalence (equiv_mod_m m) :=
begin
-- Make it easier to find where to start
unfold equivalence,
-- Get our natural number
assume m,
-- Show each case individually
split,
-- Make it easier to find where to start
unfold reflexive,
-- Show that for any natural number, x ...
assume x,
-- ... the relation is true (by reflexivity, which is implicit)
unfold equiv_mod_m,
-- Next case
split,
-- Make it easier to find where to start
unfold symmetric,
unfold equiv_mod_m,
-- Show that for any natural numbers, x and y,
-- x % m = y % m implies y % m = x % m
assume x y,
-- We do this by assuming x % m = y % m, then
assume h,
-- showing that y % m = x % m through symmetry
exact eq.symm h,
-- Next case
-- Make it easier to find where to start
unfold transitive,
unfold equiv_mod_m,
-- Show that for any natural numbers, x, y, and z,
-- x % m = y % m and y % m = z % m implies x % m = z % m
assume x y z,
-- We do this by assuming x % m = y % m and y % m = z % m,
assume h1 h2,
-- and showing that x % m = z % m through the transitive property
-- of equality.
apply eq.trans h1 h2,
end



/- #7
Consider the relation, tin_rel, that associates people 
with U.S. taxpayer id numbers, which we'll represent as 
natural numbers here. 

Assume this relation is single-valued. Which of the 
following properties does this relation have? Give
a very brief justification of each answer. Assume
the domain is all living persons, and the co-domain
is all natural numbers.

-- it's a function: yes
-- it's total: yes
-- it's injective (where "): yes
-- it's surjective (where the co-domain is all ℕ): no
-- it's strictly partial: no
-- it's bijective: no (co-domain is all ℕ)
-/



/- #8
Suppose r is the empty relation on the natural 
numbers. Which of the following properties does
it have? Explain each answer enough to show you
know why your answer is correct.

-- reflexive: no, none of the natural numbers are linked to themselves
-- symmetric: yes, there is no case where r a b is true and r b a is not true
-- transitive: yes, there is no case where r a b and r b c are true but r a c is not true
-/



/- #9
Here's a formal definition of this empty relation.
That there are no constructors given here means there 
are no proofs, which is to say that no pair can be 
proved to be in this relation, so it must be empty.
-/

inductive empty_rel : ℕ → ℕ → Prop

/-
Formally state and prove you answer for each of the
three properties. That is, for each property assert
either that empty_rel does have it or does not have it, 
then prove your assertion. Include English-language 
comments on each line to give the essential elements 
of a good English language proof.
-/


example : ¬reflexive empty_rel :=
begin
-- Make it easier to find where to start
unfold reflexive,
-- Proof by negation
assume h,
-- Pick the number 0, and show that there is no
-- proof of empty_rel 0 0
let x := h 0,
-- There is no proof of empty_rel 0 0, so we have false
cases x,
end

example : symmetric empty_rel :=
begin
-- Make it easier to find where to start
unfold symmetric,
-- Start our proof by selecting our two natural numbers and an assumption
-- that r a b implies r b a.
assume a b h,
-- empty_rel a b must be false, therefore we can prove anything
cases h,
end

example : transitive empty_rel :=
begin
-- Select our three natural numbers and an assumption of r a b and r b c
assume a b c h k,
-- empty_rel a b must be false, therefore we can prove anything
cases h,
end

/- #10
A relation, r, is said to have the property of being 
a *partial order* if it's reflexive, anti-symmetric,
and transitive. Give a brief English language proof 
that the subset relation on the subsets of any set, 
S (of objects of some type), is a partial order. 

Pf:  
Suppose S is a set, with a ⊆ S and b ⊆ S subsets. Then

1. Reflexive: S ⊆ S is true by definition of ⊆
2. Anti-symmetric: If a ⊆ b and b ⊆ a, then a = b. This is true by definition of ⊆.
   If a is a strict subset of b, then b cannot be a subset of a.
3. Transitive: If a ⊆ b and b ⊆ c, then a ⊆ c. This is true by definition of ⊆.\
   ∀ (item), (a has item → b has item) → (b has item → c has item) → (a has item → c has item)

QED.
-/



/- #11 
Finally we return again to DeMorgan's laws, but
now for sets. You'll recall that these "laws" as we
have seen them so far tell us how to distribute ¬  
over ∨ and over ∧. You will also recall that set
intersection (∩) is defined by the conjunction (∧) 
of the membership predicates, set union (∪) by the
disjunction (∨), and set complement (Sᶜ for a set,
S), by negation (¬). It makes sense to hypothesize 
that we can recast DeMorgan's laws in terms of the
distribution of complement over set union and set
intersection. Indeed we can. Your job is to state
and prove (formally) the first DeMorgan laws for 
sets, which states that the complement of a union
of any two sets equals the intersection of their 
complements.

Hint: To prove that two sets are equal, S = T, use
the ext tactic. It applies a new axiom (called set 
extensionality) that states that to prove S = T it 
suffices to prove S ↔ T, viewing the sets as being
defined by their logical membership predicates. You
know how to handle bi-implications. The rest you 
can do by seeing "not," "and," and "or" in place 
of complement, conjunction, and disjuction, resp.  
-/

example 
  (α : Type) 
  (a b: set α) :
  (a ∪ b)ᶜ = aᶜ ∩ bᶜ := 
begin
-- Set it up for regular logic
ext,
split,

-- First case: x in complement of union → x in intersection of complements
-- Assume x in complement of union
assume h,
-- Prove that x is in either complement
split,
-- Prove that x is in complement of a
-- Assume x is in a
assume ax,
-- Show that this means that x is in the union
let abx: a x ∨ b x := or.inl ax,
-- Create a contradiction
exact h abx,
-- Prove that x is in complement of b
-- Assume x is in b
assume bx,
-- Show that this means that x is in the union
let abx: a x ∨ b x := or.inr bx,
-- Create a contradiction
exact h abx,

-- Second case: x in intersection of complements → x in complement of union
-- Assume x in intersection of complements
assume h,
-- Prove that x is not in the union
-- Assume that x is in the union
assume in_union,
-- Go case by case: x is in a, and/or x is in b.
cases in_union with in_a in_b,
-- Show that this contradicts the membership predicate of the first complement
apply h.left in_a,
-- Show that this contradicts the membership predicate of the second complement
apply h.right in_b,
end


