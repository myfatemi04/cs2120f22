import data.set
import logic.relation

/- ****** -/
/-   #1   -/
/- ****** -/

 /-
 A [5 points].
 
 Give a formal definition of the proposition
 that for every natural number, n, there's a
 natural number, m, that's one more than n.
 Replace the _ placeholder with your answer.
We will call your proposition prop1.
 -/

def prop1 : Prop := ∀ (n: ℕ), ∃ (m: ℕ), m = n + 1


 /-
 B [5 points].

 Give a formal proof of this proposition. Include
 a brief one line comment just before each line in 
 your proof script explaining in English what it
 does.
 -/

 example : prop1 :=
 begin
 -- Assume we have an arbitrary natural number, `n`
 assume n,
 -- The number `n + 1` satisfies the constraint
 -- and is also a natural number
 exact ⟨n + 1, rfl⟩,
 end
 

 /- #C [5 points]. Write a brief English language
 proof of prop1.

 Answer: Assume n is arbitrary. We're to show that 
 there's a one larger number. The number, n + 1,
 satisfies the constraint.
 
 We can show this because every natural number has a
 successor which is equal to itself plus 1.
 
 QED.
 -/



/- ****** -/
/-   #2   -/
/- ****** -/

/-
We start by defining two "enumerated" data types, 
each with three values. We'll call them "lets" and
"nums," short for letters and numbers. The letters
are A, B, and C; and the numbers are one, two, and
three.
-/

inductive lets : Type
| A
| B
| C

inductive nums : Type
| one
| two
| three

open lets nums


/- #A [5 points]

Define a function, l2n_ni (short for "letters to
numbers, not injective") using "by cases" syntax,
where l2n_ni is not injective. We don't care what
non-injective function you define, as long as it
is not injective. In a brief comment afterwards,
explain what makes it not injective.
-/

def l2n_ni : lets → nums
-- add rules here
| A := one
| B := one
| C := two

-- Answer (what makes it non-injective?):
/-
The fact that there are multiple inputs that have the same
output makes it non-injective. In this case, `A` and `B` both
have their output as `one`. This violates the condition of injective
functions that if a relation exists between two inputs and the
same output, the two inputs must be the same.
Formally, `(l2n_ni A one) ∧ (l2n_ni B one) → A = B` is not satisfied,
because A ≠ B.

`injective l2n_ni := ∀ (a b: lets), l2n_ni a = l2n_ni b → a = b`
-/

/- #B [5 points]

Define a function, l2n_s (short for "letters to
numbers, surjective") using "by cases" syntax,
where l2n_s is surjective. We don't care what
surjective function you define. 
-/

def l2n_s : lets → nums
-- add rules here
| A := one
| B := two
| C := three

/- #C [5 points] 

Write a brief English-language proof showing that
your function is surjective. You must cite what it
means to be surjective (be mathematically precise).
Hint: You'll have to assume you're given any letter
as input. What you do with that arbitrary value to
complete the proof is the question to answer. Once
you have that, the rest is pretty straightforward.

Answer: This is surjective because every element
of the output space (`nums`) has some corresponding
element in the input space (`lets`) for the function
`l2n_s`.

Formally, this requires that `l2n_s` be single-valued,
and that for every element `num` of `nums`, there exists an element
`let` of `lets` such that `l2n_s let num`.

`surjective l2n_s := single_valued l2n_s → (∀ b, ∃ a, l2n_s a = b)`
-/

/- # EXTRA CREDIT [5 points] 

Prove formally that l2n_s is surjective.
-/
open function

lemma l2n_s_surjective: surjective l2n_s :=
begin
unfold surjective,
-- We choose an arbitrary number
assume arbitrary_num,
-- For all possible arbitrary numbers:
cases arbitrary_num,
-- `A` satisfies the constraint for `one`
exact ⟨A, rfl⟩,
-- `B` satisfies the constraint for `two`
exact ⟨B, rfl⟩,
-- `C` satisfies the constraint for `three`
exact ⟨C, rfl⟩,
end



/- ****** -/
/-   #3   -/
/- ****** -/


/- #A [ 5 points] 

Write a formal definition of the predicate,
"is_even," taking a single natural number, n,
and reducing to the proposition that n mod 2
is 0. When you have it right, the first test
should pass, the second, fail, the third pass,
etc. 
-/

-- Answer

def is_even : ℕ → Prop
| n := n % 2 = 0
-- or equivalent

-- tests
example : is_even 0 := rfl    -- even
example : is_even 1 := rfl    -- not even
example : is_even 2 := rfl    -- even
example : is_even 3 := rfl    -- not even
example : is_even 4 := rfl    -- even
example : is_even 5 := rfl    -- not even


/- #B [5 points]

Next, use set builder (comprehension) notation
to define the set of all even numbers, using
is_even as a "membership" predicate.
-/

def evens : set ℕ := {n: ℕ | is_even n}

/-
The next few problems use the following 
set.
-/

def under5 : set ℕ := {0, 1, 2, 3, 4, 5}

/- #C [5 points]

Prove: 2 ∈ evens ∩ under5. Hint: remember
what ∩ means logically, then use the right
logical inference rule. If you can't give
a formal proof, give a precise English
language proof instead, being precise
about the reasoning steps.
-/

example : 2 ∈ evens ∩ under5 :=
begin
unfold evens under5 is_even,
-- Set intersection just means we apply "and" to the membership
-- predictates. Therefore, we have to prove that
-- (2 % 2 = 0) ∧ (2 ∈ {0, 1, 2, 3, 4, 5}).

-- Let's split this into two subproblems.
-- Then, we will have two propositions to prove:
-- 1) 2 % 2 = 0
-- 2) 2 ∈ {0, 1, 2, 3, 4, 5}
split,
-- 2 % 2 = 0: We can use the reflexivity property.
exact rfl,
-- 2 ∈ {0, 1, 2, 3, 4, 5}
-- 2 = 0 ∨ (2 = 1 ∨ (2 = 2 ∨ (2 = 3 ∨ (2 = 4 ∨ (2 = 5)))))
-- To apply intro_right, we need to prove
-- (2 = 1 ∨ (2 = 2 ∨ (2 = 3 ∨ (2 = 4 ∨ (2 = 5)))))
apply or.intro_right,
-- To apply intro_right again, we need to prove
-- 2 = 2 ∨ (2 = 3 ∨ (2 = 4 ∨ (2 = 5)))
apply or.intro_right,
-- To apply intro_left, we need to prove 2 = 2
apply or.intro_left,
-- To do this, we just use the reflexivity property
exact rfl,
end 

-- Alternative answer:


/- D [5 points]

Consider the set, justA = { A }, of 
"lets" (letters) as (defined above). 
-/

def just_A : set lets := { A } 

/-
Prove that (the letter) C is in 
just_Aᶜ, the complement of just_A. 
If you have problems getting Lean to
check your proof, you may give an 
English language version, instead,
but be sure to state *exactly* what 
(C ∈ just_Aᶜ) means and each reasoning 
step in your informal proof.

-/

example : C ∈ just_Aᶜ := 
begin
-- Answer here
-- C ∈ just_Aᶜ means C ∉ just_A, which means C ∈ just_A → false
-- Therefore, we can show that C ∈ just_Aᶜ by assuming C ∈ just_A
-- and showing that this results in a contradiction.
assume in_just_A,
-- None of the membership rules are satisfied for `C`.
-- Therefore, `C` being in `just_A` results in a contradiction.
cases in_just_A,
end

-- Alternative answer: 

/-
Proof: 
-/


/- #E [5 points]

How many subsets are there of 
each of the following sets? You can
give an approximate answer on #4. 
Hint on 5: Recall that 𝒫 S means
the powerset of a set, S. So on
question 5, we are asking how many
subsets are there of the powerset 
of {0,1,2}.

The number of subsets = 2 ^ number of elements in the set.

                          Answers
1. {}                     -- 1
2. {0,1,2}                -- 8
3. {0,1,2,3,4,5,6,7,8,9}  -- 1024
4. { n | 0 ≤ n ∧ n ⋖ 30}  -- 16 (n ∈ {0, 1, 2, 3, 4})
5. 𝒫 {0,1,2}              -- 256 (𝒫 {0, 1, 2} = set of size 8, so 2^8 subsets)
-/



/- ****** -/
/-   #4   -/
/- ****** -/


/- A [5 points]

Define a function, prod_to: ℕ → ℕ, that,
when applied to a given n returns: 1 if n
is zero; and otherwise (if n = succ n' for 
some n') the product of n and prod_to n'. 
You likely have it right when the tests all
pass.
-/

def prod_to : ℕ → ℕ 
| nat.zero := 1
| (nat.succ n') := prod_to n' * (nat.succ n')

example : prod_to 0 = 1 := rfl
example : prod_to 1 = 1 := rfl
example : prod_to 2 = 2 := rfl
example : prod_to 3 = 6 := rfl
example : prod_to 4 = 24 := rfl


/- #B [5 points]

What is the common name of this function?

Answer: Factorial
-/


/- #C [5 points]

Give a brief explanation *why* proving these
two "lemmas" proves that the given property 
holds for *every* natural number.

(Skip)

Answer: We are defining the property inductively.
To do this, we show that the property exists
for the base case and the property exists for the
successor of any number. If we want to find the
property for any arbitrary number, we can start from
the base case and find the property for the successor
until we reach our number.
-/


/- #D [5 points]

This question tests your understanding of
the induction axiom for natural numbers.

You've learned that there are 2^n possible
"interpretations" of n propositional (i.e.,
Boolean) variables. Now *prove* that this 
is true. We'll help a bit. You fill in the
missing parts. 

1. The property, P, of n, we want to prove 
is that "the number of interpretations of 
a collection of n Boolean variables is 2^n." 

2. What we then want to prove is ∀ n, P n.  

3. What specific proposition do we want
to prove as the "base case" in a proof by
induction? Be mathematically precise.

Answer: We want to prove that there is only
one interpretation of an empty set of variables.

4. What specific proposition do we want to
prove as the "inductive case" in a proof by
induction? Be mathematically precise.

Answer: We want to prove that if we have a set
of n variables with 2^n interpretations, then adding
another variable results in a set of n + 1 variables with
2^(n + 1) interpretations.

5. Which expression in your preceding answer
corresponds to the induction hypothesis.

Answer: that our set of n variables has 2^n interpretations
-/




/- ****** -/
/-   #5   -/
/- ****** -/


/- #A [5 points] 

Prove the following formally. 
-/

example : ∀ (P Q : Prop), P ∧ Q → P ∨ Q :=
begin
-- Assume our two arbitrary propositions, P and Q
assume P Q,
-- We must prove that P ∧ Q → P ∨ Q. It will suffice
-- to show that P ∨ Q given P ∧ Q, so we assume P ∧ Q.
assume P_and_Q,
-- We apply or.intro_left with P ((P ∧ Q).left is P)
apply or.intro_left _ P_and_Q.left,
end

/- #B [5 points] 

Prove the following formally, writing
a brief comment before each line of your
proof script describing the logical step
it implements. Then below the formal proof
give an English-language version of it.
If the second half of the proof uses the
same strategy as the first half, you can,
in English, say, "the rest of the proof
uses the same strategy," and be done.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P :=
begin
-- Assume our two arbitrary propositions, P and Q
assume P Q,
-- We have to prove this in both directions. Therefore,
-- we can split it into proving P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q.
split,
-- Case 1: P ∨ Q → Q ∨ P
-- It will suffice to show Q ∨ P given P ∨ Q, so we assume P ∨ Q.
assume P_or_Q,
-- We perform case analysis on P ∨ Q
cases P_or_Q with p q,
-- Case 1a: P
-- We know that P is true, so we can apply or introduction on the right
-- to show Q ∨ P.
exact or.intro_right Q p,
-- Case 1b: Q
-- We know that Q is true, so we can apply or introduction on the left
-- to show Q ∨ P.
exact or.intro_left P q,

-- Case 2: Q ∨ P → P ∨ Q
-- It will suffice to show P ∨ Q given Q ∨ P, so we assume Q ∨ P.
assume Q_or_P,
-- We perform case analysis on Q ∨ P
cases Q_or_P with q p,
-- Case 2a: Q
-- We know that Q is true, so we can apply or introduction on the right
-- to show P ∨ Q.
exact or.intro_right P q,
-- Case 2b: P
-- We know that P is true, so we can apply or introduction on the left
-- to show P ∨ Q.
exact or.intro_left Q p,
end

/-
Proof.

Goal: Prove ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P.

We start by assuming two arbitrary propositions, P and Q.

We then split the proof into two cases: P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q.

Case 1: P ∨ Q → Q ∨ P

It will suffice to show Q ∨ P given P ∨ Q, so we assume P ∨ Q.

We perform case analysis on P ∨ Q. We have two cases: P is true, or Q is true.
 * If P is true, then we can apply or introduction on the right to show Q ∨ P.
 * If Q is true, then we can apply or introduction on the left to show Q ∨ P.

Case 2: Q ∨ P → P ∨ Q

It will suffice to show P ∨ Q given Q ∨ P, so we assume Q ∨ P.

We perform case analysis on Q ∨ P. We have two cases: Q is true, or P is true.
 * If Q is true, then we can apply or introduction on the right to show P ∨ Q.
 * If P is true, then we can apply or introduction on the left to show P ∨ Q.

-/



/- ***************** -/
/-    EXTRA CREDIT   -/
/- ***************** -/

/-
We define a new polymorphic data type, 
tree. A tree is either a "twig" that 
carries a value of some type α; or a 
tree is a "root" that carries a value 
of type α and two "children,"" each 
itself such a tree. The definition is
polymorphic in the sense that values
in the tree can be of any type, α.
-/

inductive tree (α : Type)
| twig (a : α) : tree
| root (a : α) (left right : tree) : tree

open tree

/- #A 

Define a tree, t, of natural numbers, with 0 
at the root and two sub-trees: the left is a 
twig with the value 1, and the right is a twig
with the value 2. Here's a diagram:

          0     -- root with 0 and two sub-trees
         / \
        1   2   -- twigs with 1, 2; no sub-trees
-/

-- Create a root with the value `0` and left and right trees
-- being twigs with values `1` and `2`, respectively.
def t : tree nat := root 0 (twig 1) (twig 2)


/- #B

Define a function, tree_size, that takes any
tree and returns the number of values stored 
in it. For example, t stores three values (0,
1, and 2). Reminder: Put patterns in parens.
Answer by completing the partial definition 
we provide.
-/

def tree_size {α : Type} : tree α → ℕ  
| (twig v) := 1
| (root a tree_left tree_right) := 1 + tree_size tree_left + tree_size tree_right

-- test cases
example : tree_size (twig 0) = 1 := rfl
example : tree_size t = 3 := rfl


/- #C 

Here's the induction axiom for the
tree type.
-/

#check @tree.rec_on

/-
tree.rec_on :
  Π {α : Type} 
  {motive : tree α → Sort u_1} 
  (n : tree α),
    (Π (a : α), motive (twig a)) →
    (Π (a : α) 
      (left right : tree α), 
      motive left → 
      motive right → 
      motive (root a left right)) → 
    motive n

Explain in English exactly how you'd prove, by
induction, that every tree has some property P. 
Be sure to explain what specific "lemmas" have to
be proved to complete the application of the
induction axiom for tree.

Answer: We would prove this with induction. First, we would
provide a proof of the base case. Then, we would provide a proof
that for any root, then given its left and right subtrees (and proofs
that they satisfy the property), we can prove that the root satisfies
the property. We would then use the induction axiom to prove that
the property holds for any tree.

Base case. The property holds for the twig case.
Inductive case. Given two trees that satisfy the property,
then a root with those as subtrees will also satisfy the property.
-/

