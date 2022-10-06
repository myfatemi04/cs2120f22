/-
CS2120 Fall 2022 Sullivan. Quiz #1. Edit your answers into
this file using VSCode. Save the file to your *local* hard 
drive (File > Save As > local > ...). Submit it to the Quiz1
assignment on Collab.
-/

/-
#1: For each of the following questions give a yes/no answer 
and then a very brief explanation why that answer is correct.
To explain why your answer is correct, name the specific rule
of inference that tells you it's correct, or explain that 
there is no such valid inference rule.
-/

/-
#1A

If a ball, b, is round *and* b is also red, is b red?

A: yes/no: yes

B: Why? Because we can apply and elimination on the right. If we
know that the propositions are true together, then we know that
they are true individually.


#1B

If flowers make you happy and chocolates make you happy,
and I give you flowers *or* I give you chocolates, will
you be happy?

A: yes/no: yes

B: Why? We can apply or elimination. If we know that A -> C
and B -> C, then we can prove that A or B implies C.


#1C: If giraffes are just zebras in disguise, then the 
moon is made of green cheese?

A. yes/no: no

B. Why? Because no proof exists for the proposed conclusion,
the proposed conclusion must be false. We cannot construct
a proof that the moon is made of green cheese only given
a proof that giraffes are just zebras in disguise.


#1D. If x = y implies that 0 = 1, then is it true that
x ≠ y?

A. yes/no: yes

B. Why? This is based on a proof by contradiction. If we can
prove "false", and we are sure that "false" has no proofs, then
whatever proof led us to believe that "false" is "true" must
be invalid.



#1E. If every zebra has stripes and Zoe is a Zebra then
Zoe has stripes.

A. yes/no: yes

B. Why? We can use a universal specialization (also known as
for-all elimination). Because we know that all zebras have stripes,
then based on the knowledge that Zoe is a zebra, we can conclude
that Zoe has stripes.


#1F. If Z could be *any* Zebra and Z has stripes, then 
*every* Zebra has stripes.

A. Yes/no: yes

B: Why? We can use a universal generalization. Because any
arbitrary zebra has stripes, it is impossible to select a zebra
that does not have stripes. Therefore, all zebras have stripes.


#1G. If whenever the wind blows, the leaves move, and 
the leaves are moving, then the wind is blowing.

A. yes/no: no

B. Why? Not necessarily. This is based on the converse of "implies"
not necessarily being true. If we only have the knowledge X -> Y, then
we cannot prove that Y -> X.


#1H: If Gina is nice *or* Gina is tall, and Gina is nice,
then Gina is not tall. (The "or" here is understood to be
the or of predicate logic.)

A. yes/no: no

B. Why? This is affirming the disjunct. *Or* is not exclusive in
predicate logic, so both propositions can be true at the same time
and the "or" operator will still return true.
-/



/- 
#2

Consider the following formula/proposition in propositional
logic: X ∨ ¬Y.

#2A: Is is satisfiable? If so, give a model (a binding of 
the variables to values that makes the expressions true).

This is satisfied by X = True.

#2B: Is it valid? Explain your answer. 

This is not valid because there is an interpretation that
makes the proposition false: X = False; Y = True.

-/


/-
#3: 

Express the following propositions in predicate logic, by
filling in the blank after the #check command.

If P and Q are arbitrary (any) propositions, then if (P is 
true if and only if Q is true) then if P is true then Q is 
true.
-/

#check ∀ (P Q : Prop), (P ↔ Q) → (P → Q)



/-
#4 Translate the following expressions into English.
The #check commands are just Lean commands and can
be ignored here. 
-/


-- A
#check ∀ (n m : ℕ), n < m → m - n > 0

/-
Answer: If n and m are arbitrary natural numbers, and n is less
than m, then m minus n will be greater than zero.

Or: Subtracting a smaller number from a larger number will be positive.
-/

-- B

#check ∃ (n : ℕ), ∀ (m : nat), m >= n

/-
Answer: There exists at least one natural number n, such that
for all natural numbers m, m is greater than n.

Or: There is a smallest natural number.
-/


-- C

variables (isEven: ℕ → Prop) (isOdd: ℕ → Prop)
#check ∀ (n : ℕ), isEven n ∨ isOdd n

/-
Answer: Every natural number is either even or odd.
-/


-- D

#check ∀ (P : Prop), P ∨ ¬P

/-
Answer: Every proposition is either true or not true.
-/


-- E

#check ∀ (P : Prop), ¬(P ∧ ¬P)

/-
Answer: No proposition can be true *and* not true.
-/


/-
#5 Extra Credit

Next we define contagion as a proof of a slightly long
proposition. Everything before the comma introduces new
terms, which are then used after the comma to state the
main content of the proposition. 

Using the names we've given to the variables to infer
real-world meanings, state what the logic means in plain
natural English. Please don't just give a verbatim reading
of the formal logic. 
-/

variable contagion : 
  ∀ (Animal : Type) 
  (hasVirus : Animal → Prop) 
  (a1 a2 : Animal) 
  (hasVirus : Animal → Prop)
  (closeContact : Animal → Animal → Prop), 
  hasVirus a1 → closeContact a1 a2 → hasVirus a2

/-

We are given two animals, a way to determine if they have a virus,
and a way to determine if they are in close contact.

If a1 has the virus, and a1 is in close contact with a2, then a2 must
also have the virus.

If one animal is in close contact with another animal that has the virus,
then it also has the virus.
-/
