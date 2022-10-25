
/-
This is the CS2120 (Sullivan) midterm exam. 

The exam has 100 points total distributed over four
multi-part questions. There's an extra credit question
at the end. Points for each part are indicated.
-/

-- ****************** #1 [30 points] *******************

/- A. [5 points] 

Is it true in predicate logic that  
(false → true) ∧ (false → false)?
Answer: Yes. We know that false implying anything is true. Therefore,
false → true is true. By the same reasoning, false → false is true.
We can use and introduction on (false → true) and (false → false) to
demonstrate that (false → true) ∧ (false → false) is true.

-/

/- B. [10 points] 

Give a formal proof by completing the 
following "example" in Lean, or state 
in English that there is no such proof.

-/

example : (false → true) ∧ (true → true) :=
begin
apply and.intro,
-- Prove that false → true
apply false.elim,
-- Prove that true → true
assume T,
assumption,
end


/- C [15 points]. 

Give an English language proof of the proposition. 
Identify each inference rule you use at each point
in your argument. For example, at a certain point 
you might say something like this: By the ____ rule, 
it will suffice to show ____. Then you would go on
to show that what remains to be proved is valid. 

Answer: We want to prove that false implies true and
that true implies true. Therefore, it will suffice to
show that false implies true independent of true implies
true, by case analysis. (We can use and introduction later).

First: false implies true.
The simplest way to show this is through false elimination,
because anything follows from false. Or, we can assume the
context, immediately have a contradiction, and have a proof
of the conclusion.

Second: true implies true.
A simple way to do this is by assuming the context,
and then showing that the conclusion is true. We know that
the conclusion (true) is always true anyway. Therefore, when
we assume the context, we have a proof of the conclusion.

Then, we can unify these propositions through and introduction.
-/


-- ****************** #2 [30 points] *******************


/- 
"Resolution" is an inference rule that we 
haven't talked about before. It's valid in
propositional, classical, and constructive
predicate logic. We will present the rule,
in both propositional and predicate logic,
and will ask you to prove that is's valid
in each case.


In propositional logic, the resolution rule 
is ¬P ∨ Q, P ⊢ Q. To check its validity, we 
can write it as  (¬P ∨ Q) ∧ P → Q. Note: ∧ 
has higher precedence than →, so there are 
implicit parentheses around (¬P ∨ Q) ∧ P, 
making the overall proposition an implication.
-/


/- A. [5 points].

Give a brief English language explanation why this
inference rules makes sense: not a rigorous proof,
just an explanation of why Q has to be true under
the conditions give by the assumptions/premises.

Answer: If we know that ¬P or Q is true, then we know
that at least one of them is true. If ¬P isn't the one,
then it must be Q.
-/



/- B. [5 points]

Prove that this inference rule is valid in
propositional logic by giving a truth table for it. 
We'll give you a start. Fill in the rows then state
how you know from the truth table that the overall
proposition is valid.

P   Q   (¬P ∨ Q)    (¬P ∨ Q) ∧ P    ((¬P ∨ Q) ∧ P) → Q
------------------------------------------------------
f   f   t           f               t
f   t   t           f               t
t   f   f           f               t
t   t   t           t               t

Statement: We know that the proposition is valid because
it is true under all interpretations. In order words, given
any combination of possible values for P and Q, we know
that the position is true.

-/  


/- C. [10 points] 

Give a formal proof that the inference rule is 
valid in our constructive predicate logic. Fill
in a proof script here to construct your proof.
Hint: remember that the cases tactic applied to
a proof of a conjunction applied and.elim both
left and right, and when applied to a proof of 
a disjunction gives you two cases to consider,
where you need to show that the remining goal
is true in either case. 
-/

example : ∀ (P Q : Prop), (¬P ∨ Q) ∧ P → Q :=
begin
assume P Q,
assume H,
cases H,
cases H_left,
contradiction,
assumption,
end


/-
D. [10 points] Give an informal (English) proof 
that the inference rule is valid in predicate logic. 
Name each inference rule you use in your reasoning.

Answer: We want to prove that if ¬P or Q is true and P is true,
then Q is true. It will suffice to show that we can always construct
a proof of the conclusion given the context. If we assume the context
(that ¬P or Q is true), then at least one of ¬P or Q must be true.
Let's do a case analysis.

First, ¬P. We also know that P is true. Therefore, we have a
contradiction. ¬P is equivalent to P → false, and we have a
proof of P, so therefore we can construct a proof of false. Anything
follows from false, so our first case is covered.

Second, Q. This is what we were trying to prove anyway. Therefore,
the second case is covered.

Because both of the case analyses were valid, we know that the
inference rule is valid.
-/


-- ****************** #3 [20 points] *******************


/- 
A. [10 points]. Write formally (in constructive logic) 
the proposition that, for any propositions P and Q, if 
P is equivalent to Q (iff), then if P is true, then Q
is true.  Hint: put parentheses around your ↔ expression. 
-/

-- Don't try to write a proof here; just the proposition
def if_p_iff_q_then_if_also_p_then_q : Prop :=
    ∀ (P Q: Prop), (P ↔ Q) → (P → Q)

/-
B. [10 points] Give *either* a precise, complete English
language proof that this proposition is valid, naming 
each inference you you use in your reasoning, *or* give 
a formal proof of it using Lean. You do not have to give
both. 
-/

/- Option #1: Informal proof:
P iff Q is a bi implication. We can apply iff elimination
on the left to a proof of P iff Q to generate a proof that
P implies Q.
-/


/-
Option #2: Formal proof. Reminders: the iff elim
rules are called iff.mp and iff.mpr in Lean; or you
can use "cases" to apply the two elimination rules 
to a proof of a bi-implication automatically.
-/

example : if_p_iff_q_then_if_also_p_then_q :=
begin
assume P Q,
assume P_iff_Q,
exact iff.mp P_iff_Q,
end




-- ****************** #4 [20 points] *******************

/- #



A. [10 points] Suppose P is any proposition. In plain
English give a step by step explanation of how you would 
go about proving ¬P using proof *by negation*. 

Answer: We know that ¬P is equivalent to P → false. If,
given the assumption that P is true, we can construct
a proof of false, then we can use false elimination to
prove that ¬P must be true.

-/


/- B. [10 points] 

In plain English explain each step in a proof of P
*by contradiction*. Identify where a proof by negation 
(¬ introduction) occurs in the proof by contradiction. 
Explain what classical rule of inference you need to 
use to finish off such a proof. 

Answer: If, given a proof of P, we can construct a proof
of false, then we can use false elimination to prove that
¬P must be true. We can consider this a type of proof by
negation: given the assumption that ¬P is true, if we can
construct a proof of false, then we know that ¬¬P is true.
¬¬P is only equivalent to P if the law of the excluded
middle applies.
-/



/- Extra Credit [10 points for all three answers correct]

Suppose that "if it's sunny, it's hot, and also that if 
it's not sunny, it's hot. 


A. Is it hot in classical logic? 

Answer: Yes.


B. Is it hot "constructively?" Briefly explain your answer. 
    
Answer: No, because in constructive logic, there is no law of
the excluded middle, which we rely on here. If it is neither sunny
nor not sunny, then we cannot make a conclusion as to whether it
is hot or not given only these two implications.


C. Give a formal proof of your answer to the classical question. 
Use S and H as names to stand for the propositions, "it's sunny" 
and "it's hot," where S stands for "it's sunny" and H stands for
"it's hot."
-/

-- it's hot
example : ∀ (S H : Prop), (S → H) → (¬S → H) → H :=
begin
assume S H,
assume S_implies_H,
assume not_S_implies_H,
cases classical.em S with s_true s_false,
apply S_implies_H s_true,
apply not_S_implies_H s_false,
end

