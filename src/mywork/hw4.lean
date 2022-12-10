/-
CS 2120 F22 Homework #4. Due Oct 13.
-/

/- #1A [10 points]

Write a formal proposition stating that 
logical and (∧) is associative. That is, 
for arbitrary propositions, P, Q, and R,
P ∧ (Q ∧ R) is true *iff* (P ∧ Q) ∧ R is, 
too. Replace the placeholder (_) with your
answer.
-/

def and_associative := ∀ (P Q R), P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R

/- #1B [10 points]

Give an English language proof. Identify
the inference rules of predicate logic
that you use in your reasoning.
-/

/-
Answer: Because this is a problem of biimplication, it suffices
to show that both directions are true independently of each other.

1. If P and (Q and R) is true, then P is true, and (Q and R) is
true [and elimination]. If (Q and R) is true, then Q is true and R is
true [and elimination]. Therefore, P, Q, and R are true. Using
and introduction, we can conclude from P being true and Q being true
that (P and Q) is true. From (P and Q) being true and R being true,
we can use and introduction again to conclude that (P and Q) and R is
true.

2. If (P and Q) and R is true, then (P and Q) is true and R is true
[and elimination]. If (P and Q) is true, then P is true and Q is true
[and elimination]. Therefore, P, Q, and R are true. Using and introduction,
we can conclude from Q being true and R being true that (Q and R) is
true. From P being true and (Q and R) being true, we can use and
introduction again to conclude that P and (Q and R) is true.

Because the propositions are true in both directions, they must be
true iff each other.
-/

/- #1C [5 points]

Give a formal proof of the proposition.
Hint: unfold and_associative to start.
-/

theorem
and_assoc_true: and_associative
:=
begin
  unfold and_associative,
  -- Start a for-all introduction
  assume P Q R,
  -- Now, we just need to prove a bi-implication. We do this with
  -- iff.intro. This splits us into two subgoals.
  apply iff.intro _ _,

  -- Cases is used to decompose an OR or an AND into two cases.
  assume pqr,
  cases pqr with p qr,
  cases qr with q r,
  -- "let" is used for proofs. "assume" is used for propositions.
  let pq := and.intro p q,
  exact and.intro pq r,

  assume pqr,
  cases pqr with pq r,
  cases pq with p q,
  exact and.intro p (and.intro q r),
end



/- #2A [10 points]

Write the proposition that ∨ is associative.,
analogous to the proposition about ∧ in #1.
-/

def or_associative : Prop := 
  ∀ (P Q R : Prop), P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R


/- #2B [10 points]

Write an English language proof of it, citing
the specific inference rules you use in your
reasoning.
-/

/-
Answer: Because this is a problem of biimplication, it suffices
to show that both directions are true independently of each other.

1. Assume that P ∨ (Q ∨ R) is true. 

-/


/- #2C [5 points]

Complete the following formal proof.
-/

theorem or_associative_true2 : or_associative :=
begin
unfold or_associative,
assume P Q R,
split,
assume porqorr,
cases porqorr with p qorr,
exact (or.intro_left R (or.intro_left Q p)),
cases qorr with q r,
exact or.intro_left R (or.intro_right P q),
apply or.intro_right, exact r,
assume porqorr,
cases porqorr with porq r,
cases porq with p q,
exact or.intro_left (Q ∨ R) p,
exact or.intro_right P (or.intro_left R q),
exact or.intro_right P (or.intro_right Q r),
end

theorem or_associative_true : or_associative :=
begin
unfold or_associative,
assume P Q R,

apply iff.intro _ _,

-- Forward direction
assume pqr,
cases pqr with p q_or_r,
exact or.intro_left R (or.intro_left Q p),

cases q_or_r with q r,
let pq := (or.intro_right P q),
exact or.intro_left R pq,

exact or.intro_right (P ∨ Q) r,

assume pqr,
cases pqr with p_or_q r,
-- Case for p_or_q
cases p_or_q with p q,
-- Case for p
exact or.intro_left (Q ∨ R) p,
-- Case for q
let qr := or.intro_left R q,
exact or.intro_right P qr,

-- Case for r
let qr := or.intro_right Q r,
exact or.intro_right P qr,

end


/- #3A [10 points]
Write a formal statement of the proposition.
-/

def arrow_transitive : Prop :=
  ∀ (X Y Z: Prop), (X → Y) → (Y → Z) → (X → Z)

/- #3B [10 points]

Write an English language proof of the proposition
that for any propositions, X, Y, and Z, it's the
case that (X → Y) → (Y → Z) → (X → Z). In other
words, implication is "transitive." Hint: Recall
that if you have a proof of, say, X → Y, and you 
have a proof of X, you can derive a proof of Y by
arrow elimination. Think of it as applying a proof
of an implication to a proof of its premise to get
yourself a proof of its conclusion.
-/

/-
Answer: Because this is a problem of implication, it suffices
to show that whenever the context is true, the conclusion must
follow. Therefore, we can start by assuming that X implies Y, that
Y implies Z, and finally that X is true.

If we assume X, then because X implies Y, we can use arrow elimination
to conclude that Y is true. If we assume Y, then because Y implies Z,
we can use arrow elimination to conclude that Z is true. Therefore, Z is
true whenever X is true, so our proposition is valid.
-/


/- #3C [5 points]. 
Write a formal proof of it.
-/
example: arrow_transitive :=
begin
assume X Y Z,
assume xy yz,
assume x,

exact yz (xy x)
end


/- #4
Suppose that if it's raining then the streets
are wet. This problem requires you to prove that
if the streets are not wet then it's not raining.
-/

/- #4A [10 points]

Start by writing the proposition in predicate
logic by completing the following answer.
-/

def contrapositive : Prop :=
  ∀ (Raining Wet : Prop), 
    (Raining → Wet) → (¬Wet → ¬Raining)


/- #4B [10 points].
-/

theorem contrapositive_valid : contrapositive :=
begin
unfold contrapositive,
assume Raining Wet,
assume rw,
assume not_wet,

-- Show that rain is impossible
assume raining,
-- False elimination
exact not_wet (rw raining),
end

/- #4C [5 points]. 

Give an English language proof of it.

We assume that rain implies a wet street, and we want to prove
that a dry street implies no rain. Our tactic is to assume that
the street is dry, and then show that rain is impossible. We can
do this through contradiction. If the street is dry, but it is also
raining, then we can use the assumption that rain implies a wet
street to derive a contradiction. Therefore, we can prove that
if rain implies a wet street, and we know that the street is not
wet, then we can conclude that it is not raining.
-/


/- #5. Extra credit.

Complete the following formal proof of the 
proposition that if for any proposition P, 
P ∨ ¬P is true, then for any propositions, 
X and Y, if it's not the case that X or Y
is true then it is the case that ¬X and ¬Y 
is true. 
-/

theorem demorgan1 : 
  (∀ (P : Prop), P ∨ ¬ P) → 
    ∀ (X Y : Prop), 
      ¬(X ∨ Y) → (¬X ∧ ¬Y) :=
begin
assume em X Y nx_or_y,
cases (em X) with x nx,
-- Case for X being true
-- Show that X being true makes ¬(X ∨ Y) false
let x_or_y := or.intro_left Y x,
contradiction,

-- Case for X being false
apply and.intro nx _,
-- Show that y cannot be true
assume y,
let x_or_y := or.intro_right X y,
contradiction,
end

/-
A comment on or.intro_left and or.intro_right.
In Lean each of these takes two arguments: a
proof of the disjunct -- the proposition on 
one side of the ∨ -- that is to be proven true, 
*and* it takes as an argument the proposition 
that is not being proven true. In applications 
of these rules the proposition argument (not 
being proven) comes first, while the proof 
argument comes second.

The reason is that Lean needs to know what 
overall proposition is being proved. From the
proof argument it can infer the proposition 
being proved, but it needs the other proposition
as well to know the full (X ∨ Y) disjunction to
be proved. 

Here's an example:
-/

example : 0 = 0 ∨ 0 = 1 :=
begin
apply or.intro_left (0 = 1) rfl
/-
The "rfl" serves as a proof of 0=0.
But in addition, as the first argument
to or.intro, we need to provide the
*proposition* that is not being proved.
Here's that's (0 = 1). In contexts
where Lean can infer both disuncts,
you can use the simpler or.inl or 
or.inr, each of which just takes one
argument: a proof of the left or of 
the right side, respectively.
-/
end

