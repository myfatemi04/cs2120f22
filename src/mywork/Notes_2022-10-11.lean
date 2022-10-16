/-

Nature of Implies

rw: ∀ (r: R), W
 - rw: name of proof
 - ∀ (r: R), W: proposition

If we have a proof of rw, then we actually have a proof of R → W!

In Lean, P → Q is reduced to ∀ (p: P), Q.

-/

/-

Proof by negation: Used to prove ¬P.
Proof by contradiction: Used to prove P.

Let's think about proof by negation.
 - What are you trying to prove?
 - How do you do it?

When you use proof by negation, you are trying to prove ¬P.

How do you prove that P implies false?

You assume that P is true (or that you have a proof of P),
and then you show that it leads to a contradiction/impossibility.

Proof by contradiction starts with an assumption of ¬P.
Goal: Prove P
How:
1. Assume ¬P.
2. Show that this assumption leads to a contradiction.
3. Deduce ¬¬P (via _negation introduction_).
4. Conclude P (via _negation elimination_).

Reminder: negation introduction is that (P → false) → ¬P.

While this looks just like an inverted proof by negation, it
is not the same.

Let's do a (silly) example: Prove 0 = 0 by contradiction.
1. Assume ¬(0 = 0). nx: (0 ≠ 0)
2. Use eq.refl (the reflexive property of equality).
   eq.refl 0 → (0 = 0)
3. We can get a proof x: 0 = 0.

¬(0 = 0) *really* means that 0 = 0 → false.

If we apply nx to x: (nx x) → false.

# How do we find a contradiction?

We derive something that just can't be true.

Assume h: ¬(0 = 0). h is a proof of (0 = 0) → false.
But 0 = 0 is true, so there is a proof of it, let's call it pf.
Now we simply **apply h** to pf (arrow elimination) to derive a
proof of false. By ¬ introduction, this proves ¬¬(0 = 0). Finally
we apply negation elimination to deduce that (0 = 0) is true.

-/

#check @classical.by_contradiction
#check false.elim

example: 0 = 0 :=
begin
-- Sort of like a stack. We apply this to the next theorem, and it
-- is replaced is (¬P → false) → P.
apply classical.by_contradiction,
assume h, -- h: (¬(0 = 0) → false) → P
let k := eq.refl 0, -- Proves that 0 = 0
apply false.elim (h k),
end

/-

Law of the excluded middle:
For any proposition P, either P or ¬P is true.

This is powerful! We can apply classical.em to any proposition
to get a free proof of P ∨ ¬P. From this, we can do case analysis.

Something is either true or false, even if there is no proof of it.
-/

#check classical.em

example: ∀ (P: Prop), ¬¬P → P :=
begin
assume P,
assume nnp,
-- If we assume the law of the excluded middle,
-- then we will be able to prove that negation elimination
-- is valid.
let k: P ∨ ¬P := classical.em P,
sorry -- We'll come back to this.
end

-- If the law of the excluded middle is valid, then negation
-- elimination is valid.
example: ∀ (P: Prop), (P ∨ ¬P) → (¬¬P → P) :=
begin
assume P,
assume em_P,
-- We will use case analysis (equivalent to or elimination).
-- Assume not-not-p.
assume nnp,
cases em_P with p np,
	-- Case P
  -- This is a proof of P
	exact p,
	--------------------------------
	-- Case ¬P
	-- nnp is that if we have a proof of ¬P, then we have a proof of false.
	-- np is a proof of ¬P, so we have a proof of false.
	let f := nnp np,
	apply false.elim f,
end

/-
In constructive logic, we are dealing with proof objects. Therefore, we can't
judge (P ∨ ¬P) to be true unless we have a proof one way or the other.

In predicate logic, the law of the excluded middle is an axiom.
-/

/-

The midterm is about:
 - Being able to identify the inference rules being used
 - You don't have to know how to do everything in Lean

-/

/-
#check: Used to check the type of an expression.
NOT used to check if an expression is valid.
-/

#check 5

#check ℕ
#check bool
#check string

#check ∀ (T: Type) (t: T), t = t

/-

There are two contexts in which variables exist.

There's the logical context, where everything is a Prop.
There's the type context, where everything is a Type.

Prop → 0 = 0 → eq.refl 0
Type → String → "Hello!"

-/

