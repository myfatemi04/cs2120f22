/-

# Quantifiers and Equality

Unary predicate on α: α → Prop

## Quantifiers
Universal quantifier: ∀ x: α, p x

The forall introduction rule states that given a proof of p x,
in a context where x (x: α) is arbitrary, we obtain a proof
∀ x: α, p x. This is also the most straightforward way to create
the proof.

The forall elimination rule states that given a proof
∀ x: α, p x and any term t: α, we obtain a proof of p t.

-/

-- Define a type and two predicates
variables (α: Type*) (p q: α → Prop)

example: (∀ x: α, p x ∧ q x) → ∀ y: α, p y :=
begin
assume h,
assume y,
exact (h y).left,
end

variable r: α → α → Prop
variable trans_r': ∀ x y z, r x y → r y z → r x z

variables a b c: α 
variables (hab: r a b) (hbc: r b c)

#check trans_r' a b c hab hbc

variable refl_r: ∀ x, r x x
variable symm_r: ∀ {x y}, r x y → r y x
variable trans_r: ∀ {x y z}, r x y → r y z → r x z

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
  r a d :=
trans_r (trans_r hab (symm_r hcb)) hcd

-- ## Equality

#check eq.refl
#check eq.symm
#check eq.trans

universe u
#check @eq.refl.{u}
#check @eq.symm.{u}
#check @eq.trans.{u}

variables (d: α) (hab': a = b) (hcb': c = b) (hcd': c = d)
example: a = d := eq.trans (eq.trans hab' (eq.symm hcb')) hcd'

-- Why is reflexivity powerful?
-- Sometimes nontrivial identities can be proved by reflexivity
-- because terms with a common reduct are the same.

variable (β: Type*)

example (f: α → β) (a: α): (λ x, f x) a = f a := eq.refl _
example (a: α) (b: α): (a, b).1 = a := eq.refl _
example: 2 + 3 = 5 := eq.refl _

-- We can also just write `rfl` instead of `eq.refl _`

-- Equality has the property that every assertion respects the
-- equivalence (we can substitute equal expressions into any
-- situation without changing the truth value, even if they are
-- technically different variables)

example (α: Type*) (a b: α) (p: α → Prop)
	(h1: a = b) (h2: p a): p b :=
	eq.subst h1 h2

example (α: Type*) (a b: α) (p: α → Prop)
	(h1: a = b) (h2: p a): p b :=
	h1 ▸ h2 -- Plug in h1 to h2

-- Some other things you can do are `congr_arg`, which replaces
-- the argument of a function, and `congr_fun`, which replaces the function
-- `congr` can replace both at once

variables f g: α → ℕ
variable h1: a = b
variable h2: f = g

-- Put the equality hypothesis in the place that you
-- expect the term to go in a normal "applies" thing
example: f a = f b := congr_arg f h1
example: f a = g a := congr_fun h2 a
example: f a = g b := congr h2 h1


