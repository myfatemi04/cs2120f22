example
	(Person: Type)
	(Loves: Person → Person → Prop)
	:
	(∃ (p: Person), ∀(q: Person), Loves p q) →
	(∀ (p: Person), ∃(q: Person), Loves q p)
	:=
begin
	assume p_loves_everyone,
	assume p,
	cases p_loves_everyone with p' p'_loves_everyone,
	-- exists introduction
	-- If you have a witness and a proof of the witness, you can use both of them.
	existsi p',
	-- Now, we need to prove that p' loves p.
	-- To do this, we apply p'_loves_everyone to p.
	exact p'_loves_everyone p,
end

-- ∃ elimination

#check @exists.elim

def exists_elim :=
	∀ {X: Type}
		{P: X → Prop}
		{Y: Prop},
		(∃ (x: X), P x) →
		(∀ (x: X), P x → Y) →
		Y

example: exists_elim :=
begin
unfold exists_elim,
assume X P,
assume Y,
assume exists_X_with_property_P,
assume if_any_X_has_P_then_Y,
cases exists_X_with_property_P with w w_has_P, -- w is the witness
-- There's some existing object out there called w that has the
-- property P.
exact if_any_X_has_P_then_Y w w_has_P,
-- Applying if_any_X_has_P_then_Y to w (an X), then we get a proof
-- that a proof of P x → Y.
end

-- Creating identity functions
def id_nat: ℕ → ℕ | n := n 
def id_T (T: Type): T → T | t := t
-- What does 'T t' mean?
def id_T': ∀ (T: Type), T → T | T t := t

-- I can declare an argument to be an implicit argument

def id_T'': ∀ (T: Type), T → T | T t := t

#eval id_nat 3
#eval id_T nat 3
#eval id_T' nat 3

-- If you use an '@' sign before you use a polymorphic function, it turns
-- off the implicit arguments and allows you to use all of them specifically.

def id_T2 {T: Type}: T → T | t := t
#check id_T2 -- ?M_1 → ?M_1 
-- This results in the meta-variable ?M_1
#check @id_T2 -- Π {T: Type}, T → T 
-- The Π is like a for-all. It's used for computational symbols rather
-- than logical symbols.

-- Predicate logic: The syntax includes function symbols.
-- For example: MotherOf(John) = Mary --- MotherOf is a function symbol
-- Lean has a mechanism that lets us write logical expressions about objects.

namespace my_types

-- This type has no values
inductive empty: Type

-- This has one possible value: star
inductive unit: Type
| star

-- Define a function that takes a unit and returns a unit.
-- Then, apply that function to some value.

def x: unit := unit.star
def id_unit: unit → unit | u := u

open unit
#eval id_unit x

inductive my_bool: Type
| true__
| false__

open my_bool

def my_bool_not: my_bool → my_bool
| true__ := false__
| false__ := true__

#eval my_bool_not true__
#eval my_bool_not false__

end my_types
