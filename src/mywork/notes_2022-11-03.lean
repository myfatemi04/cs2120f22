/- From Sets      : collections of objects
     to Relations : collections of pairs -/

-- Note: This is NOT a function
def negation: bool → bool → Prop
	| tt ff := true
	| ff tt := true
	| _ _ := false 

-- ... but this IS a function
#eval bnot tt

example: ¬ negation tt tt :=
begin
-- * Use proof by contradiction
assume h,
-- * It's NOT the case that (tt tt) is in this relation
-- You can use cases like this because it's done automatically
cases h,
end

example: ∀ (b1 b2), negation b1 b2 ↔ bnot b1 = b2 :=
begin
assume b1 b2,
-- * Bi-implication. We can use "split"
split,
assume h, -- or "intro h"
cases b1,
-- * First half of case analysis b1
cases b2,
-- ** Case f f
cases h,
-- ** Case t f
exact rfl,
-- * Second half of case analysis b1
cases b2,
-- ** Case f t
exact rfl,
-- ** Case t t
cases h,

-- Now, time for the backwards direction.
assume h,
cases b1, -- Looks at all possible values of b1
-- * b1 = ff
cases b2,
cases h,
-- We are left to prove "negation ff tt"
unfold negation,
-- * b1 = tt
cases b2,
unfold negation,
cases h,
end

inductive bit
| zero
| one

-- A binary relation is a combination of pairs of these values

-- This one is more like a function
def bit_flip: bit → bit
| bit.zero := bit.one
| bit.one := bit.zero

-- This one is more like a set
def bool_to_bit_relation: bool → bit → Prop
| tt bit.one := true
| ff bit.zero := true
| _ _ := false

-- Crosses between two sets yields all possible combinations
-- I think I learned about this in prob theory? It's why
-- R^3 = R x R x R = all combinations of (x, y, z)

-- Let my relation R ⊆ (S ⨯ A) be a relation on S, A.
-- There are four pairs of values in S ⨯ A.
-- Therefore, there are 2^4 possible relations between
-- S and A.
