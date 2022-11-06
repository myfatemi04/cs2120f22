namespace hidden
universe u
constant list : Type u → Type u

namespace list
constant cons   : Π α : Type u, α → list α → list α
constant nil    : Π α : Type u, list α
constant append : Π α : Type u, list α → list α → list α
end list

open hidden.list

variable  α : Type
variable  a : α
variables l1 l2 : list α

-- Here, when constructing a list, we are adding the type parameter α
-- constantly. However, Lean should be able to infer this!
#check nil α
#check cons α a (nil α)
#check append α (cons α a (nil α)) l1
#check append α (append α (cons α a (nil α)) l1) l2

end hidden

namespace hidden2
universe u
constant list : Type u → Type u

namespace list
constant cons   : Π {α : Type u}, α → list α → list α
constant nil    : Π {α : Type u}, list α
constant append : Π {α : Type u}, list α → list α → list α
end list

open hidden2.list

variable  α : Type
variable  a : α
variables l1 l2 : list α

-- Yay, we can infer now.
#check cons a nil
#check append (cons a nil) l1
#check append (append (cons a nil) l1) l2

-- What about this?
#check nil
-- Ah. We specify explicitly
#check @nil ℕ
-- Or...
#check (nil: list ℕ)

end hidden2

namespace hidden3

universe u

section
def ident {α: Type u} (x: α) := x

variables α β: Type u
variables (a: α) (b: β)

#check ident
#check ident a
#check ident b
end

section
-- Here, α is declared as a parameterizable type variable
variable {α: Type u}
variable x: α
def ident' := x
end

-- Variables go out of scope at the end of the section;
-- Definitions stick around.

variables α β: Type u
variables (a: α) (b: β)

#check ident'
#check ident' a
#check ident' b

end hidden3
