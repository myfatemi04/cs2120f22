constant α: Type _
#check α

constant β: Type*
#check β

#check fun x: nat, x + 5

def foo: (ℕ → ℕ) → ℕ := λ f, f 0
#print foo
def double(x: ℕ) := x + x
def square(x: ℕ) := x * x
def compose(α β γ: Type*) (g: β → γ) (f: α → β) (x: α) := g (f x)

-- Dependent Types --
-- https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html
-- Π indicates a type that is dependent on other types. In other words,
-- a type parameter.
namespace hidden

universe u

namespace list
-- Type declarations for list
constant list: Type u → Type u
-- Inserts new element at head of list
constant cons: Π α: Type u, α → list α → list α
constant nil: Π α: Type u, list α
-- Returns the first element
constant head: Π α: Type u, list α → α
-- Returns a list containing the rest of the elements
constant tail: Π α: Type u, list α → list α
-- Returns a list formed from two other lists
constant append: Π α: Type u, list α → list α → list α
end list

end hidden

-- You can do similar things with vectors --
namespace hidden

universe u
constant vec: Type u → ℕ → Type u

namespace vec
-- Note that in 'varname: (...)', the '(...)' declares the _type_ of
-- the variable; it does not assign a definition.
constant empty: Π α: Type u, vec α 0
constant cons: Π (α: Type u) (n: ℕ), α → vec α n → vec α (n + 1)
constant append: Π (α: Type u) (n m: ℕ), vec α m → vec α n → vec α (n + m) 
end vec

end hidden

-- # Sigma types
-- Σ x: α, β x
-- Also known as _dependent products_
-- Just as Π x: α, β x generalizes α → β,
-- Σ x: α, β x generalizes α × β in the same way
variable α: Type
variable β: α → Type
variable a: α
variable b: β a

#check sigma.mk a b
#check (sigma.mk a b).1 -- First
#check (sigma.mk a b).2 -- Second
