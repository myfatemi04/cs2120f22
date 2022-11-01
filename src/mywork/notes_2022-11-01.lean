import data.set

def isEven(n: ℕ) := n % 2 == 0

def evens: set ℕ := {n: ℕ | isEven n}

#reduce evens 3
#reduce evens 4

def xyz: set ℕ := {1, 2, 3}

#reduce xyz 4

def strings5 := {s: string | s.length = 5}

def set135: set ℕ := {1, 3, 5}

example: 4 ∉ set135 :=
begin
assume h,
cases h,
cases h,
cases h,
cases h,
cases h,
end

example: 4 ∉ set135 :=
begin
assume h,
repeat {cases h},
end

-- What is the predicate that defines the empty set? --
-- false

def emptyset: set ℕ := {n: ℕ | false}
def universalset: set ℕ := {n: ℕ | true}

-- We can define a polymorphic concept of the empty set --
-- This takes a Type parameter
def generate_emptyset(T: Type) := {t: T | false}

example: ∀ (n: ℕ), n ∉ (∅: set ℕ) :=
begin
-- Take some arbitrary but specific ℕ
assume a,
-- a ∉ ∅ is the same as (a ∈ ∅) → false, so we assume a ∈ ∅ 
assume h,
cases h,
end

example: 7 ∈ universalset :=
begin
-- Applying the universal set predicate to '7' simply returns 'true'
-- `trivial` is a tactic which proves true
trivial,
end

def set_intersection {α: Type} (S T: set α) (a: α):
	(a ∈ S ∧ a ∈ T) ↔ (a ∈ S ∩ T) :=
begin
split,
assume h,
exact h,
assume h,
exact h,
end

def set_union {α: Type} (S T: set α) (a: α):
	(a ∈ S) ∨ (a ∈ T) ↔ a ∈ (S ∪ T) :=
begin
split,
assume h,
exact h,
assume h,
exact h,
end

def set_complement {α: Type} (S: set α) (a: α):
	a ∉ S ↔ a ∈ Sᶜ :=
begin
split,
assume h,
exact h,
assume h,
exact h,
end

def set_subset {α: Type} (S T: set α) (a: α):
	(a ∈ S) → (a ∈ T) ↔ (S ⊂ T) :=
begin
split,
assume st,
exact st,
assume h,
assume a,
assume as,
exact (h as),
end

def set_difference {α: Type} {S T: set α} (a: α):
	(a ∈ S ∧ a ∉ T) ↔ a ∈ S \ T :=
begin
split,
assume h,
exact h,
assume h,
exact h,
end
