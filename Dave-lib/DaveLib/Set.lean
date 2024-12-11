namespace Set

-- For sets we will use the type variable α and set it to universe u
variable {α : Type u}


-- Definition of Set
def Set (ω : Type u) := ω → Prop

def setOf (p : α → Prop) : Set α := p
def mem (a : α) (s : Set α) : Prop := s a
infix:50 " ∈ " => mem

-- Extensionality theorem
theorem ext {A B : Set α} (h : ∀ (x : α), x ∈ A ↔ x ∈ B) : A = B := by
apply funext
intro x
apply propext
exact h x

-- Few important definitions
def union (A B : Set α) : Set α := setOf (fun e => e ∈ A ∨ e ∈ B)
def inter (A B : Set α) : Set α := setOf (fun e => e ∈ A ∧ e ∈ B)
def subset (A B : Set α) := ∀ (e : α), e ∈ A → e ∈ B

def family_union (F : Set (Set α)) : Set α := setOf (fun e => ∃ A, A ∈ F ∧ e ∈ A)
def family_inter (F : Set (Set α)) : Set α := setOf (fun e => ∀ A, A ∈ F ∧ e ∈ A)

-- We define the insert operation and singleton
def insert (a : α) (A : Set α) : Set α := setOf (fun e => e = a ∨ e ∈ A)

-- Definition of finite sets
inductive finite : (Set α → Prop) where
| empty : finite empty
| insert : (a : α) → (A : Set α) → finite A → finite (insert a A)
