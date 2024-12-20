namespace Set

-- definition of a set
def set (α : Type u) := α → Prop

def set_of (p : α → Prop) : set α := p

def mem (a : α) (s : set α) : Prop := s a
infix:75 " ∈ " => mem

-- theorem about set extensionality
theorem setext {A B : set α} (h : ∀ (x : α), x ∈ A ↔ x ∈ B) : A = B := by
apply funext
intro x
apply propext
exact h x

-- basic set operations
def empty : set α := fun _ => false

def univ : set α := fun _ => true

def subset (A B : set α) : Prop := ∀ (a : α), a ∈ A → a ∈ B

def union (A B : set α) : set α := set_of (fun e => e ∈ A ∨ e ∈ B)

def inter (A B : set α) : set α := set_of (fun e => e ∈ A ∧ e ∈ B)

def singleton (a : α) : set α := set_of (fun e => e = a)

def power_set (A : set α) : set (set α) := set_of (fun S => subset S A)

def insert (a : α) (A : set α) : set α := set_of (fun e => e = a ∨ e ∈ A)
