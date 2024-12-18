namespace Set

-- Definition of Set
def set (α : Type u) := α → Prop

def set_of (p : α → Prop) : set α := p

def mem (a : α) (s : set α) : Prop := s a
infix:75 " ∈ " => mem

-- Extensionality theorem
theorem ext {A B : set α} (h : ∀ (x : α), x ∈ A ↔ x ∈ B) : A = B := by
apply funext
intro x
apply propext
exact h x

def empty : set α := fun _ => false

def univ : set α := fun _ => true

def subset (A B : set α) : Prop := ∀ (a : α), a ∈ A → a ∈ B

def union (A B : set α) : set α := set_of (fun e => e ∈ A ∨ e ∈ B)

def inter (A B : set α) : set α := set_of (fun e => e ∈ A ∧ e ∈ B)

def power_set (A : set α) : set (set α) := set_of (fun S => subset S A)



theorem subset_of_empty {A : set α} : subset A empty → A = empty := by
intro h
apply ext
intro e
have left : e ∈ A → e ∈ empty := fun he => h e he
have right : e ∈ empty → e ∈ A := by
  intro he
  simp only [mem, empty] at he
  rw [Bool.false_eq_true] at he
  exact False.elim he
exact Iff.intro left right

/-
theorem subset_of_empty' {A : set α} :  ¬ A = empty → ¬ subset A empty := by
intro h hn
exact h (subset_of_empty hn)

def singleton (a : α) : set α := set_of (fun e => e = a)


theorem singleton_non (a : α) : a ∈ A → ¬ (subset (singleton a) A) = empty := sorry


theorem foo (A : set α) : ¬ A = empty → ¬ power_set A = empty := by
intro h hp
simp only [power_set, set_of] at hp
apply subset_of_empty' h
simp [subset]
intro a ha
simp [mem, empty]
-/
