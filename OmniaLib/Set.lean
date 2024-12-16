import OmniaLib.Order
namespace Set

-- Definition of Set
def set (α : Type u) := α → Prop

def set_of (p : α → Prop) : set α := p

def mem (a : α) (s : set α) : Prop := s a
infix:50 " ∈ " => mem

def empty : set α := fun _ => false

-- Extensionality theorem
theorem ext {A B : set α} (h : ∀ (x : α), x ∈ A ↔ x ∈ B) : A = B := by
apply funext
intro x
apply propext
exact h x

-- Subset relation induces partial order
def subset (A B : set α) : Prop := ∀ (e : α), e ∈ A → e ∈ B
infix:50 " ⊆ " => subset
infix:50 " ⊂ " => Order.strict subset

theorem set_refl (A : set α) : A ⊆ A := by
unfold subset
intro e
exact fun h => h





/-
instance : @Order.reflexive (set α) subset where
refl := set_refl

theorem set_antisymm (A B : set α) : A ⊆ B → B ⊆ A → A = B := by
intro ha hb
apply ext
intro e
unfold subset at ha hb
exact Iff.intro (ha e) (hb e)

instance : @Order.antisymmetric (set α) subset where
antisymm := set_antisymm

theorem set_trans (A B C : set α) : A ⊆ B → B ⊆ C → A ⊆ C := by
intro hab hbc
unfold subset
intro e he
unfold subset at hab hbc
have : e ∈ B := hab e he
exact hbc e this

instance : @Order.transitive (set α) subset where
trans := set_trans

instance : @Order.preorder (set α) subset := Order.preorder.mk
instance : @Order.partial_order (set α) subset := Order.partial_order.mk

theorem foo (α : Type u) (A B C : set α) (h1 : A ⊂ B) (h2 : B ⊂ C) : A ⊂ C := by
exact Order.strict_trans h1 h2
-/
