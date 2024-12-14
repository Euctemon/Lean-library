namespace Order

universe u

-- building blocks for more complex relations
class reflexive (α : Type u) (r : α → α → Prop) : Prop where
refl : ∀ (a : α), r a a

class symmetric (α : Type u) (r : α → α → Prop) : Prop where
symm : ∀ (a b : α), r a b → r b a

class antisymmetric (α : Type u) (r : α → α → Prop) : Prop where
antisymm : ∀ (a b : α), r a b → r b a → a = b

class transitive (α : Type u) (r : α → α → Prop) : Prop where
trans : ∀ (a b c : α), r a b → r b c → r a c

class total (α : Type u) (r : α → α → Prop) : Prop where
total : ∀ (a b : α), r a b ∨ r b a


-- more complex relations
class preorder (α : Type u) (r : α → α → Prop)
  extends reflexive α r, transitive α r : Prop

class equivalence  (α : Type u) (r : α → α → Prop)
  extends preorder α r, symmetric α r : Prop

class partial_order (α : Type u) (r : α → α → Prop)
  extends preorder α r, antisymmetric α r : Prop

class linear_order (α : Type u) (r : α → α → Prop)
  extends partial_order α r, total α r : Prop


-- strict part of relation
def strict_of {α : Type u} (r : α → α → Prop) := fun a b => r a b ∧ ¬ a = b
postfix:max "°" => strict_of

theorem foo [p : partial_order α r] (a b : α) (h : r° a b) : ¬ r b a := by
intro rab
unfold strict_of at h
have heq : a = b := p.antisymm a b h.left rab
exact h.right heq

theorem strict_trans [p : partial_order α r] (a b c : α) (h1 : r° a b) (h2 : r° b c) : r° a c := by
unfold strict_of
unfold strict_of at h1 h2
apply And.intro
case left =>
  exact p.trans a b c h1.left h2.left
case right =>
  intro hac
  have hbc : ¬ c = b := hac ▸ h1.right
  apply hbc
  have rcb := hac ▸ h1.left
  have := p.antisymm b c h2.left rcb
  exact Eq.symm this
