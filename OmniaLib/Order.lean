namespace Order

-- some implicit type variables
variable {α : Type u}
variable {β : Type v}

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

class equivalence (α : Type u) (r : α → α → Prop)
  extends preorder α r, symmetric α r : Prop

class partial_order (α : Type u) (r : α → α → Prop)
  extends preorder α r, antisymmetric α r : Prop

class linear_order (α : Type u) (r : α → α → Prop)
  extends partial_order α r, total α r : Prop


-- strict part of relation
def strict (r : α → α → Prop) (a b : α) : Prop := r a b ∧ ¬ a = b

theorem strict_not_symm [pr : partial_order α r] : ∀ (a b : α), strict r a b → ¬ r b a := by
intro a b h rba
have : a = b := pr.antisymm a b h.left rba
exact h.right this

theorem strict_trans [pr : partial_order α r] : ∀ (a b c : α), strict r a b → strict r b c → strict r a c := by
intro a b c rab rbc
apply And.intro
case left =>
  exact pr.trans a b c rab.left rbc.left
case right =>
  intro eq_ac
  apply eq_ac ▸ rab.right
  have : r c b := eq_ac ▸ rab.left
  have : b = c := pr.antisymm b c rbc.left this
  exact Eq.symm this




def hom_order (r : α → α → Prop) (s : β → β → Prop) (f : α → β) : Prop := ∀ (a b : α), r a b → s (f a) (f b)

def hom_rel (r : α → α → Prop) (s : β → β → Prop) (f g : α → β) : Prop := ∀ (a b : α), r a b → s (f a) (g b)

theorem hom_rel.refl (f : α → β) : hom_order r s f → hom_rel r s f f := by
intro h
unfold hom_rel
intro a b rab
exact h a b rab

theorem hom_rel.antisymm (f g : α → β) [pr : reflexive α r] [ps : antisymmetric β s]
 : hom_rel r s f g → hom_rel r s g f → f = g := by
intro h1 h2
apply funext
intro a
have sfg : s (f a) (g a) := h1 a a (pr.refl a)
have sgf : s (g a) (f a) := h2 a a (pr.refl a)
exact ps.antisymm (f a) (g a) sfg sgf

theorem hom_rel.trans (f g j : α → β) [pr : reflexive α r] [ps : transitive β s]
  : hom_order r s j → hom_rel r s f g → hom_rel r s g j → hom_rel r s f j := by
intro h1 h2 h3
intro a b rab
have sfg := h2 a a (pr.refl a)
have sgj := h3 a a (pr.refl a)
have foo := ps.trans (f a) (g a) (j a) sfg sgj
have doo := h1 a b rab
exact ps.trans (f a) (j a) (j b) foo doo



/-
https://en.wikipedia.org/wiki/Galois_connection

-/
