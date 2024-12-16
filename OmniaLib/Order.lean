namespace Order

/-
Mathlib.Order.Defs.Unbundled
-/

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

theorem strict_trans [pr : partial_order α r] :
  ∀ (a b c : α), strict r a b → strict r b c → strict r a c := by
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


structure order_hom (r : α → α → Prop) (s : β → β → Prop) where
apply : α → β
respects : ∀ (a b : α), r a b → s (apply a) (apply b)

namespace hom_rel
variable {r : α → α → Prop}
variable {s : β → β → Prop}

def rel (f g : order_hom r s) : Prop :=
  ∀ (a b : α), r a b → s (f.apply a) (g.apply b)

theorem refl (f : order_hom r s) : rel f f := by
intro a b hab
exact f.respects a b hab

instance : reflexive (order_hom r s) rel where
refl := refl

theorem trans [pr : reflexive α r] [ps : transitive β s]  (f g h : order_hom r s) :
  rel f g → rel g h → rel f h := by
intro h1 h2 a b rab
have h3 := h1 a a (pr.refl a)
have h4 := h2 a b rab
exact ps.trans (f.apply a) (g.apply a) (h.apply b) h3 h4

instance [reflexive α r] [transitive β s] : transitive (order_hom r s) rel where
trans := hom_rel.trans

instance [reflexive α r] [preorder β s] : preorder (order_hom r s) rel := preorder.mk


theorem antisymm [pr : reflexive α r] [ps : antisymmetric β s]  (f g : order_hom r s) :
  rel f g → rel g f → f = g := by
intro h1 h2
cases f with
| mk f f_resp => cases g with
    | mk g g_rel =>
      have : f = g := by
        apply funext
        intro a
        have h3 : s (f a) (g a) := h1 a a (pr.refl a)
        have h4 : s (g a) (f a) := h2 a a (pr.refl a)
        exact ps.antisymm (f a) (g a) h3 h4
      simp [rel] at h1 h2
      simp [this]

instance [reflexive α r] [antisymmetric β s] : antisymmetric (order_hom r s) rel where
antisymm := hom_rel.antisymm

instance [reflexive α r] [partial_order β s] : partial_order (order_hom r s) rel := partial_order.mk

end hom_rel
