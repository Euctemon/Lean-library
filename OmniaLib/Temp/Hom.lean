import OmniaLib.Order.Defs

namespace Order
variable {α : Type u}
variable {β : Type v}

structure hom (r : α → α → Prop) (s : β → β → Prop) where
apply : α → β
respects : ∀ (a b : α), r a b → s (apply a) (apply b)


variable {r : α → α → Prop}
variable {s : β → β → Prop}

def rel (f g : hom r s) : Prop :=
  ∀ (a b : α), r a b → s (f.apply a) (g.apply b)

theorem refl (f : hom r s) : rel f f := by
intro a b hab
exact f.respects a b hab

instance : reflexive (hom r s) rel where
refl := refl

theorem trans [pr : reflexive α r] [ps : transitive β s]  (f g h : hom r s) :
  rel f g → rel g h → rel f h := by
intro h1 h2 a b rab
have h3 := h1 a a (pr.refl a)
have h4 := h2 a b rab
exact ps.trans (f.apply a) (g.apply a) (h.apply b) h3 h4

instance [reflexive α r] [transitive β s] : transitive (hom r s) rel where
trans := trans

instance [reflexive α r] [preorder β s] : preorder (hom r s) rel := preorder.mk

theorem antisymm [pr : reflexive α r] [ps : antisymmetric β s]  (f g : hom r s) :
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

instance [reflexive α r] [antisymmetric β s] : antisymmetric (hom r s) rel where
antisymm := antisymm

instance [reflexive α r] [partial_order β s] : partial_order (hom r s) rel := partial_order.mk
