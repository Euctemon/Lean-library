import OmniaLib.Order.Relation.Basic

namespace Set

-- predicate for a finite set
inductive finite : (set α → Prop) where
| empty : finite empty
| insert : (a : α) → (A : set α) → finite A → finite (insert a A)

theorem union.finite_if_finite (A B : set α) : finite A → finite B → finite (union A B) := by
intro ha hb
induction ha with
| empty =>
  have : union empty B = B := by
    apply setext
    intro a
    apply Iff.intro
    intro ha
    apply Or.elim ha
    intro he
    simp [mem, empty] at he
    exact fun a => a
  rw [this]
  exact hb
| insert c C hc hcc => sorry
