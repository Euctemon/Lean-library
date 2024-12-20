import OmniaLib.Set.Defs

namespace Set




-- predicate for a finite set
inductive finite : (set α → Prop) where
| empty : finite empty
| insert : (a : α) → (A : set α) → finite A → finite (insert a A)


theorem union.finite_if_finite (A B : set α) : finite A → finite B → finite (union A B) := by
intro ha hb
induction ha with
| empty => sorry
| insert c C fin finU => sorry
