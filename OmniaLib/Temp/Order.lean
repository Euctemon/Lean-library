/- import OmniaLib.Set.Defs
import OmniaLib.Order.Defs
namespace Set

theorem subset.refl (A : set α) : subset A A := fun _ h => h

instance : Order.reflexive (set α) subset where
refl := subset.refl

theorem subset.antisymm (A B : set α) : subset A B → subset B A → A = B := by
intro ha hb
apply setext
intro e
unfold subset at ha hb
exact Iff.intro (ha e) (hb e)

instance : Order.antisymmetric (set α) subset where
antisymm := subset.antisymm

theorem subset.trans (A B C : set α) : subset A B → subset B C → subset A C := by
intro hab hbc
unfold subset
intro e he
unfold subset at hab hbc
have : e ∈ B := hab e he
exact hbc e this

instance : Order.transitive (set α) subset where
trans := subset.trans

instance : Order.preorder (set α) subset := Order.preorder.mk
instance : Order.partial_order (set α) subset := Order.partial_order.mk

theorem subset.left_meets (A B : set α) : subset (inter A B) A := fun _ h => h.left

theorem subset.right_meets (A B : set α) : subset (inter A B) B := fun _ h => h.right

instance : Order.has_meets (set α) subset where
meet := inter
meet_left := subset.left_meets
meet_right := subset.right_meets

theorem subset.left_joins (A B : set α) : subset A (union A B) :=
  fun e h => Or.intro_left (e ∈ B) h

theorem subset.right_joins (A B : set α) : subset B (union A B) :=
  fun e h => Or.intro_right (e ∈ A) h

instance : Order.has_joins (set α) subset where
join := union
join_left := subset.left_joins
join_right := subset.right_joins

instance : Order.lattice (set α) subset := Order.lattice.mk

theorem empty_is_subset (A : set α) :  subset empty A := by
intro e he
simp only [mem, empty, Bool.false_eq_true] at he

instance : Order.has_bot (set α) subset where
bot := empty
is_bot := empty_is_subset
 -/
