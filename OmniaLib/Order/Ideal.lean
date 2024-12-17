import OmniaLib.Set.Defs
import OmniaLib.Order.Defs

namespace Order
variable {α : Type u}

structure lower_set (r : α → α → Prop) (S : Set.set α) where
lower : ∀ (a b : α), r a b → a ∈ S → b ∈ S

structure directed_set (r : α → α → Prop) (S : Set.set α)
  extends has_meets α r where
directed : ∀ (a b : α), meet a b ∈ S

structure ideal (r : α → α → Prop) (S : Set.set α)
  extends directed_set r S, lower_set r S where
nonempty : ¬ S = Set.empty
