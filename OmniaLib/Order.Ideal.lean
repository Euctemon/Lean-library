import OmniaLib.Set
namespace Ideal

class lower_set (α : Type u) (r : α → α → Prop) (S : Set.set α) where
 foo : ∀ a b, a ∈ S → r a b → b ∈ S

class directed_set (α : Type u) (r : α → α → Prop) where
meet : α → α → α
left : ∀ (a b : α), r (meet a b) a
right : ∀ (a b : α), r (meet a b) b

structure ideal (α : Type u) (r : α → α → Prop) (S : Set.set α)
  extends directed_set α r, lower_set α r S where
nonempty : ¬ S = empty
