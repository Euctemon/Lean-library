import OmniaLib.Set.Defs
namespace Order

-- basic types of relations
class reflexive (α : Type u) (r : α → α → Prop) (S : Set.set α) : Prop where
refl : ∀ (a : α), a ∈ S → r a a

class symmetric (α : Type u) (r : α → α → Prop) (S : Set.set α) : Prop where
symm : ∀ (a b : α), a ∈ S → b ∈ S → r a b → r b a

class antisymmetric (α : Type u) (r : α → α → Prop) (S : Set.set α) : Prop where
antisymm : ∀ (a b : α), a ∈ S → b ∈ S → r a b → r b a → a = b

class transitive (α : Type u) (r : α → α → Prop) (S : Set.set α) : Prop where
trans : ∀ (a b c : α), a ∈ S → b ∈ S → c ∈ S →  r a b → r b c → r a c

class total (α : Type u) (r : α → α → Prop) (S : Set.set α) : Prop where
total : ∀ (a b : α), a ∈ S → b ∈ S → r a b ∨ r b a


-- basic structures studied in order theory
class preorder (α : Type u) (r : α → α → Prop) (S : Set.set α)
  extends reflexive α r S, transitive α r S : Prop

class equivalence (α : Type u) (r : α → α → Prop) (S : Set.set α)
  extends preorder α r S, symmetric α r S : Prop

class partial_order (α : Type u) (r : α → α → Prop) (S : Set.set α)
  extends preorder α r S, antisymmetric α r S : Prop

class linear_order (α : Type u) (r : α → α → Prop) (S : Set.set α)
  extends partial_order α r S, total α r S : Prop
