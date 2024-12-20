import OmniaLib.Set.Defs
namespace Order
open Set

-- basic types of relations
class reflexive (α : Type u) (r : α → α → Prop) (S : set α) : Prop where
refl : ∀ (a : α), a ∈ S → r a a

class symmetric (α : Type u) (r : α → α → Prop) (S : set α) : Prop where
symm : ∀ (a b : α), a ∈ S → b ∈ S → r a b → r b a

class antisymmetric (α : Type u) (r : α → α → Prop) (S : set α) : Prop where
antisymm : ∀ (a b : α), a ∈ S → b ∈ S → r a b → r b a → a = b

class transitive (α : Type u) (r : α → α → Prop) (S : set α) : Prop where
trans : ∀ (a b c : α), a ∈ S → b ∈ S → c ∈ S →  r a b → r b c → r a c

class total (α : Type u) (r : α → α → Prop) (S : set α) : Prop where
total : ∀ (a b : α), a ∈ S → b ∈ S → r a b ∨ r b a

class has_bot (α : Type u) (r : α → α → Prop) (S : set α) where
bot : α
bot_mem : bot ∈ S
bot_def : ∀ (a : α), a ∈ S → r bot a

class has_top (α : Type u) (r : α → α → Prop) (S : set α) : Type u where
top : α
top_mem : top ∈ S
top_def : ∀ (a : α), a ∈ S → r a top

class has_inf (α : Type u) (r : α → α → Prop) (S : set α) : Type u where
inf : α → α → α
inf_mem : ∀ (a b : α), a ∈ S → b ∈ S → inf a b ∈ S
inf_left : ∀ (a b : α), r (inf a b) a
inf_right : ∀ (a b : α), r (inf a b) b
inf_higher : ∀ (a b c : α), r c a → r c b → r c (inf a b)

class has_sup (α : Type u) (r : α → α → Prop) (S : set α) : Type u where
sup : α → α → α
sup_mem : ∀ (a b : α), a ∈ S → b ∈ S → sup a b ∈ S
sup_left : ∀ (a b : α), r a (sup a b)
sup_right : ∀ (a b : α), r b (sup a b)
sup_lower : ∀ (a b c : α), r a c → r b c → r (sup a b) c

-- basic structures studied in order theory
class preorder (α : Type u) (r : α → α → Prop) (S : set α)
  extends reflexive α r S, transitive α r S : Prop

class equivalence (α : Type u) (r : α → α → Prop) (S : set α)
  extends preorder α r S, symmetric α r S : Prop

class partial_order (α : Type u) (r : α → α → Prop) (S : set α)
  extends preorder α r S, antisymmetric α r S : Prop

class linear_order (α : Type u) (r : α → α → Prop) (S : set α)
  extends partial_order α r S, total α r S : Prop

class lattice (α : Type u) (r : α → α → Prop) (S : set α)
  extends partial_order α r S, has_inf α r S, has_sup α r S : Type u
