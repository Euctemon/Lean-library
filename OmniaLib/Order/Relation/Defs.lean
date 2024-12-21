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

class bot (α : Type u) where
bot : α
notation "⊥" => bot.bot

class top (α : Type u) where
top : α
notation "⊤" => top.top

class inf (α : Type u) where
inf : α → α → α
infix:80 " ⊓ " => inf.inf

class sup (α : Type u) where
sup : α → α → α
infix:80 " ⊔ " => sup.sup

class has_bot (α : Type u) (r : α → α → Prop) (S : set α) extends bot α where
bot_mem : ⊥ ∈ S
bot_def : ∀ (a : α), a ∈ S → r ⊥ a

class has_top (α : Type u) (r : α → α → Prop) (S : set α) extends top α where
top_mem : ⊤ ∈ S
top_def : ∀ (a : α), a ∈ S → r a ⊤

class has_inf (α : Type u) (r : α → α → Prop) (S : set α) extends inf α where
inf_mem : ∀ (a b : α), a ∈ S → b ∈ S → a ⊓ b ∈ S
inf_left : ∀ (a b : α), a ∈ S → b ∈ S → r (a ⊓ b) a
inf_right : ∀ (a b : α), a ∈ S → b ∈ S → r (a ⊓ b) b
inf_higher : ∀ (a b c : α), a ∈ S → b ∈ S → c ∈ S → r c a → r c b → r c (a ⊓ b)

class has_sup (α : Type u) (r : α → α → Prop) (S : set α) extends sup α where
sup_mem : ∀ (a b : α), a ∈ S → b ∈ S → a ⊔ b ∈ S
sup_left : ∀ (a b : α), a ∈ S → b ∈ S → r a (a ⊔ b)
sup_right : ∀ (a b : α), a ∈ S → b ∈ S → r b (a ⊔ b)
sup_lower : ∀ (a b c : α), a ∈ S → b ∈ S → c ∈ S → r a c → r b c → r (a ⊔ b) c

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

class bounded_lattice (α : Type u) (r : α → α → Prop) (S : set α)
  extends lattice α r S, has_bot α r S, has_top α r S
