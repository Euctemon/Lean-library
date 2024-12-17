namespace Order

-- basic types of relations
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


-- important constants and functions on relation
class has_bot (α : Type u) (r : α → α → Prop) where
bot : α
is_bot : ∀ (a : α), r bot a

class has_meets (α : Type u) (r : α → α → Prop) where
meet : α → α → α
meet_left : ∀ (a b : α), r (meet a b) a
meet_right : ∀ (a b : α), r (meet a b) b

class has_top (α : Type u) (r : α → α → Prop) where
top : α
is_top : ∀ (a : α), r a top

class has_joins (α : Type u) (r : α → α → Prop) where
join : α → α → α
join_left : ∀ (a b : α), r a (join a b)
join_right : ∀ (a b : α), r b (join a b)


-- more complex relations
class preorder (α : Type u) (r : α → α → Prop)
  extends reflexive α r, transitive α r : Prop

class equivalence (α : Type u) (r : α → α → Prop)
  extends preorder α r, symmetric α r : Prop

class partial_order (α : Type u) (r : α → α → Prop)
  extends preorder α r, antisymmetric α r : Prop

class linear_order (α : Type u) (r : α → α → Prop)
  extends partial_order α r, total α r : Prop

class lattice  (α : Type u) (r : α → α → Prop)
  extends partial_order α r, has_meets α r, has_joins α r
