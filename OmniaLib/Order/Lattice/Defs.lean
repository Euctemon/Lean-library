import OmniaLib.Order.Relation.Defs
import OmniaLib.Set.Defs

class has_bot (α : Type u) (r : α → α → Prop) (S : Set.set α) where
bot : α
bot_mem : bot ∈ S
bot_def : ∀ (a : α), a ∈ S → r bot a

class has_top (α : Type u) (r : α → α → Prop) (S : Set.set α) where
top : α
top_mem : top ∈ S
top_def : ∀ (a : α), a ∈ S → r a top

class has_inf (α : Type u) (r : α → α → Prop) (S : Set.set α) where
inf : α → α → α
inf_mem : ∀ (a b : α), a ∈ S → b ∈ S → inf a b ∈ S
inf_left : ∀ (a b : α), r (inf a b) a
inf_right : ∀ (a b : α), r (inf a b) b
inf_higher : ∀ (a b c : α), r c a → r c b → r c (inf a b)


/- class has_inf (α : Type u) (r : α → α → Prop) where
inf : α → α → α
inf_left : ∀ (a b : α), r (inf a b) a
inf_right : ∀ (a b : α), r (inf a b) b
inf_higher : ∀ (a b c : α), r c a → r c b → r c (inf a b)

class has_top (α : Type u) (r : α → α → Prop) where
top : α
is_top : ∀ (a : α), r a top

class has_sup (α : Type u) (r : α → α → Prop) where
sup : α → α → α
sup_left : ∀ (a b : α), r a (sup a b)
sup_right : ∀ (a b : α), r b (sup a b)
sup_lower : ∀ (a b c : α), r a c → r b c → r (sup a b) c -/
