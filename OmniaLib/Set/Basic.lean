import OmniaLib.Set.Defs
import OmniaLib.Order.Relation.Defs

/-
Subset relation induced a partial order on any set of sets 𝔸. The set 𝔸 might not have a bottom element,
top element, infima or suprema. If we suppose that 𝔸 is the power set of some set A, then we can prove
that subset relation together with intersection and union induces a lattice structure on 𝔸.
-/

open Set Order
variable {α : Type u}

-- partial order
instance subset.is_refl : reflexive (set α) subset 𝔸 where
refl := fun _ _ _ h => h

instance subset.is_antisymm : antisymmetric (set α) subset 𝔸 where
antisymm := fun _ _ _ _ sa sb => setext (fun e => Iff.intro (sa e) (sb e))

instance subset.is_trans : transitive (set α) subset 𝔸 where
trans := fun _ _ _ _ _ _ sa sb e he => sb e (sa e he)

instance subset.preorder : preorder (set α) subset 𝔸 := preorder.mk

instance subset.partial_order : partial_order (set α) subset 𝔸 := partial_order.mk

-- lattice
instance power_set.has_bot : has_bot (set α) subset (power_set A) where
bot := empty
bot_mem := fun _ h => False.elim (Bool.false_eq_true ▸ h)
bot_def := fun _ _ _ h => False.elim (Bool.false_eq_true ▸ h)

instance power_set.has_top : has_top (set α) subset (power_set A) where
top := A
top_mem := fun _ ha => ha
top_def := fun _ ha => ha

instance power_set.has_inf : has_inf (set α) subset (power_set A) where
inf := inter
inf_mem := fun _ _ ha _ e he => ha e he.left
inf_left := fun _ _ _ _ _ he => he.left
inf_right := fun _ _ _ _  _ he => he.right
inf_higher := fun _ _ _ _ _ _  hca hcb e he => And.intro (hca e he) (hcb e he)

instance power_set.has_sup : has_sup (set α) subset (power_set A) where
sup := union
sup_mem := fun _ _ ha hb => fun m hm => Or.elim hm (fun a => ha m a) (fun b => hb m b)
sup_left := fun _ b _ _ => fun e he => Or.intro_left (b e) he
sup_right := fun a _ _ _ => fun e he => Or.intro_right (a e) he
sup_lower := fun _ _ _ _ _ _ hca hcb e he => Or.elim he (fun ha => hca e ha) (fun hb => hcb e hb)

instance power_set.lattice : lattice (set α) subset (power_set A) := lattice.mk

instance power_set.bounded_lattice : bounded_lattice (set α) subset (power_set A) := bounded_lattice.mk
