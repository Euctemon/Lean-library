import OmniaLib.Order.Relation.Defs

open Order Set
variable {α : Type u}

instance refl_on_subset (h : subset B A) (p : reflexive α r A) : reflexive α r B where
refl := fun a ha => p.refl a (h a ha)

instance antisymm_on_subset (h : subset B A) (p : antisymmetric α r A) : antisymmetric α r B where
antisymm := fun a b ha hb ra rb => p.antisymm a b (h a ha) (h b hb) ra rb

instance trans_on_subset (h : subset B A) (p : transitive α r A) : transitive α r B where
trans := fun a b c ha hb hc ra rb => p.trans a b c (h a ha) (h b hb) (h c hc) ra rb

instance has_inf_on_subset (h : subset B A) (p : has_inf α r A) : has_inf α r B := sorry
instance has_sup_on_subset (h : subset B A) (p : has_sup α r A) : has_sup α r B := sorry




instance preorder_on_subset (h : subset B A) (p : preorder α r A) : preorder α r B :=
 @preorder.mk α r B (refl_on_subset h p.toreflexive) (trans_on_subset h p.totransitive)

instance partial_order_on_subset (h : subset B A) (p : partial_order α r A) : partial_order α r B :=
 @partial_order.mk α r B (preorder_on_subset h p.topreorder) (antisymm_on_subset h p.toantisymmetric)

instance subset_is_refl : reflexive (set α) subset 𝔸 where
refl := fun _ _ => fun _ h => h

instance subset_is_antisymm : antisymmetric (set α) subset 𝔸 where
antisymm := by
  intro a b ha hb sa sb
  apply setext
  intro e
  exact Iff.intro (sa e) (sb e)

instance subset_is_trans : transitive (set α) subset 𝔸 where
trans := by
  intro a b c _ _ _ sa sb
  exact fun e he => (sb e (sa e he))

instance subset_has_bot : has_bot (set α) subset (power_set A) := sorry

instance subset_has_inf : has_inf (set α) subset (power_set A) := sorry

instance subset_has_top : has_top (set α) subset (power_set A) := sorry

instance subset_has_sup : has_sup (set α) subset (power_set A) := sorry

instance subset_is_preorder : preorder (set α) subset (power_set A) := preorder.mk

instance subset_is_partial_order : partial_order (set α) subset (power_set A) := partial_order.mk

instance subset_is_lattice : lattice (set α) subset (power_set A) := sorry
