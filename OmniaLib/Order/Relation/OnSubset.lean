import OmniaLib.Order.Relation.Defs

/-
Properties of relation are trivially satisfied on a subset of a carrier. But specific elements do not
generally enjoy this property. For example a subset of a carrier might not include the bottom or top
element. It might also not include suprema, infima, etc ...,  so no lattice instances.
-/

open Order Set
variable {α : Type u}

instance refl.on_subset (h : subset B A) (p : reflexive α r A) : reflexive α r B where
refl := fun a ha => p.refl a (h a ha)

instance antisymm.on_subset (h : subset B A) (p : antisymmetric α r A) : antisymmetric α r B where
antisymm := fun a b ha hb ra rb => p.antisymm a b (h a ha) (h b hb) ra rb

instance trans.on_subset (h : subset B A) (p : transitive α r A) : transitive α r B where
trans := fun a b c ha hb hc ra rb => p.trans a b c (h a ha) (h b hb) (h c hc) ra rb

instance preorder.on_subset (h : subset B A) (p : preorder α r A) : preorder α r B :=
 @preorder.mk α r B (refl.on_subset h p.toreflexive) (trans.on_subset h p.totransitive)

instance partial.order_on_subset (h : subset B A) (p : partial_order α r A) : partial_order α r B :=
 @partial_order.mk α r B (preorder.on_subset h p.topreorder) (antisymm.on_subset h p.toantisymmetric)
