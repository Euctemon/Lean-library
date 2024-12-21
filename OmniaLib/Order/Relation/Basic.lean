import OmniaLib.Order.Relation.Defs

open Order

theorem bot.unique (p₁ : has_bot α r A) (p₂ : antisymmetric α r A) :
  ∀ (a : α), a ∈ A → r a ⊥ → a = ⊥ := by
intro a ha hr
have : r ⊥ a := p₁.bot_def a ha
exact p₂.antisymm a p₁.bot ha p₁.bot_mem hr this

theorem bot.inf_idemp (p : bounded_lattice α r A) : ∀ (a : α), a ∈ A → ⊥ ⊓ a = ⊥ := by
intro a ha
have : r (⊥ ⊓ a) ⊥ := p.inf_left p.bot a p.bot_mem ha
apply bot.unique p.tohas_bot p.toantisymmetric
exact p.inf_mem p.bot a p.bot_mem ha
exact this


theorem dodo (p : lattice α r A) : ∀ (a : α), a ∈ A → a ⊔ a = a := by
intro a ha
apply p.antisymm
sorry
exact ha
exact p.sup_lower a a a ha ha ha (p.refl a ha) (p.refl a ha)


theorem doo (p : lattice α r A) : ∀ (a b : α), a ∈ A → b ∈ A → r a b → r (a ⊔ b) b := by
intro a b ha hb rab
exact p.sup_lower a b b ha hb hb rab (p.refl b hb)


theorem bot.sup_idemp (p : bounded_lattice α r A) : ∀ (a : α), a ∈ A → ⊥ ⊔ a = a := by
intro a ha
apply p.antisymm _ _ (p.sup_mem p.bot a p.bot_mem ha) ha
have : r (⊥ ⊔ a) a := by
  apply doo
  exact p.bot_mem
  exact ha
  exact p.bot_def a ha
exact this
apply p.sup_right ⊥ a
exact p.bot_mem
exact ha
