import OmniaLib.Order.Relation.Defs

open Order

theorem bot.unique (p₁ : has_bot α r A) (p₂ : antisymmetric α r A) :
  ∀ (a : α), a ∈ A → r a p₁.bot → a = p₁.bot := by
intro a ha hr
have : r p₁.bot a := p₁.bot_def a ha
exact p₂.antisymm a p₁.bot ha p₁.bot_mem hr this

theorem bot.inf_idemp (p : bounded_lattice α r A) : ∀ (a : α), a ∈ A → p.inf p.bot a = p.bot := by
intro a ha
have : r (p.inf p.bot a) p.bot := sorry
sorry
