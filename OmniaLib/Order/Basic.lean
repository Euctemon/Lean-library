import OmniaLib.Order.Defs
namespace Order

namespace meet
theorem left_absorb [p : has_meets α r] [k : partial_order α r] : p.meet a a = a := sorry




namespace partial_order
theorem bot_unique [p₁ : has_bot α r] [p₂ : partial_order α r] :
  ∀ (a : α), r a p₁.bot → a = p₁.bot := by
intro a ha
have : r p₁.bot a := p₁.is_bot a
exact p₂.antisymm a p₁.bot ha this

theorem neq_bot_imp_not_rel [p₁ : has_bot α r] [p₂ : partial_order α r] :
  ∀ (a : α), ¬ a = p₁.bot → ¬ r a p₁.bot := by
intro a ha hn
apply ha
exact bot_unique a hn

end partial_order
