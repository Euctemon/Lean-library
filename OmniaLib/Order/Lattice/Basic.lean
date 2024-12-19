import OmniaLib.Order.Relation.Defs
namespace Order

theorem bot.unique [p₁ : has_bot α r] [p₂ : partial_order α r] :
  ∀ (a : α), r a p₁.bot → a = p₁.bot := by
intro a h1
apply p₂.antisymm a p₁.bot h1
exact p₁.is_bot a

theorem top.unique [p₁ : has_top α r] [p₂ : partial_order α r] :
  ∀ (a : α), r p₁.top a → a = p₁.top := by
intro a h1
apply p₂.antisymm a p₁.top _ h1
exact p₁.is_top a

theorem inf.unique [p₁ : has_inf α r] [p₂ : partial_order α r] :
  ∀ (a b c : α), r c a → r c b → r (p₁.inf a b) c → p₁.inf a b = c := by
intro a b c h1 h2 h3
apply p₂.antisymm (p₁.inf a b) c h3
exact p₁.inf_higher a b c h1 h2

theorem inf.comm [p₁ : has_inf α r] [p₂ : partial_order α r] :
  ∀ (a b : α), p₁.inf a b = p₁.inf b a := by
intro a b
have left : r (p₁.inf a b) (p₁.inf b a) := by
  simp only [p₁.inf_higher, p₁.inf_left, p₁.inf_right]
have right : r (p₁.inf b a) (p₁.inf a b) := by
  simp only [p₁.inf_higher, p₁.inf_left, p₁.inf_right]
exact p₂.antisymm _ _ left right

theorem sup.unique [p₁ : has_sup α r] [p₂ : partial_order α r] :
  ∀ (a b c : α), r a c → r b c → r c (p₁.sup a b) → p₁.sup a b = c := by
intro a b c h1 h2 h3
apply p₂.antisymm (p₁.sup a b) c _ h3
exact p₁.sup_lower a b c h1 h2

theorem sup.comm [p₁ : has_sup α r] [p₂ : partial_order α r] :
  ∀ (a b : α), p₁.sup a b = p₁.sup b a := by
intro a b
have left : r (p₁.sup a b) (p₁.sup b a) := by
  simp only [p₁.sup_lower, p₁.sup_left, p₁.sup_right]
have right : r (p₁.sup b a) (p₁.sup a b) := by
  simp only [p₁.sup_lower, p₁.sup_left, p₁.sup_right]
exact p₂.antisymm _ _ left right
