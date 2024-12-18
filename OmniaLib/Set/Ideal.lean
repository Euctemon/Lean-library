import OmniaLib.Set.Order
import OmniaLib.Order.Ideal
namespace Set

variable {α : Type u}

theorem set.directed (A B : set α) : A ∈ power_set S → B ∈ power_set S → inter A B ∈ power_set S := by
simp only [power_set, mem, set_of]
intro ha hb
have := subset.left_meets A B
exact subset.trans (inter A B) A S this ha

theorem set.lower_set (A B : set α) : subset A B → B ∈ power_set C → A ∈ power_set C := by
simp only [power_set, mem, set_of]
intro ha hb
exact subset.trans A B C ha hb

instance (A : set α) (h : ¬ A = empty) : Order.ideal subset (power_set A) where
meet := inter
meet_left := subset.left_meets
meet_right := subset.right_meets
directed := set.directed
lower := set.lower_set
nonempty := sorry
