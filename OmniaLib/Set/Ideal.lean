import OmniaLib.Set.Order
import OmniaLib.Order.Ideal
import OmniaLib.Order.PartialOrder

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


-- work in progress


theorem subset_of_empty {A : set α} : subset A empty → A = empty := by
apply @Order.partial_order.bot_unique (set α) subset

theorem ff {A : set α} : ¬ A = empty → ¬ subset A empty := by
apply @Order.partial_order.neq_bot_imp_not_rel (set α) subset

theorem singleton_non (a : α) : a ∈ A → ¬ A = empty := by
intro h hn
rw [hn] at h
exact (Bool.eq_not_self false).mp h

theorem foo (A : set α) : ¬ A = empty → ¬ power_set A = empty := by
intro h hp
simp only [power_set, set_of] at hp
apply ff h
simp [subset]
intro a ha
simp [mem, empty]
have : subset A A := by exact fun a a => a
apply @singleton_non (set α) (fun S => subset S A) A _ hp
simp [mem]
exact this

instance (A : set α) (h : ¬ A = empty) : Order.ideal subset (power_set A) where
meet := inter
meet_left := subset.left_meets
meet_right := subset.right_meets
directed := set.directed
lower := set.lower_set
nonempty := foo A h
