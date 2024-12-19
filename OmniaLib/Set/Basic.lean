import OmniaLib.Set.Defs
namespace Set

variable {α : Type u}

theorem empty_subset_of_any (A : set α) : subset empty A := by
unfold subset mem empty
intro a h
rw [Bool.false_eq_true] at h
exact False.elim h

theorem any_subset_of_univ (A : set α) : subset A univ := by
unfold subset mem univ
intro a h
exact rfl

theorem subset.refl {A : set α} : subset A A := fun _ h => h

theorem subset.antisymm {A B : set α} : subset A B → subset B A → A = B := by
unfold subset mem
intro hab hba
apply setext
intro e
exact Iff.intro (hab e) (hba e)

theorem subset.trans (A B C : set α) : subset A B → subset B C → subset A C := by
unfold subset mem
intro hab hbc
intro e he
exact hbc e (hab e he)

theorem inter.symm {A B : set α} : inter A B = inter B A := by
apply setext
intro e
apply Iff.intro
case h.mp =>
  unfold inter set_of mem
  exact fun h => And.symm h
case h.mpr =>
  unfold inter set_of mem
  exact fun h => And.symm h

theorem inter.left_subset (A B : set α) : subset (inter A B) A := by
unfold inter set_of subset mem
exact fun e he => he.left

theorem inter.right_subset (A B : set α) : subset (inter A B) B := by
unfold inter set_of subset mem
exact fun e he => he.right

theorem inter.is_inf (A B C : set α) : subset C A → subset C B → subset C (inter A B) := by
unfold inter subset set_of mem
intro hca hcb e he
apply And.intro
case left =>
  exact hca e he
case right =>
  exact hcb e he

theorem union.symm {A B : set α} : union A B = union B A := by
apply setext
intro e
apply Iff.intro
case h.mp =>
  unfold union set_of mem
  exact fun h => Or.symm h
case h.mpr =>
  unfold union set_of mem
  exact fun h => Or.symm h

theorem union.left_subset (A B : set α) : subset A (union A B) := by
unfold union set_of subset mem
exact fun e he => Or.intro_left (B e) he

theorem union.right_subset (A B : set α) : subset B (union A B) := by
unfold union set_of subset mem
exact fun e he => Or.intro_right (A e) he

theorem union.is_sup (A B C : set α) : subset A C → subset B C → subset (union A B) C := by
unfold union subset set_of mem
intro hca hcb e he
apply Or.elim he
case left =>
  exact fun ha => hca e ha
case right =>
  exact fun hb => hcb e hb
