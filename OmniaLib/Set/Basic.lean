import OmniaLib.Set.Defs
namespace Set

variable {α : Type u}

-- subset relation
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

-- intersection operation
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

-- empty set and universal set
theorem empty.is_bot (A : set α) : subset empty A := by
unfold subset mem empty
intro a h
rw [Bool.false_eq_true] at h
exact False.elim h

theorem empty.bot_unique (A : set α) : subset A empty → A = empty := by
intro h
apply setext
intro a
apply Iff.intro
case h.mp =>
  exact fun ha => h a ha
case h.mpr =>
  unfold empty mem
  rw [Bool.false_eq_true]
  exact fun f => False.elim f

theorem empty.union_with (A : set α) : union A empty = A := by
apply setext
intro a
apply Iff.intro
case h.mp =>
  intro h
  exact Or.elim h (fun ha => ha) (empty.is_bot A a)
case h.mpr =>
  intro h
  exact union.left_subset A empty a h

theorem empty.inter_with (A : set α) : inter A empty = emty := by
apply setext
intro a
apply Iff.intro
case h.mp => sorry



theorem univ.is_top (A : set α) : subset A univ := by
unfold subset mem univ
intro a h
exact rfl

theorem univ.top_unique (A : set α) : subset univ A → A = univ := by
intro h
apply setext
intro a
apply Iff.intro
case h.mp =>
  unfold univ
  exact fun a => rfl
case h.mpr =>
  exact fun ha => h a ha
