import LeanProofs.A198683FiveSix

/-!
# OEIS A198683: the upper bound `a198683 7 <= 34`

The `n = 7` representative-list refinement pipeline: starting from the full
split enumeration, successive collapsed representative lists are proved to
cover `a198683ValueSet 7`, ending in the 34-element canonical representative
list and the upper bound `a198683_seven_le_thirty_four`.
-/

namespace LeanProofs

noncomputable section

open Complex

open A198683Support

private noncomputable def a198683SevenCollapsedReps : List ℂ :=
  [principalPow Complex.I p6A, principalPow Complex.I p6B, principalPow Complex.I p6C,
    principalPow Complex.I p6D, principalPow Complex.I p6E, principalPow Complex.I p6F,
    principalPow Complex.I p6G, principalPow Complex.I p6H, principalPow Complex.I p6I,
    principalPow Complex.I p6J, principalPow Complex.I p6K, principalPow Complex.I p6L,
    principalPow Complex.I p6M, principalPow Complex.I p6N, principalPow Complex.I p6O,
    principalPow p2 p5A, principalPow p2 p5B, principalPow p2 p5C,
    principalPow p2 p5D, principalPow p2 p5E, principalPow p2 p5F,
    principalPow p2 p5G,
    principalPow p3L p4A, principalPow p3L p4B, principalPow p3L p4C,
    principalPow p3R p4A, principalPow p3R p4B, principalPow p3R p4C,
    principalPow p4A p3L, principalPow p4A p3R, principalPow p4B p3L,
    principalPow p4C p3L,
    principalPow p5A p2, principalPow p5B p2, principalPow p5C p2,
    principalPow p5D p2, principalPow p5F p2, principalPow p5G p2,
    principalPow p6A Complex.I, principalPow p6B Complex.I, principalPow p6C Complex.I,
    principalPow p6D Complex.I, principalPow p6F Complex.I, principalPow p6G Complex.I,
    principalPow p6H Complex.I, principalPow p6I Complex.I, principalPow p6J Complex.I,
    principalPow p6K Complex.I, principalPow p6M Complex.I, principalPow p6N Complex.I,
    principalPow p6O Complex.I]

private theorem a198683_seven_subset_collapsedReps :
    a198683ValueSet 7 ⊆
      Set.range (fun i : Fin a198683SevenCollapsedReps.length =>
        a198683SevenCollapsedReps.get i) := by
  classical
  have reps_length : a198683SevenCollapsedReps.length = 51 := by
    norm_num [a198683SevenCollapsedReps]
  let rep : Fin a198683SevenCollapsedReps.length → ℂ :=
    fun i => a198683SevenCollapsedReps.get i
  change a198683ValueSet 7 ⊆ Set.range rep
  have inRange (i : Nat) (h : i < a198683SevenCollapsedReps.length) :
      a198683SevenCollapsedReps.get ⟨i, h⟩ ∈ Set.range rep := by
    exact ⟨⟨i, h⟩, rfl⟩
  intro z hz
  simp only [a198683ValueSet] at hz
  rcases hz with ⟨k, x, hx, y, hy, rfl⟩
  fin_cases k
  · change x ∈ a198683ValueSet 1 at hx
    change y ∈ a198683ValueSet 6 at hy
    rw [mem_valueSet_one] at hx
    rw [mem_valueSet_six] at hy
    rcases hx
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact inRange 0 (by rw [reps_length]; norm_num)
    · exact inRange 1 (by rw [reps_length]; norm_num)
    · exact inRange 2 (by rw [reps_length]; norm_num)
    · exact inRange 3 (by rw [reps_length]; norm_num)
    · exact inRange 4 (by rw [reps_length]; norm_num)
    · exact inRange 5 (by rw [reps_length]; norm_num)
    · exact inRange 6 (by rw [reps_length]; norm_num)
    · exact inRange 7 (by rw [reps_length]; norm_num)
    · exact inRange 8 (by rw [reps_length]; norm_num)
    · exact inRange 9 (by rw [reps_length]; norm_num)
    · exact inRange 10 (by rw [reps_length]; norm_num)
    · exact inRange 11 (by rw [reps_length]; norm_num)
    · exact inRange 12 (by rw [reps_length]; norm_num)
    · exact inRange 13 (by rw [reps_length]; norm_num)
    · exact inRange 14 (by rw [reps_length]; norm_num)
  · change x ∈ a198683ValueSet 2 at hx
    change y ∈ a198683ValueSet 5 at hy
    rw [mem_valueSet_two] at hx
    rw [mem_valueSet_five] at hy
    rcases hx
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inRange 15 (by rw [reps_length]; norm_num)
    · exact inRange 16 (by rw [reps_length]; norm_num)
    · exact inRange 17 (by rw [reps_length]; norm_num)
    · exact inRange 18 (by rw [reps_length]; norm_num)
    · exact inRange 19 (by rw [reps_length]; norm_num)
    · exact inRange 20 (by rw [reps_length]; norm_num)
    · exact inRange 21 (by rw [reps_length]; norm_num)
  · change x ∈ a198683ValueSet 3 at hx
    change y ∈ a198683ValueSet 4 at hy
    rw [mem_valueSet_three] at hx
    rw [mem_valueSet_four] at hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl | rfl
      · exact inRange 22 (by rw [reps_length]; norm_num)
      · exact inRange 23 (by rw [reps_length]; norm_num)
      · exact inRange 24 (by rw [reps_length]; norm_num)
    · rcases hy with rfl | rfl | rfl
      · exact inRange 25 (by rw [reps_length]; norm_num)
      · exact inRange 26 (by rw [reps_length]; norm_num)
      · exact inRange 27 (by rw [reps_length]; norm_num)
  · change x ∈ a198683ValueSet 4 at hx
    change y ∈ a198683ValueSet 3 at hy
    rw [mem_valueSet_four] at hx
    rw [mem_valueSet_three] at hy
    rcases hx with rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact inRange 28 (by rw [reps_length]; norm_num)
      · exact inRange 29 (by rw [reps_length]; norm_num)
    · rcases hy with rfl | rfl
      · exact inRange 30 (by rw [reps_length]; norm_num)
      · change principalPow p4B p3R ∈ Set.range rep
        rw [p4B_pow_p3R_eq_p2_pow_p5E]
        exact inRange 19 (by rw [reps_length]; norm_num)
    · rcases hy with rfl | rfl
      · exact inRange 31 (by rw [reps_length]; norm_num)
      · change principalPow p4C p3R ∈ Set.range rep
        rw [p4C_pow_p3R_eq_p3L, ← I_pow_p6E_eq_p3L]
        exact inRange 4 (by rw [reps_length]; norm_num)
  · change x ∈ a198683ValueSet 5 at hx
    change y ∈ a198683ValueSet 2 at hy
    rw [mem_valueSet_five] at hx
    rw [mem_valueSet_two] at hy
    rcases hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact inRange 32 (by rw [reps_length]; norm_num)
    · exact inRange 33 (by rw [reps_length]; norm_num)
    · exact inRange 34 (by rw [reps_length]; norm_num)
    · exact inRange 35 (by rw [reps_length]; norm_num)
    · change principalPow p5E p2 ∈ Set.range rep
      rw [p5E_pow_p2_eq_p3L, ← I_pow_p6E_eq_p3L]
      exact inRange 4 (by rw [reps_length]; norm_num)
    · exact inRange 36 (by rw [reps_length]; norm_num)
    · exact inRange 37 (by rw [reps_length]; norm_num)
  · change x ∈ a198683ValueSet 6 at hx
    change y ∈ a198683ValueSet 1 at hy
    rw [mem_valueSet_six] at hx
    rw [mem_valueSet_one] at hy
    rcases hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · exact inRange 38 (by rw [reps_length]; norm_num)
    · exact inRange 39 (by rw [reps_length]; norm_num)
    · exact inRange 40 (by rw [reps_length]; norm_num)
    · exact inRange 41 (by rw [reps_length]; norm_num)
    · rw [p6E_pow_I_eq_p2_pow_p5E]
      exact inRange 19 (by rw [reps_length]; norm_num)
    · exact inRange 42 (by rw [reps_length]; norm_num)
    · exact inRange 43 (by rw [reps_length]; norm_num)
    · exact inRange 44 (by rw [reps_length]; norm_num)
    · exact inRange 45 (by rw [reps_length]; norm_num)
    · exact inRange 46 (by rw [reps_length]; norm_num)
    · exact inRange 47 (by rw [reps_length]; norm_num)
    · rw [p6L_pow_I_eq_p3L, ← I_pow_p6E_eq_p3L]
      exact inRange 4 (by rw [reps_length]; norm_num)
    · exact inRange 48 (by rw [reps_length]; norm_num)
    · exact inRange 49 (by rw [reps_length]; norm_num)
    · exact inRange 50 (by rw [reps_length]; norm_num)

private noncomputable def a198683SevenMoreCollapsedReps : List ℂ :=
  [principalPow Complex.I p6A, principalPow Complex.I p6B, principalPow Complex.I p6C,
    principalPow Complex.I p6D, principalPow Complex.I p6E, principalPow Complex.I p6F,
    principalPow Complex.I p6G, principalPow Complex.I p6H, principalPow Complex.I p6I,
    principalPow Complex.I p6J, principalPow Complex.I p6K, principalPow Complex.I p6L,
    principalPow Complex.I p6M, principalPow Complex.I p6N, principalPow Complex.I p6O,
    principalPow p2 p5A, principalPow p2 p5B, principalPow p2 p5C,
    principalPow p2 p5D, principalPow p2 p5E, principalPow p2 p5F,
    principalPow p2 p5G,
    principalPow p3L p4A, principalPow p3L p4B, principalPow p3L p4C,
    principalPow p3R p4A, principalPow p3R p4B, principalPow p3R p4C,
    principalPow p4A p3L, principalPow p4A p3R, principalPow p4B p3L,
    principalPow p4C p3L,
    principalPow p5B p2, principalPow p5F p2, principalPow p5G p2,
    principalPow p6A Complex.I, principalPow p6B Complex.I, principalPow p6C Complex.I,
    principalPow p6D Complex.I, principalPow p6F Complex.I, principalPow p6G Complex.I,
    principalPow p6H Complex.I, principalPow p6K Complex.I, principalPow p6M Complex.I,
    principalPow p6O Complex.I]

private theorem a198683_seven_subset_moreCollapsedReps :
    a198683ValueSet 7 ⊆
      Set.range (fun i : Fin a198683SevenMoreCollapsedReps.length =>
        a198683SevenMoreCollapsedReps.get i) := by
  classical
  let rep51 : Fin a198683SevenCollapsedReps.length → ℂ :=
    fun i => a198683SevenCollapsedReps.get i
  let rep45 : Fin a198683SevenMoreCollapsedReps.length → ℂ :=
    fun i => a198683SevenMoreCollapsedReps.get i
  have hsubset51 : a198683ValueSet 7 ⊆ Set.range rep51 := by
    simpa [rep51] using a198683_seven_subset_collapsedReps
  have reps45_length : a198683SevenMoreCollapsedReps.length = 45 := by
    norm_num [a198683SevenMoreCollapsedReps]
  have inRange45 (i : Nat) (h : i < a198683SevenMoreCollapsedReps.length) :
      a198683SevenMoreCollapsedReps.get ⟨i, h⟩ ∈ Set.range rep45 := by
    exact ⟨⟨i, h⟩, rfl⟩
  have hrange : Set.range rep51 ⊆ Set.range rep45 := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    fin_cases i
    · exact inRange45 0 (by rw [reps45_length]; norm_num)
    · exact inRange45 1 (by rw [reps45_length]; norm_num)
    · exact inRange45 2 (by rw [reps45_length]; norm_num)
    · exact inRange45 3 (by rw [reps45_length]; norm_num)
    · exact inRange45 4 (by rw [reps45_length]; norm_num)
    · exact inRange45 5 (by rw [reps45_length]; norm_num)
    · exact inRange45 6 (by rw [reps45_length]; norm_num)
    · exact inRange45 7 (by rw [reps45_length]; norm_num)
    · exact inRange45 8 (by rw [reps45_length]; norm_num)
    · exact inRange45 9 (by rw [reps45_length]; norm_num)
    · exact inRange45 10 (by rw [reps45_length]; norm_num)
    · exact inRange45 11 (by rw [reps45_length]; norm_num)
    · exact inRange45 12 (by rw [reps45_length]; norm_num)
    · exact inRange45 13 (by rw [reps45_length]; norm_num)
    · exact inRange45 14 (by rw [reps45_length]; norm_num)
    · exact inRange45 15 (by rw [reps45_length]; norm_num)
    · exact inRange45 16 (by rw [reps45_length]; norm_num)
    · exact inRange45 17 (by rw [reps45_length]; norm_num)
    · exact inRange45 18 (by rw [reps45_length]; norm_num)
    · exact inRange45 19 (by rw [reps45_length]; norm_num)
    · exact inRange45 20 (by rw [reps45_length]; norm_num)
    · exact inRange45 21 (by rw [reps45_length]; norm_num)
    · exact inRange45 22 (by rw [reps45_length]; norm_num)
    · exact inRange45 23 (by rw [reps45_length]; norm_num)
    · exact inRange45 24 (by rw [reps45_length]; norm_num)
    · exact inRange45 25 (by rw [reps45_length]; norm_num)
    · exact inRange45 26 (by rw [reps45_length]; norm_num)
    · exact inRange45 27 (by rw [reps45_length]; norm_num)
    · exact inRange45 28 (by rw [reps45_length]; norm_num)
    · exact inRange45 29 (by rw [reps45_length]; norm_num)
    · exact inRange45 30 (by rw [reps45_length]; norm_num)
    · exact inRange45 31 (by rw [reps45_length]; norm_num)
    · change principalPow p5A p2 ∈ Set.range rep45
      rw [← p3L_pow_p4A_eq_p5A_pow_p2]
      exact inRange45 22 (by rw [reps45_length]; norm_num)
    · exact inRange45 32 (by rw [reps45_length]; norm_num)
    · change principalPow p5C p2 ∈ Set.range rep45
      rw [← p3L_pow_p4C_eq_p5C_pow_p2]
      exact inRange45 24 (by rw [reps45_length]; norm_num)
    · change principalPow p5D p2 ∈ Set.range rep45
      rw [← p4C_pow_p3L_eq_p5D_pow_p2]
      exact inRange45 31 (by rw [reps45_length]; norm_num)
    · exact inRange45 33 (by rw [reps45_length]; norm_num)
    · exact inRange45 34 (by rw [reps45_length]; norm_num)
    · exact inRange45 35 (by rw [reps45_length]; norm_num)
    · exact inRange45 36 (by rw [reps45_length]; norm_num)
    · exact inRange45 37 (by rw [reps45_length]; norm_num)
    · exact inRange45 38 (by rw [reps45_length]; norm_num)
    · exact inRange45 39 (by rw [reps45_length]; norm_num)
    · exact inRange45 40 (by rw [reps45_length]; norm_num)
    · exact inRange45 41 (by rw [reps45_length]; norm_num)
    · change principalPow p6I Complex.I ∈ Set.range rep45
      rw [← p3R_pow_p4B_eq_p6I_pow_I]
      exact inRange45 26 (by rw [reps45_length]; norm_num)
    · change principalPow p6J Complex.I ∈ Set.range rep45
      rw [← p3R_pow_p4C_eq_p6J_pow_I]
      exact inRange45 27 (by rw [reps45_length]; norm_num)
    · exact inRange45 42 (by rw [reps45_length]; norm_num)
    · exact inRange45 43 (by rw [reps45_length]; norm_num)
    · change principalPow p6N Complex.I ∈ Set.range rep45
      rw [← p5G_pow_p2_eq_p6N_pow_I]
      exact inRange45 34 (by rw [reps45_length]; norm_num)
    · exact inRange45 44 (by rw [reps45_length]; norm_num)
  exact hsubset51.trans hrange

private noncomputable def a198683SevenPeriodicCollapsedReps : List ℂ :=
  [principalPow Complex.I p6A, principalPow Complex.I p6B, principalPow Complex.I p6C,
    principalPow Complex.I p6D, principalPow Complex.I p6E, principalPow Complex.I p6F,
    principalPow Complex.I p6G, principalPow Complex.I p6H, principalPow Complex.I p6I,
    principalPow Complex.I p6J, principalPow Complex.I p6K, principalPow Complex.I p6L,
    principalPow Complex.I p6M, principalPow Complex.I p6N, principalPow Complex.I p6O,
    principalPow p2 p5A, principalPow p2 p5B, principalPow p2 p5C,
    principalPow p2 p5D, principalPow p2 p5E, principalPow p2 p5F,
    principalPow p2 p5G,
    principalPow p3L p4A, principalPow p3L p4B, principalPow p3L p4C,
    principalPow p3R p4A, principalPow p3R p4B, principalPow p3R p4C,
    principalPow p4A p3L, principalPow p4A p3R, principalPow p4B p3L,
    principalPow p4C p3L,
    principalPow p5B p2, principalPow p5F p2, principalPow p5G p2,
    principalPow p6A Complex.I, principalPow p6B Complex.I, principalPow p6C Complex.I,
    principalPow p6D Complex.I, principalPow p6F Complex.I, principalPow p6G Complex.I,
    principalPow p6H Complex.I, principalPow p6K Complex.I, principalPow p6M Complex.I]

private theorem a198683_seven_subset_periodicCollapsedReps :
    a198683ValueSet 7 ⊆
      Set.range (fun i : Fin a198683SevenPeriodicCollapsedReps.length =>
        a198683SevenPeriodicCollapsedReps.get i) := by
  classical
  let rep45 : Fin a198683SevenMoreCollapsedReps.length → ℂ :=
    fun i => a198683SevenMoreCollapsedReps.get i
  let rep44 : Fin a198683SevenPeriodicCollapsedReps.length → ℂ :=
    fun i => a198683SevenPeriodicCollapsedReps.get i
  have hsubset45 : a198683ValueSet 7 ⊆ Set.range rep45 := by
    simpa [rep45] using a198683_seven_subset_moreCollapsedReps
  have reps44_length : a198683SevenPeriodicCollapsedReps.length = 44 := by
    norm_num [a198683SevenPeriodicCollapsedReps]
  have inRange44 (i : Nat) (h : i < a198683SevenPeriodicCollapsedReps.length) :
      a198683SevenPeriodicCollapsedReps.get ⟨i, h⟩ ∈ Set.range rep44 := by
    exact ⟨⟨i, h⟩, rfl⟩
  have hrange : Set.range rep45 ⊆ Set.range rep44 := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    fin_cases i
    · exact inRange44 0 (by rw [reps44_length]; norm_num)
    · exact inRange44 1 (by rw [reps44_length]; norm_num)
    · exact inRange44 2 (by rw [reps44_length]; norm_num)
    · exact inRange44 3 (by rw [reps44_length]; norm_num)
    · exact inRange44 4 (by rw [reps44_length]; norm_num)
    · exact inRange44 5 (by rw [reps44_length]; norm_num)
    · exact inRange44 6 (by rw [reps44_length]; norm_num)
    · exact inRange44 7 (by rw [reps44_length]; norm_num)
    · exact inRange44 8 (by rw [reps44_length]; norm_num)
    · exact inRange44 9 (by rw [reps44_length]; norm_num)
    · exact inRange44 10 (by rw [reps44_length]; norm_num)
    · exact inRange44 11 (by rw [reps44_length]; norm_num)
    · exact inRange44 12 (by rw [reps44_length]; norm_num)
    · exact inRange44 13 (by rw [reps44_length]; norm_num)
    · exact inRange44 14 (by rw [reps44_length]; norm_num)
    · exact inRange44 15 (by rw [reps44_length]; norm_num)
    · exact inRange44 16 (by rw [reps44_length]; norm_num)
    · exact inRange44 17 (by rw [reps44_length]; norm_num)
    · exact inRange44 18 (by rw [reps44_length]; norm_num)
    · exact inRange44 19 (by rw [reps44_length]; norm_num)
    · exact inRange44 20 (by rw [reps44_length]; norm_num)
    · exact inRange44 21 (by rw [reps44_length]; norm_num)
    · exact inRange44 22 (by rw [reps44_length]; norm_num)
    · exact inRange44 23 (by rw [reps44_length]; norm_num)
    · exact inRange44 24 (by rw [reps44_length]; norm_num)
    · exact inRange44 25 (by rw [reps44_length]; norm_num)
    · exact inRange44 26 (by rw [reps44_length]; norm_num)
    · exact inRange44 27 (by rw [reps44_length]; norm_num)
    · exact inRange44 28 (by rw [reps44_length]; norm_num)
    · exact inRange44 29 (by rw [reps44_length]; norm_num)
    · exact inRange44 30 (by rw [reps44_length]; norm_num)
    · exact inRange44 31 (by rw [reps44_length]; norm_num)
    · exact inRange44 32 (by rw [reps44_length]; norm_num)
    · exact inRange44 33 (by rw [reps44_length]; norm_num)
    · exact inRange44 34 (by rw [reps44_length]; norm_num)
    · exact inRange44 35 (by rw [reps44_length]; norm_num)
    · exact inRange44 36 (by rw [reps44_length]; norm_num)
    · exact inRange44 37 (by rw [reps44_length]; norm_num)
    · exact inRange44 38 (by rw [reps44_length]; norm_num)
    · exact inRange44 39 (by rw [reps44_length]; norm_num)
    · exact inRange44 40 (by rw [reps44_length]; norm_num)
    · exact inRange44 41 (by rw [reps44_length]; norm_num)
    · exact inRange44 42 (by rw [reps44_length]; norm_num)
    · exact inRange44 43 (by rw [reps44_length]; norm_num)
    · change principalPow p6O Complex.I ∈ Set.range rep44
      rw [p6O_pow_I_eq_p3R_pow_p4B]
      exact inRange44 26 (by rw [reps44_length]; norm_num)
  exact hsubset45.trans hrange

private noncomputable def a198683SevenBranchCollapsedReps : List ℂ :=
  [principalPow Complex.I p6A, principalPow Complex.I p6B, principalPow Complex.I p6C,
    principalPow Complex.I p6D, principalPow Complex.I p6E, principalPow Complex.I p6F,
    principalPow Complex.I p6G, principalPow Complex.I p6H, principalPow Complex.I p6I,
    principalPow Complex.I p6J, principalPow Complex.I p6K, principalPow Complex.I p6L,
    principalPow Complex.I p6M, principalPow Complex.I p6N, principalPow Complex.I p6O,
    principalPow p2 p5A, principalPow p2 p5B, principalPow p2 p5C,
    principalPow p2 p5D, principalPow p2 p5E, principalPow p2 p5F,
    principalPow p2 p5G,
    principalPow p3L p4A, principalPow p3L p4B, principalPow p3L p4C,
    principalPow p3R p4A, principalPow p3R p4B, principalPow p3R p4C,
    principalPow p4A p3L, principalPow p4A p3R, principalPow p4B p3L,
    principalPow p4C p3L,
    principalPow p5B p2, principalPow p5F p2, principalPow p5G p2,
    principalPow p6H Complex.I, principalPow p6K Complex.I, principalPow p6M Complex.I]

private theorem a198683_seven_subset_branchCollapsedReps :
    a198683ValueSet 7 ⊆
      Set.range (fun i : Fin a198683SevenBranchCollapsedReps.length =>
        a198683SevenBranchCollapsedReps.get i) := by
  classical
  let rep44 : Fin a198683SevenPeriodicCollapsedReps.length → ℂ :=
    fun i => a198683SevenPeriodicCollapsedReps.get i
  let rep38 : Fin a198683SevenBranchCollapsedReps.length → ℂ :=
    fun i => a198683SevenBranchCollapsedReps.get i
  have hsubset44 : a198683ValueSet 7 ⊆ Set.range rep44 := by
    simpa [rep44] using a198683_seven_subset_periodicCollapsedReps
  have reps38_length : a198683SevenBranchCollapsedReps.length = 38 := by
    norm_num [a198683SevenBranchCollapsedReps]
  have inRange38 (i : Nat) (h : i < a198683SevenBranchCollapsedReps.length) :
      a198683SevenBranchCollapsedReps.get ⟨i, h⟩ ∈ Set.range rep38 := by
    exact ⟨⟨i, h⟩, rfl⟩
  have hrange : Set.range rep44 ⊆ Set.range rep38 := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    fin_cases i
    · exact inRange38 0 (by rw [reps38_length]; norm_num)
    · exact inRange38 1 (by rw [reps38_length]; norm_num)
    · exact inRange38 2 (by rw [reps38_length]; norm_num)
    · exact inRange38 3 (by rw [reps38_length]; norm_num)
    · exact inRange38 4 (by rw [reps38_length]; norm_num)
    · exact inRange38 5 (by rw [reps38_length]; norm_num)
    · exact inRange38 6 (by rw [reps38_length]; norm_num)
    · exact inRange38 7 (by rw [reps38_length]; norm_num)
    · exact inRange38 8 (by rw [reps38_length]; norm_num)
    · exact inRange38 9 (by rw [reps38_length]; norm_num)
    · exact inRange38 10 (by rw [reps38_length]; norm_num)
    · exact inRange38 11 (by rw [reps38_length]; norm_num)
    · exact inRange38 12 (by rw [reps38_length]; norm_num)
    · exact inRange38 13 (by rw [reps38_length]; norm_num)
    · exact inRange38 14 (by rw [reps38_length]; norm_num)
    · exact inRange38 15 (by rw [reps38_length]; norm_num)
    · exact inRange38 16 (by rw [reps38_length]; norm_num)
    · exact inRange38 17 (by rw [reps38_length]; norm_num)
    · exact inRange38 18 (by rw [reps38_length]; norm_num)
    · exact inRange38 19 (by rw [reps38_length]; norm_num)
    · exact inRange38 20 (by rw [reps38_length]; norm_num)
    · exact inRange38 21 (by rw [reps38_length]; norm_num)
    · exact inRange38 22 (by rw [reps38_length]; norm_num)
    · exact inRange38 23 (by rw [reps38_length]; norm_num)
    · exact inRange38 24 (by rw [reps38_length]; norm_num)
    · exact inRange38 25 (by rw [reps38_length]; norm_num)
    · exact inRange38 26 (by rw [reps38_length]; norm_num)
    · exact inRange38 27 (by rw [reps38_length]; norm_num)
    · exact inRange38 28 (by rw [reps38_length]; norm_num)
    · exact inRange38 29 (by rw [reps38_length]; norm_num)
    · exact inRange38 30 (by rw [reps38_length]; norm_num)
    · exact inRange38 31 (by rw [reps38_length]; norm_num)
    · exact inRange38 32 (by rw [reps38_length]; norm_num)
    · exact inRange38 33 (by rw [reps38_length]; norm_num)
    · exact inRange38 34 (by rw [reps38_length]; norm_num)
    · change principalPow p6A Complex.I ∈ Set.range rep38
      rw [p6A_pow_I_eq_p2_pow_p5A]
      exact inRange38 15 (by rw [reps38_length]; norm_num)
    · change principalPow p6B Complex.I ∈ Set.range rep38
      rw [p6B_pow_I_eq_p2_pow_p5B]
      exact inRange38 16 (by rw [reps38_length]; norm_num)
    · change principalPow p6C Complex.I ∈ Set.range rep38
      rw [p6C_pow_I_eq_p2_pow_p5C]
      exact inRange38 17 (by rw [reps38_length]; norm_num)
    · change principalPow p6D Complex.I ∈ Set.range rep38
      rw [p6D_pow_I_eq_p2_pow_p5D]
      exact inRange38 18 (by rw [reps38_length]; norm_num)
    · change principalPow p6F Complex.I ∈ Set.range rep38
      rw [p6F_pow_I_eq_p2_pow_p5F]
      exact inRange38 20 (by rw [reps38_length]; norm_num)
    · change principalPow p6G Complex.I ∈ Set.range rep38
      rw [p6G_pow_I_eq_p2_pow_p5G]
      exact inRange38 21 (by rw [reps38_length]; norm_num)
    · exact inRange38 35 (by rw [reps38_length]; norm_num)
    · exact inRange38 36 (by rw [reps38_length]; norm_num)
    · exact inRange38 37 (by rw [reps38_length]; norm_num)
  exact hsubset44.trans hrange

namespace A198683Support

noncomputable def a198683SevenCanonicalReps : List ℂ :=
  [principalPow Complex.I p6A, principalPow Complex.I p6B, principalPow Complex.I p6C,
    principalPow Complex.I p6D, principalPow Complex.I p6E, principalPow Complex.I p6F,
    principalPow Complex.I p6G, principalPow Complex.I p6H, principalPow Complex.I p6I,
    principalPow Complex.I p6J, principalPow Complex.I p6K, principalPow Complex.I p6L,
    principalPow Complex.I p6M, principalPow Complex.I p6N, principalPow Complex.I p6O,
    principalPow p2 p5A, principalPow p2 p5B, principalPow p2 p5C,
    principalPow p2 p5D, principalPow p2 p5E, principalPow p2 p5F,
    principalPow p2 p5G,
    principalPow p3L p4A, principalPow p3L p4B, principalPow p3L p4C,
    principalPow p3R p4A, principalPow p3R p4B, principalPow p3R p4C,
    principalPow p4A p3L, principalPow p4B p3L, principalPow p4C p3L,
    principalPow p5B p2, principalPow p5F p2, principalPow p5G p2]

theorem a198683_seven_subset_canonicalReps :
    a198683ValueSet 7 ⊆
      Set.range (fun i : Fin a198683SevenCanonicalReps.length =>
        a198683SevenCanonicalReps.get i) := by
  classical
  let rep38 : Fin a198683SevenBranchCollapsedReps.length → ℂ :=
    fun i => a198683SevenBranchCollapsedReps.get i
  let rep34 : Fin a198683SevenCanonicalReps.length → ℂ :=
    fun i => a198683SevenCanonicalReps.get i
  have hsubset38 : a198683ValueSet 7 ⊆ Set.range rep38 := by
    simpa [rep38] using a198683_seven_subset_branchCollapsedReps
  have reps34_length : a198683SevenCanonicalReps.length = 34 := by
    norm_num [a198683SevenCanonicalReps]
  have inRange34 (i : Nat) (h : i < a198683SevenCanonicalReps.length) :
      a198683SevenCanonicalReps.get ⟨i, h⟩ ∈ Set.range rep34 := by
    exact ⟨⟨i, h⟩, rfl⟩
  have hrange : Set.range rep38 ⊆ Set.range rep34 := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    fin_cases i
    · exact inRange34 0 (by rw [reps34_length]; norm_num)
    · exact inRange34 1 (by rw [reps34_length]; norm_num)
    · exact inRange34 2 (by rw [reps34_length]; norm_num)
    · exact inRange34 3 (by rw [reps34_length]; norm_num)
    · exact inRange34 4 (by rw [reps34_length]; norm_num)
    · exact inRange34 5 (by rw [reps34_length]; norm_num)
    · exact inRange34 6 (by rw [reps34_length]; norm_num)
    · exact inRange34 7 (by rw [reps34_length]; norm_num)
    · exact inRange34 8 (by rw [reps34_length]; norm_num)
    · exact inRange34 9 (by rw [reps34_length]; norm_num)
    · exact inRange34 10 (by rw [reps34_length]; norm_num)
    · exact inRange34 11 (by rw [reps34_length]; norm_num)
    · exact inRange34 12 (by rw [reps34_length]; norm_num)
    · exact inRange34 13 (by rw [reps34_length]; norm_num)
    · exact inRange34 14 (by rw [reps34_length]; norm_num)
    · exact inRange34 15 (by rw [reps34_length]; norm_num)
    · exact inRange34 16 (by rw [reps34_length]; norm_num)
    · exact inRange34 17 (by rw [reps34_length]; norm_num)
    · exact inRange34 18 (by rw [reps34_length]; norm_num)
    · exact inRange34 19 (by rw [reps34_length]; norm_num)
    · exact inRange34 20 (by rw [reps34_length]; norm_num)
    · exact inRange34 21 (by rw [reps34_length]; norm_num)
    · exact inRange34 22 (by rw [reps34_length]; norm_num)
    · exact inRange34 23 (by rw [reps34_length]; norm_num)
    · exact inRange34 24 (by rw [reps34_length]; norm_num)
    · exact inRange34 25 (by rw [reps34_length]; norm_num)
    · exact inRange34 26 (by rw [reps34_length]; norm_num)
    · exact inRange34 27 (by rw [reps34_length]; norm_num)
    · exact inRange34 28 (by rw [reps34_length]; norm_num)
    · change principalPow p4A p3R ∈ Set.range rep34
      rw [p4A_pow_p3R_eq_p4B_pow_p3L]
      exact inRange34 29 (by rw [reps34_length]; norm_num)
    · exact inRange34 29 (by rw [reps34_length]; norm_num)
    · exact inRange34 30 (by rw [reps34_length]; norm_num)
    · exact inRange34 31 (by rw [reps34_length]; norm_num)
    · exact inRange34 32 (by rw [reps34_length]; norm_num)
    · exact inRange34 33 (by rw [reps34_length]; norm_num)
    · change principalPow p6H Complex.I ∈ Set.range rep34
      rw [p6H_pow_I_eq_p3R_pow_p4A]
      exact inRange34 25 (by rw [reps34_length]; norm_num)
    · change principalPow p6K Complex.I ∈ Set.range rep34
      rw [p6K_pow_I_eq_p4C_pow_p3L]
      exact inRange34 30 (by rw [reps34_length]; norm_num)
    · change principalPow p6M Complex.I ∈ Set.range rep34
      rw [p6M_pow_I_eq_p4B_pow_p3L]
      exact inRange34 29 (by rw [reps34_length]; norm_num)
  exact hsubset38.trans hrange

end A198683Support

/-- Semantic upper bound matching the accepted OEIS value `A198683(7) = 34`. -/
theorem a198683_seven_le_thirty_four : a198683 7 ≤ 34 := by
  classical
  rw [a198683_eq_valueSet_ncard]
  let rep : Fin a198683SevenCanonicalReps.length → ℂ :=
    fun i => a198683SevenCanonicalReps.get i
  have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
    simpa [rep] using a198683_seven_subset_canonicalReps
  let repFinset : Finset ℂ := Finset.univ.image rep
  have hRangeSubset : Set.range rep ⊆ (repFinset : Set ℂ) := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    change rep i ∈ repFinset
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  calc
    (a198683ValueSet 7).ncard ≤ (Set.range rep).ncard :=
      Set.ncard_le_ncard hsubset
    _ ≤ (repFinset : Set ℂ).ncard := Set.ncard_le_ncard hRangeSubset
    _ = repFinset.card := by rw [Set.ncard_coe_finset]
    _ ≤ (Finset.univ : Finset (Fin a198683SevenCanonicalReps.length)).card :=
      Finset.card_image_le
    _ = a198683SevenCanonicalReps.length := by simp
    _ = 34 := by norm_num [a198683SevenCanonicalReps]

end

end LeanProofs
