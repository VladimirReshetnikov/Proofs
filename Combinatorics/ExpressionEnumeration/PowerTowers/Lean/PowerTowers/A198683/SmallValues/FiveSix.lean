import PowerTowers.A198683.Tower

/-!
# OEIS A198683: the values `a198683 5 = 7` and `a198683 6 = 15`

Candidate enumeration and exact separation certificates for tower sizes five
and six, over the constants and analytic facts of
`LeanProofs.A198683Tower`.
-/

namespace LeanProofs

noncomputable section

open Complex

open A198683Support

private theorem valueSet_five_eq_candidates :
    a198683ValueSet 5 =
      ({p5A, p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ) := by
  ext z
  constructor
  · intro hz
    simp only [a198683ValueSet] at hz
    rcases hz with ⟨k, x, hx, y, hy, rfl⟩
    fin_cases k
    · change x ∈ a198683ValueSet 1 at hx
      change y ∈ a198683ValueSet 4 at hy
      rw [mem_valueSet_one] at hx
      rw [mem_valueSet_four] at hy
      rcases hx
      rcases hy with rfl | rfl | rfl
      · simp [p5A]
      · simp [p5B]
      · simp [p5C]
    · change x ∈ a198683ValueSet 2 at hx
      change y ∈ a198683ValueSet 3 at hy
      rw [mem_valueSet_two] at hx
      rw [mem_valueSet_three] at hy
      rcases hx
      rcases hy with rfl | rfl
      · simp [p5D, p3L, p2]
      · simp [p5E, p3R, p2]
    · change x ∈ a198683ValueSet 3 at hx
      change y ∈ a198683ValueSet 2 at hy
      rw [mem_valueSet_three] at hx
      rw [mem_valueSet_two] at hy
      rcases hy
      rcases hx with rfl | rfl
      · simp [p5F, p3L, p2]
      · simp [p5G, p3R, p2]
    · change x ∈ a198683ValueSet 4 at hx
      change y ∈ a198683ValueSet 1 at hy
      rw [mem_valueSet_four] at hx
      rw [mem_valueSet_one] at hy
      rcases hy
      rcases hx with rfl | rfl | rfl
      · rw [p4A_pow_I_eq_p5D]
        simp
      · rw [p4B_pow_I_eq_p5E]
        simp
      · rw [p4C_pow_I_eq_p5G]
        simp
  · intro hz
    simp only [a198683ValueSet]
    rcases hz with hz | hz | hz | hz | hz | hz | hz
    · refine ⟨0, Complex.I, ?_, p4A, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_four.2 (Or.inl rfl)
      · simpa [p5A] using hz
    · refine ⟨0, Complex.I, ?_, p4B, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_four.2 (Or.inr (Or.inl rfl))
      · simpa [p5B] using hz
    · refine ⟨0, Complex.I, ?_, p4C, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))
      · simpa [p5C] using hz
    · refine ⟨1, p2, ?_, p3L, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · simpa [p5D] using hz
    · refine ⟨1, p2, ?_, p3R, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_three.2 (Or.inr rfl)
      · simpa [p5E] using hz
    · refine ⟨2, p3L, ?_, p2, ?_, ?_⟩
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · exact mem_valueSet_two.2 rfl
      · simpa [p5F] using hz
    · refine ⟨2, p3R, ?_, p2, ?_, ?_⟩
      · exact mem_valueSet_three.2 (Or.inr rfl)
      · exact mem_valueSet_two.2 rfl
      · simpa [p5G] using hz

namespace A198683Support

theorem mem_valueSet_five {z : ℂ} :
    z ∈ a198683ValueSet 5 ↔
      z = p5A ∨ z = p5B ∨ z = p5C ∨ z = p5D ∨ z = p5E ∨ z = p5F ∨ z = p5G := by
  rw [valueSet_five_eq_candidates]
  simp

theorem valueSet_six_eq_candidates :
    a198683ValueSet 6 =
      ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M,
        p6N, p6O} : Set ℂ) := by
  ext z
  constructor
  · intro hz
    simp only [a198683ValueSet] at hz
    rcases hz with ⟨k, x, hx, y, hy, rfl⟩
    fin_cases k
    · change x ∈ a198683ValueSet 1 at hx
      change y ∈ a198683ValueSet 5 at hy
      rw [mem_valueSet_one] at hx
      rw [mem_valueSet_five] at hy
      rcases hx
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [p6A]
      · simp [p6B]
      · simp [p6C]
      · simp [p6D]
      · simp [p6E]
      · simp [p6F]
      · simp [p6G]
    · change x ∈ a198683ValueSet 2 at hx
      change y ∈ a198683ValueSet 4 at hy
      rw [mem_valueSet_two] at hx
      rw [mem_valueSet_four] at hy
      rcases hx
      rcases hy with rfl | rfl | rfl
      · simp [p6H, p2]
      · simp [p6I, p2]
      · simp [p6J, p2]
    · change x ∈ a198683ValueSet 3 at hx
      change y ∈ a198683ValueSet 3 at hy
      rw [mem_valueSet_three] at hx
      rw [mem_valueSet_three] at hy
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · simp [p6K, p3L, p2]
        · simp [p6L, p3L, p3R, p2]
      · rcases hy with rfl | rfl
        · simp [p6M, p3R, p3L, p2]
        · change principalPow p3R p3R ∈
            ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L,
              p6M, p6N, p6O} : Set ℂ)
          rw [p3R_pow_p3R_eq_p6E]
          simp
    · change x ∈ a198683ValueSet 4 at hx
      change y ∈ a198683ValueSet 2 at hy
      rw [mem_valueSet_four] at hx
      rw [mem_valueSet_two] at hy
      rcases hy
      rcases hx with rfl | rfl | rfl
      · change principalPow p4A p2 ∈
          ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L,
            p6M, p6N, p6O} : Set ℂ)
        rw [p4A_pow_p2_eq_p6K]
        simp
      · change principalPow p4B p2 ∈
          ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L,
            p6M, p6N, p6O} : Set ℂ)
        rw [p4B_pow_p2_eq_p6L]
        simp
      · change principalPow p4C p2 ∈
          ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L,
            p6M, p6N, p6O} : Set ℂ)
        rw [p4C_pow_p2_eq_p6N]
        simp
    · change x ∈ a198683ValueSet 5 at hx
      change y ∈ a198683ValueSet 1 at hy
      rw [mem_valueSet_five] at hx
      rw [mem_valueSet_one] at hy
      rcases hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [p5A_pow_I_eq_p6H]
        simp
      · simp [p6O]
      · rw [p5C_pow_I_eq_p6J]
        simp
      · rw [p5D_pow_I_eq_p6M]
        simp
      · rw [p5E_pow_I_eq_p6E]
        simp
      · rw [p5F_pow_I_eq_p6N]
        simp
      · rw [p5G_pow_I_eq_p6L]
        simp
  · intro hz
    simp only [a198683ValueSet]
    rcases hz with hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz | hz
    · refine ⟨0, Complex.I, ?_, p5A, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inl rfl)
      · simpa [p6A] using hz
    · refine ⟨0, Complex.I, ?_, p5B, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inr (Or.inl rfl))
      · simpa [p6B] using hz
    · refine ⟨0, Complex.I, ?_, p5C, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inr (Or.inr (Or.inl rfl)))
      · simpa [p6C] using hz
    · refine ⟨0, Complex.I, ?_, p5D, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · simpa [p6D] using hz
    · refine ⟨0, Complex.I, ?_, p5E, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      · simpa [p6E] using hz
    · refine ⟨0, Complex.I, ?_, p5F, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      · simpa [p6F] using hz
    · refine ⟨0, Complex.I, ?_, p5G, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_five.2
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
      · simpa [p6G] using hz
    · refine ⟨1, p2, ?_, p4A, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_four.2 (Or.inl rfl)
      · simpa [p6H] using hz
    · refine ⟨1, p2, ?_, p4B, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_four.2 (Or.inr (Or.inl rfl))
      · simpa [p6I] using hz
    · refine ⟨1, p2, ?_, p4C, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))
      · simpa [p6J] using hz
    · refine ⟨2, p3L, ?_, p3L, ?_, ?_⟩
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · simpa [p6K] using hz
    · refine ⟨2, p3L, ?_, p3R, ?_, ?_⟩
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · exact mem_valueSet_three.2 (Or.inr rfl)
      · simpa [p6L] using hz
    · refine ⟨2, p3R, ?_, p3L, ?_, ?_⟩
      · exact mem_valueSet_three.2 (Or.inr rfl)
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · simpa [p6M] using hz
    · refine ⟨3, p4C, ?_, p2, ?_, ?_⟩
      · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))
      · exact mem_valueSet_two.2 rfl
      · simpa [p6N] using hz
    · refine ⟨4, p5B, ?_, Complex.I, ?_, ?_⟩
      · exact mem_valueSet_five.2 (Or.inr (Or.inl rfl))
      · exact mem_valueSet_one.2 rfl
      · simpa [p6O] using hz

theorem mem_valueSet_six {z : ℂ} :
    z ∈ a198683ValueSet 6 ↔
      z = p6A ∨ z = p6B ∨ z = p6C ∨ z = p6D ∨ z = p6E ∨ z = p6F ∨ z = p6G ∨
        z = p6H ∨ z = p6I ∨ z = p6J ∨ z = p6K ∨ z = p6L ∨ z = p6M ∨
        z = p6N ∨ z = p6O := by
  rw [valueSet_six_eq_candidates]
  simp

end A198683Support

/-- Semantic upper bound for the next OEIS value: `A198683(5) <= 7`. -/
theorem a198683_five_le_seven : a198683 5 ≤ 7 := by
  rw [a198683_eq_valueSet_ncard, valueSet_five_eq_candidates]
  have hG : ({p5G} : Set ℂ).ncard ≤ 1 := by simp
  have hFG : ({p5F, p5G} : Set ℂ).ncard ≤ 2 := by
    calc
      ({p5F, p5G} : Set ℂ).ncard ≤ ({p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5F ({p5G} : Set ℂ)
      _ ≤ 2 := by linarith
  have hEFG : ({p5E, p5F, p5G} : Set ℂ).ncard ≤ 3 := by
    calc
      ({p5E, p5F, p5G} : Set ℂ).ncard ≤ ({p5F, p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5E ({p5F, p5G} : Set ℂ)
      _ ≤ 3 := by linarith
  have hDEFG : ({p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤ 4 := by
    calc
      ({p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤
          ({p5E, p5F, p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5D ({p5E, p5F, p5G} : Set ℂ)
      _ ≤ 4 := by linarith
  have hCDEFG : ({p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤ 5 := by
    calc
      ({p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤
          ({p5D, p5E, p5F, p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5C ({p5D, p5E, p5F, p5G} : Set ℂ)
      _ ≤ 5 := by linarith
  have hBCDEFG : ({p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤ 6 := by
    calc
      ({p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤
          ({p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5B ({p5C, p5D, p5E, p5F, p5G} : Set ℂ)
      _ ≤ 6 := by linarith
  calc
    ({p5A, p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard ≤
        ({p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ).ncard + 1 :=
        Set.ncard_insert_le p5A ({p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ)
    _ ≤ 7 := by linarith

/-- `A198683(5) = 7`. -/
theorem a198683_five : a198683 5 = 7 := by
  rw [a198683_eq_valueSet_ncard, valueSet_five_eq_candidates]
  have hA :
      p5A ∉ ({p5B, p5C, p5D, p5E, p5F, p5G} : Set ℂ) := by
    simp [p5A_ne_p5B, p5A_ne_p5C, p5A_ne_p5D, p5A_ne_p5E, p5A_ne_p5F,
      p5A_ne_p5G]
  have hB :
      p5B ∉ ({p5C, p5D, p5E, p5F, p5G} : Set ℂ) := by
    simp [p5B_ne_p5C, p5D_ne_p5B.symm, p5B_ne_p5E, p5B_ne_p5F, p5B_ne_p5G]
  have hC :
      p5C ∉ ({p5D, p5E, p5F, p5G} : Set ℂ) := by
    simp [p5D_ne_p5C.symm, p5C_ne_p5E, p5F_ne_p5C.symm, p5G_ne_p5C.symm]
  have hD :
      p5D ∉ ({p5E, p5F, p5G} : Set ℂ) := by
    simp [p5D_ne_p5E, p5D_ne_p5F, p5D_ne_p5G]
  have hE :
      p5E ∉ ({p5F, p5G} : Set ℂ) := by
    simp [p5F_ne_p5E.symm, p5G_ne_p5E.symm]
  have hF :
      p5F ∉ ({p5G} : Set ℂ) := by
    simp [p5G_ne_p5F.symm]
  rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB,
    Set.ncard_insert_of_notMem hC, Set.ncard_insert_of_notMem hD,
    Set.ncard_insert_of_notMem hE, Set.ncard_insert_of_notMem hF]
  simp

/-- Semantic upper bound for the next OEIS value: `A198683(6) <= 15`. -/
theorem a198683_six_le_fifteen : a198683 6 ≤ 15 := by
  classical
  rw [a198683_eq_valueSet_ncard, valueSet_six_eq_candidates]
  let reps : List ℂ :=
    [p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O]
  have hsubset :
      ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N,
        p6O} : Set ℂ) ⊆ (reps.toFinset : Set ℂ) := by
    intro z hz
    simpa [reps] using hz
  calc
    ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N,
        p6O} : Set ℂ).ncard ≤ (reps.toFinset : Set ℂ).ncard :=
      Set.ncard_le_ncard hsubset
    _ = reps.toFinset.card := by rw [Set.ncard_coe_finset]
    _ ≤ reps.length := List.toFinset_card_le reps
    _ = 15 := by norm_num [reps]

/-- `A198683(6) = 15`. -/
theorem a198683_six : a198683 6 = 15 := by
  rw [a198683_eq_valueSet_ncard, valueSet_six_eq_candidates]
  have hA :
      p6A ∉ ({p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M,
        p6N, p6O} : Set ℂ) := by
    simp [p6A_ne_p6B, p6A_ne_p6C, p6A_ne_p6D, p6A_ne_p6E, p6A_ne_p6F,
      p6A_ne_p6G, p6K_ne_p6A.symm,
      ne_of_im_pos_of_im_neg p6A_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6A_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6A_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6A_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6A_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6A_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6A_im_pos p6O_im_zero]
  have hB :
      p6B ∉ ({p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N,
        p6O} : Set ℂ) := by
    simp [p6B_ne_p6C, p6B_ne_p6D, p6B_ne_p6E, p6B_ne_p6F, p6B_ne_p6G,
      p6K_ne_p6B.symm,
      ne_of_im_pos_of_im_neg p6B_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6B_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6B_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6B_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6B_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6B_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6B_im_pos p6O_im_zero]
  have hC :
      p6C ∉ ({p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N,
        p6O} : Set ℂ) := by
    simp [p6C_ne_p6D, p6C_ne_p6E, p6C_ne_p6F, p6C_ne_p6G,
      p6K_ne_p6C.symm,
      ne_of_im_pos_of_im_neg p6C_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6C_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6C_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6C_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6C_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6C_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6C_im_pos p6O_im_zero]
  have hD :
      p6D ∉ ({p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N,
        p6O} : Set ℂ) := by
    simp [p6D_ne_p6E, p6D_ne_p6F, p6D_ne_p6G, p6K_ne_p6D.symm,
      ne_of_im_pos_of_im_neg p6D_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6D_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6D_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6D_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6D_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6D_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6D_im_pos p6O_im_zero]
  have hE :
      p6E ∉ ({p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6E_ne_p6F, p6E_ne_p6G, p6I_ne_p6E.symm, p6E_ne_p6J,
      p6E_ne_p6L, p6E_ne_p6N, p6E_ne_p6O,
      (ne_of_im_neg_of_im_zero p6H_im_neg p6E_im_zero).symm,
      (ne_of_im_neg_of_im_zero p6M_im_neg p6E_im_zero).symm,
      (ne_of_im_pos_of_im_zero p6K_im_pos p6E_im_zero).symm]
  have hF :
      p6F ∉ ({p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6F_ne_p6G, p6K_ne_p6F.symm,
      ne_of_im_pos_of_im_neg p6F_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6F_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6F_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6F_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6F_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6F_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6F_im_pos p6O_im_zero]
  have hG :
      p6G ∉ ({p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6K_ne_p6G.symm,
      ne_of_im_pos_of_im_neg p6G_im_pos p6H_im_neg,
      ne_of_im_pos_of_im_neg p6G_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6G_im_pos p6I_im_zero,
      ne_of_im_pos_of_im_zero p6G_im_pos p6J_im_zero,
      ne_of_im_pos_of_im_zero p6G_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6G_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6G_im_pos p6O_im_zero]
  have hH :
      p6H ∉ ({p6I, p6J, p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6H_ne_p6M,
      ne_of_im_neg_of_im_zero p6H_im_neg p6I_im_zero,
      ne_of_im_neg_of_im_zero p6H_im_neg p6J_im_zero,
      ne_of_im_neg_of_im_zero p6H_im_neg p6L_im_zero,
      ne_of_im_neg_of_im_zero p6H_im_neg p6N_im_zero,
      ne_of_im_neg_of_im_zero p6H_im_neg p6O_im_zero,
      (ne_of_im_pos_of_im_neg p6K_im_pos p6H_im_neg).symm]
  have hI :
      p6I ∉ ({p6J, p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6I_ne_p6J, p6I_ne_p6L, p6I_ne_p6N, p6I_ne_p6O,
      (ne_of_im_pos_of_im_zero p6K_im_pos p6I_im_zero).symm,
      (ne_of_im_neg_of_im_zero p6M_im_neg p6I_im_zero).symm]
  have hJ :
      p6J ∉ ({p6K, p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [p6J_ne_p6L, p6J_ne_p6N, p6O_ne_p6J.symm,
      (ne_of_im_pos_of_im_zero p6K_im_pos p6J_im_zero).symm,
      (ne_of_im_neg_of_im_zero p6M_im_neg p6J_im_zero).symm]
  have hK :
      p6K ∉ ({p6L, p6M, p6N, p6O} : Set ℂ) := by
    simp [ne_of_im_pos_of_im_neg p6K_im_pos p6M_im_neg,
      ne_of_im_pos_of_im_zero p6K_im_pos p6L_im_zero,
      ne_of_im_pos_of_im_zero p6K_im_pos p6N_im_zero,
      ne_of_im_pos_of_im_zero p6K_im_pos p6O_im_zero]
  have hL :
      p6L ∉ ({p6M, p6N, p6O} : Set ℂ) := by
    simp [p6N_ne_p6L.symm, p6O_ne_p6L.symm,
      (ne_of_im_neg_of_im_zero p6M_im_neg p6L_im_zero).symm]
  have hM :
      p6M ∉ ({p6N, p6O} : Set ℂ) := by
    simp [ne_of_im_neg_of_im_zero p6M_im_neg p6N_im_zero,
      ne_of_im_neg_of_im_zero p6M_im_neg p6O_im_zero]
  have hN :
      p6N ∉ ({p6O} : Set ℂ) := by
    simp [p6O_ne_p6N.symm]
  rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB,
    Set.ncard_insert_of_notMem hC, Set.ncard_insert_of_notMem hD,
    Set.ncard_insert_of_notMem hE, Set.ncard_insert_of_notMem hF,
    Set.ncard_insert_of_notMem hG, Set.ncard_insert_of_notMem hH,
    Set.ncard_insert_of_notMem hI, Set.ncard_insert_of_notMem hJ,
    Set.ncard_insert_of_notMem hK, Set.ncard_insert_of_notMem hL,
    Set.ncard_insert_of_notMem hM, Set.ncard_insert_of_notMem hN]
  simp

end

end LeanProofs
