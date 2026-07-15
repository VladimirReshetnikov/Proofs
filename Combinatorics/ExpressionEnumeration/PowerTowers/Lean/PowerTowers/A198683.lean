import PowerTowers.A198683.SmallValues.SevenUpper

/-!
# Initial values of OEIS A198683

OEIS A198683 counts the distinct principal values of all binary
parenthesizations of `i^i^...^i`.  The canonical lexical definition and the
supporting analytic corpus live in `LeanProofs.A198683Tower`; the `n = 5, 6`
values in `LeanProofs.A198683FiveSix`; and the `n = 7` upper bound in
`LeanProofs.A198683SevenUpper`.  This module proves the matching lower bound
`thirty_four_le_a198683_seven`, assembles `a198683_seven : a198683 7 = 34`,
and restates the historical intermediate bounds as corollaries.

The accepted OEIS data currently run through `n = 11`; `n = 12` is deliberately
not included in the OEIS data field because the local corpus records it as
still awaiting a proof-quality certificate.
-/

namespace LeanProofs

noncomputable section

open Complex

open A198683Support

/-! ## Seed family: the six-candidate set and its iᶻ image

The fifteen-element six-candidate set, its cardinality and geometric bounds, and the first seven principal values obtained as its `principalPow I` image. -/

private noncomputable def a198683SixCandidateSet : Set ℂ :=
  ({p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M,
    p6N, p6O} : Set ℂ)

private theorem a198683SixCandidateSet_ncard :
    a198683SixCandidateSet.ncard = 15 := by
  have hsix := a198683_six
  rw [a198683_eq_valueSet_ncard, valueSet_six_eq_candidates] at hsix
  simpa [a198683SixCandidateSet] using hsix

private theorem re_bounds_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -2 < z.re ∧ z.re ≤ 2 := by
  have habs : |z.re| ≤ 1 := (Complex.abs_re_le_norm z).trans hz
  exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩

private theorem re_bounds_of_norm_lt_two {z : ℂ} (hz : ‖z‖ < 2) :
    -2 < z.re ∧ z.re ≤ 2 := by
  have hlt : |z.re| < 2 := (Complex.abs_re_le_norm z).trans_lt hz
  exact ⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩

private theorem a198683SixCandidateSet_re_bounds {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    -2 < z.re ∧ z.re ≤ 2 := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact re_bounds_of_norm_le_one p6A_norm_le_one
  · exact re_bounds_of_norm_le_one p6B_norm_le_one
  · exact re_bounds_of_norm_le_one p6C_norm_le_one
  · exact re_bounds_of_norm_lt_two p6D_norm_lt_two
  · exact re_bounds_of_norm_le_one p6E_norm_le_one
  · exact re_bounds_of_norm_le_one p6F_norm_le_one
  · exact re_bounds_of_norm_lt_two p6G_norm_lt_two
  · exact re_bounds_of_norm_le_one p6H_norm_le_one
  · exact re_bounds_of_norm_le_one p6I_norm_le_one
  · exact re_bounds_of_norm_le_one p6J_norm_le_one
  · exact re_bounds_of_norm_le_one p6K_norm_le_one
  · exact re_bounds_of_norm_lt_two p6L_norm_lt_two
  · exact re_bounds_of_norm_lt_two p6M_norm_lt_two
  · exact re_bounds_of_norm_le_one p6N_norm_le_one
  · exact re_bounds_of_norm_le_one p6O_norm_le_one

private theorem re_lt_two_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    z.re < 2 := by
  linarith [(Complex.re_le_norm z).trans hz]

private theorem a198683SixCandidateSet_re_pos {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) : 0 < z.re := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact p6A_re_pos
  · exact p6B_re_pos
  · exact p6C_re_pos
  · exact p6D_re_pos
  · exact p6E_re_pos
  · exact p6F_re_pos
  · exact p6G_re_pos
  · exact p6H_re_pos
  · exact p6I_re_pos
  · exact p6J_re_pos
  · exact p6K_re_pos
  · exact p6L_re_pos
  · exact p6M_re_pos
  · exact p6N_re_pos
  · exact p6O_re_pos

private theorem a198683SixCandidateSet_re_lt_two {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) : z.re < 2 := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact re_lt_two_of_norm_le_one p6A_norm_le_one
  · exact re_lt_two_of_norm_le_one p6B_norm_le_one
  · exact re_lt_two_of_norm_le_one p6C_norm_le_one
  · exact (Complex.re_le_norm p6D).trans_lt p6D_norm_lt_two
  · exact re_lt_two_of_norm_le_one p6E_norm_le_one
  · exact re_lt_two_of_norm_le_one p6F_norm_le_one
  · exact (Complex.re_le_norm p6G).trans_lt p6G_norm_lt_two
  · exact re_lt_two_of_norm_le_one p6H_norm_le_one
  · exact re_lt_two_of_norm_le_one p6I_norm_le_one
  · exact re_lt_two_of_norm_le_one p6J_norm_le_one
  · exact re_lt_two_of_norm_le_one p6K_norm_le_one
  · exact (Complex.re_le_norm p6L).trans_lt p6L_norm_lt_two
  · exact (Complex.re_le_norm p6M).trans_lt p6M_norm_lt_two
  · exact re_lt_two_of_norm_le_one p6N_norm_le_one
  · exact re_lt_two_of_norm_le_one p6O_norm_le_one

private theorem I_pow_im_pos_of_re_pos_of_re_lt_two {z : ℂ}
    (hzpos : 0 < z.re) (hzlt : z.re < 2) :
    0 < (principalPow Complex.I z).im := by
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos, hzpos, hzlt]

private theorem I_pow_image_sixCandidateSet_im_pos {z : ℂ}
    (hz : z ∈ (fun w : ℂ => principalPow Complex.I w) '' a198683SixCandidateSet) :
    0 < z.im := by
  rcases hz with ⟨w, hw, rfl⟩
  exact I_pow_im_pos_of_re_pos_of_re_lt_two
    (a198683SixCandidateSet_re_pos hw) (a198683SixCandidateSet_re_lt_two hw)

private theorem a198683SixCandidateSet_subset_six :
    a198683SixCandidateSet ⊆ a198683ValueSet 6 := by
  intro z hz
  rw [valueSet_six_eq_candidates]
  simpa [a198683SixCandidateSet] using hz

private theorem I_pow_injOn_a198683SixCandidateSet :
    Set.InjOn (fun z : ℂ => principalPow Complex.I z) a198683SixCandidateSet := by
  intro x hx y hy hxy
  have hxre := a198683SixCandidateSet_re_bounds hx
  have hyre := a198683SixCandidateSet_re_bounds hy
  exact I_pow_inj_of_re_mem_two hxre.1 hxre.2 hyre.1 hyre.2 hxy

private theorem I_pow_image_sixCandidateSet_subset_seven :
    (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet ⊆
      a198683ValueSet 7 := by
  rintro z ⟨x, hx, rfl⟩
  simp only [a198683ValueSet]
  refine ⟨0, Complex.I, ?_, x, ?_, rfl⟩
  · exact mem_valueSet_one.2 rfl
  · exact a198683SixCandidateSet_subset_six hx

/-! ## Second family: the p2ᶻ negative-exponent image

The five-element negative-exponent set and the further principal values produced as its `principalPow p2` image. -/

private theorem p5B_im_pos :
    0 < p5B.im := by
  rw [p5B_eq_exp_beta]
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
  apply Real.sin_pos_of_mem_Ioo
  exact ⟨beta_pos, beta_lt_angleE.trans angleE_lt_pi⟩

private theorem p2_pow_inj_of_norm_le_one {x y : ℂ}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    principalPow p2 x = principalPow p2 y → x = y := by
  intro h
  dsimp [principalPow] at h
  rw [log_p2_eq] at h
  have hxabs : |x.im| ≤ 1 := (Complex.abs_im_le_norm x).trans hx
  have hyabs : |y.im| ≤ 1 := (Complex.abs_im_le_norm y).trans hy
  have hxge : -1 ≤ x.im := (abs_le.mp hxabs).1
  have hxle : x.im ≤ 1 := (abs_le.mp hxabs).2
  have hyge : -1 ≤ y.im := (abs_le.mp hyabs).1
  have hyle : y.im ≤ 1 := (abs_le.mp hyabs).2
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (-(Real.pi / 2) : ℂ) * x)
    (y := (-(Real.pi / 2) : ℂ) * y)
    (by simp [Complex.mul_im]; nlinarith [Real.pi_pos, hxle])
    (by simp [Complex.mul_im]; nlinarith [Real.pi_pos, hxge])
    (by simp [Complex.mul_im]; nlinarith [Real.pi_pos, hyle])
    (by simp [Complex.mul_im]; nlinarith [Real.pi_pos, hyge])
    h
  have hc : (-(Real.pi / 2) : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  exact mul_left_cancel₀ hc heq

private theorem p2_pow_im_neg_of_im_pos_of_norm_le_one {z : ℂ}
    (hzpos : 0 < z.im) (hznorm : ‖z‖ ≤ 1) :
    (principalPow p2 z).im < 0 := by
  dsimp [principalPow]
  rw [log_p2_eq, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, hzpos]
  · have hle : z.im ≤ 1 := (abs_le.mp ((Complex.abs_im_le_norm z).trans hznorm)).2
    nlinarith [Real.pi_pos, hle]

private noncomputable def a198683SevenP2NegativeExponents : Set ℂ :=
  ({p5A, p5B, p5C, p5E, p5F} : Set ℂ)

private theorem a198683SevenP2NegativeExponents_ncard :
    a198683SevenP2NegativeExponents.ncard = 5 := by
  have hA : p5A ∉ ({p5B, p5C, p5E, p5F} : Set ℂ) := by
    simp [p5A_ne_p5B, p5A_ne_p5C, p5A_ne_p5E, p5A_ne_p5F]
  have hB : p5B ∉ ({p5C, p5E, p5F} : Set ℂ) := by
    simp [p5B_ne_p5C, p5B_ne_p5E, p5B_ne_p5F]
  have hC : p5C ∉ ({p5E, p5F} : Set ℂ) := by
    simp [p5C_ne_p5E, p5F_ne_p5C.symm]
  have hE : p5E ∉ ({p5F} : Set ℂ) := by
    simp [p5F_ne_p5E.symm]
  dsimp [a198683SevenP2NegativeExponents]
  rw [Set.ncard_insert_of_notMem hA, Set.ncard_insert_of_notMem hB,
    Set.ncard_insert_of_notMem hC, Set.ncard_insert_of_notMem hE]
  simp

private theorem a198683SevenP2NegativeExponents_norm_le_one {z : ℂ}
    (hz : z ∈ a198683SevenP2NegativeExponents) : ‖z‖ ≤ 1 := by
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact p5A_norm_le_one
  · exact p5B_norm_le_one
  · exact p5C_norm_le_one
  · exact p5E_norm_le_one
  · exact p5F_norm_le_one

private theorem a198683SevenP2NegativeExponents_im_pos {z : ℂ}
    (hz : z ∈ a198683SevenP2NegativeExponents) : 0 < z.im := by
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact p5A_im_pos
  · exact p5B_im_pos
  · exact p5C_im_pos
  · simp [p5E_eq_I]
  · exact p5F_im_pos

private theorem a198683SevenP2NegativeExponents_subset_five :
    a198683SevenP2NegativeExponents ⊆ a198683ValueSet 5 := by
  intro z hz
  rw [mem_valueSet_five]
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

private theorem p2_pow_injOn_p2NegativeExponents :
    Set.InjOn (fun z : ℂ => principalPow p2 z) a198683SevenP2NegativeExponents := by
  intro x hx y hy hxy
  exact p2_pow_inj_of_norm_le_one
    (a198683SevenP2NegativeExponents_norm_le_one hx)
    (a198683SevenP2NegativeExponents_norm_le_one hy) hxy

private theorem p2_pow_image_p2NegativeExponents_subset_seven :
    (fun z : ℂ => principalPow p2 z) '' a198683SevenP2NegativeExponents ⊆
      a198683ValueSet 7 := by
  rintro z ⟨x, hx, rfl⟩
  simp only [a198683ValueSet]
  refine ⟨1, p2, ?_, x, ?_, rfl⟩
  · exact mem_valueSet_two.2 rfl
  · exact a198683SevenP2NegativeExponents_subset_five hx

private theorem p2_pow_image_p2NegativeExponents_im_neg {z : ℂ}
    (hz : z ∈ (fun w : ℂ => principalPow p2 w) '' a198683SevenP2NegativeExponents) :
    z.im < 0 := by
  rcases hz with ⟨w, hw, rfl⟩
  exact p2_pow_im_neg_of_im_pos_of_norm_le_one
    (a198683SevenP2NegativeExponents_im_pos hw)
    (a198683SevenP2NegativeExponents_norm_le_one hw)

private theorem p2_pow_norm_le_one_of_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) :
    ‖principalPow p2 z‖ ≤ 1 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p2_eq]
  simp [Complex.mul_re]
  exact mul_nonneg (by positivity) hz

private theorem a198683SevenP2NegativeExponents_re_nonneg {z : ℂ}
    (hz : z ∈ a198683SevenP2NegativeExponents) : 0 ≤ z.re := by
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · exact p5A_re_pos.le
  · exact p5B_re_pos.le
  · exact p5C_re_pos.le
  · simp [p5E_eq_I]
  · exact p5F_re_pos.le

private theorem p2_pow_image_p2NegativeExponents_norm_le_one {z : ℂ}
    (hz : z ∈ (fun w : ℂ => principalPow p2 w) '' a198683SevenP2NegativeExponents) :
    ‖z‖ ≤ 1 := by
  rcases hz with ⟨w, hw, rfl⟩
  exact p2_pow_norm_le_one_of_re_nonneg
    (a198683SevenP2NegativeExponents_re_nonneg hw)

/-! ## Off-unit-circle witnesses (p3R^p4A, p4B^p3L)

New principal values separated from the two image families purely by their modulus. -/

private theorem p3R_pow_p4A_im_neg :
    (principalPow p3R p4A).im < 0 := by
  dsimp [principalPow]
  rw [log_p3R_eq, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, p4A_re_pos]
  · nlinarith [Real.pi_pos, p4A_re_lt_one]

private theorem p3R_pow_p4A_norm_gt_one :
    1 < ‖principalPow p3R p4A‖ := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p3R_eq]
  simp [Complex.mul_re, Complex.mul_im]
  nlinarith [Real.pi_pos, p4A_im_pos]

private theorem p3R_pow_p4A_mem_seven :
    principalPow p3R p4A ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨2, p3R, ?_, p4A, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inr rfl)
  · exact mem_valueSet_four.2 (Or.inl rfl)

private theorem I_pow_norm_eq_one_of_im_zero {z : ℂ} (hz : z.im = 0) :
    ‖principalPow Complex.I z‖ = 1 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im, hz]

private theorem p4B_pow_p3L_norm_gt_four :
    4 < ‖principalPow p4B p3L‖ := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p4B_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  apply Real.exp_lt_exp.mpr
  have hlog4 : Real.log 4 < (7 : ℝ) / 5 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith [Real.log_two_lt_d9]
  have harg : (7 : ℝ) / 5 < Real.pi / 2 * Real.cos theta := by
    nlinarith [Real.pi_gt_d2, cos_theta_gt_seventeen_div_eighteen]
  exact hlog4.trans harg

private theorem p4B_pow_p3L_norm_lt_five :
    ‖principalPow p4B p3L‖ < 5 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p4B_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have harg : Real.pi / 2 * Real.cos theta < Real.pi / 2 := by
    simpa using
      mul_lt_mul_of_pos_left cos_theta_lt_one (show 0 < Real.pi / 2 by positivity)
  exact (Real.exp_lt_exp.mpr harg).trans exp_pi_div_two_lt_five

private theorem p4B_pow_p3L_im_pos :
    0 < (principalPow p4B p3L).im := by
  dsimp [principalPow]
  rw [log_p4B_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, sin_theta_pos]
  · have hsin_le_one : Real.sin theta ≤ 1 := Real.sin_le_one theta
    nlinarith [Real.pi_pos, hsin_le_one]

private theorem p4B_pow_p3L_mem_seven :
    principalPow p4B p3L ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨3, p4B, ?_, p3L, ?_, rfl⟩
  · exact mem_valueSet_four.2 (Or.inr (Or.inl rfl))
  · exact mem_valueSet_three.2 (Or.inl rfl)

private theorem neg_p6H_im_lt_seven_div_eighth :
    -p6H.im < (7 : ℝ) / 8 := by
  dsimp [p6H, principalPow]
  rw [log_p2_eq, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  have hexp_le_one :
      Real.exp (-(Real.pi / 2 * p4A.re)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, p4A_re_pos])
  have harg_pos : 0 < Real.pi / 2 * p4A.im := by
    nlinarith [Real.pi_pos, p4A_im_pos]
  have harg_lt_pi_div_three : Real.pi / 2 * p4A.im < Real.pi / 3 := by
    nlinarith [Real.pi_pos, p4A_im_lt_two_div_three]
  have hsin_lt_pi_div_three :
      Real.sin (Real.pi / 2 * p4A.im) < Real.sin (Real.pi / 3) := by
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := Real.pi / 2 * p4A.im) (y := Real.pi / 3)
      (by linarith [Real.pi_pos, harg_pos]) (by linarith [Real.pi_pos]) harg_lt_pi_div_three
  have hsin_lt : Real.sin (Real.pi / 2 * p4A.im) < (7 : ℝ) / 8 := by
    rw [Real.sin_pi_div_three] at hsin_lt_pi_div_three
    have hsqrt : Real.sqrt 3 < (7 : ℝ) / 4 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (7 : ℝ) / 4)]
      norm_num
    nlinarith
  have hsin_nonneg : 0 ≤ Real.sin (Real.pi / 2 * p4A.im) :=
    (Real.sin_pos_of_mem_Ioo ⟨harg_pos, by linarith [Real.pi_pos, harg_lt_pi_div_three]⟩).le
  have hmul_le :
      Real.exp (-(Real.pi / 2 * p4A.re)) *
          Real.sin (Real.pi / 2 * p4A.im) ≤
        1 * Real.sin (Real.pi / 2 * p4A.im) :=
    mul_le_mul_of_nonneg_right hexp_le_one hsin_nonneg
  nlinarith [hmul_le, hsin_lt]

private theorem I_pow_p6H_norm_lt_four :
    ‖principalPow Complex.I p6H‖ < 4 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  apply Real.exp_lt_exp.mpr
  have hlog4 :
      Real.pi / 2 * ((7 : ℝ) / 8) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    nlinarith [Real.pi_lt_d2, Real.log_two_gt_d9]
  nlinarith [Real.pi_pos, neg_p6H_im_lt_seven_div_eighth, hlog4]

private theorem neg_p6M_im_gt_eleven_div_ten :
    (11 : ℝ) / 10 < -p6M.im := by
  dsimp [p6M, principalPow]
  rw [log_p3R_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hu_gt : (1 : ℝ) / 3 < Real.pi / 2 * Real.sin theta := by
    nlinarith [Real.pi_gt_d2, sin_theta_gt_seven_div_thirty]
  have hexp_gt : (4 : ℝ) / 3 < Real.exp (Real.pi / 2 * Real.sin theta) := by
    have h := Real.add_one_lt_exp (by nlinarith [hu_gt] :
      Real.pi / 2 * Real.sin theta ≠ 0)
    nlinarith [h, hu_gt]
  have hsin_gt :
      (6 : ℝ) / 7 < Real.sin (Real.pi / 2 * Real.cos theta) := by
    rw [show Real.pi / 2 * Real.cos theta = Real.pi / 2 - thetaDelta by
      dsimp [thetaDelta]
      ring]
    rw [Real.sin_pi_div_two_sub]
    exact cos_thetaDelta_gt_six_div_seven
  have hprod :
      (4 : ℝ) / 3 * ((6 : ℝ) / 7) <
        Real.exp (Real.pi / 2 * Real.sin theta) *
          Real.sin (Real.pi / 2 * Real.cos theta) :=
    mul_lt_mul hexp_gt hsin_gt.le (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem I_pow_p6M_norm_gt_five :
    5 < ‖principalPow Complex.I p6M‖ := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  apply Real.exp_lt_exp.mpr
  have hlog : Real.log 5 < Real.pi / 2 * ((11 : ℝ) / 10) := by
    nlinarith [Real.pi_gt_d2, Real.log_five_lt_d9]
  nlinarith [Real.pi_pos, neg_p6M_im_gt_eleven_div_ten, hlog]

private theorem ne_of_norm_lt_norm_gt {z w : ℂ} {r : ℝ}
    (hz : ‖z‖ < r) (hw : r < ‖w‖) : z ≠ w := by
  intro h
  rw [h] at hz
  linarith

private theorem ne_of_norm_gt_norm_lt {z w : ℂ} {r : ℝ}
    (hz : r < ‖z‖) (hw : ‖w‖ < r) : z ≠ w := by
  intro h
  rw [h] at hz
  linarith

private theorem p4B_pow_p3L_notMem_I_pow_sixCandidateSet :
    principalPow p4B p3L ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hzw⟩
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6A_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6B_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6C_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6D_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · have hlt : ‖principalPow Complex.I p6E‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6E_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6F_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6G_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      I_pow_p6H_norm_lt_four p4B_pow_p3L_norm_gt_four) hzw
  · have hlt : ‖principalPow Complex.I p6I‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6I_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw
  · have hlt : ‖principalPow Complex.I p6J‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6J_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_lt_norm_gt (r := 4)
      ((I_pow_norm_lt_one_of_im_pos p6K_im_pos).trans (by norm_num))
      p4B_pow_p3L_norm_gt_four) hzw
  · have hlt : ‖principalPow Complex.I p6L‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6L_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw
  · exact (ne_of_norm_gt_norm_lt (r := 5)
      I_pow_p6M_norm_gt_five p4B_pow_p3L_norm_lt_five) hzw
  · have hlt : ‖principalPow Complex.I p6N‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6N_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw
  · have hlt : ‖principalPow Complex.I p6O‖ < 4 := by
      rw [I_pow_norm_eq_one_of_im_zero p6O_im_zero]
      norm_num
    exact (ne_of_norm_lt_norm_gt (r := 4) hlt p4B_pow_p3L_norm_gt_four) hzw

/-! ## The principal value i

Identifying `i` itself as a principal value and proving it distinct from the earlier images through the `ne_one` lemmas. -/

private theorem principalPow_I_one_eq_I :
    principalPow Complex.I (1 : ℂ) = Complex.I := by
  dsimp [principalPow]
  rw [log_I_real]
  simp

private theorem p3L_pow_p4B_eq_I :
    principalPow p3L p4B = Complex.I := by
  dsimp [principalPow]
  rw [log_p3L_eq, p4B_eq_exp_pi_div_two]
  rw [show ((theta : ℂ) * Complex.I) * (Real.exp (Real.pi / 2) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    have htheta_mul : theta * Real.exp (Real.pi / 2) = Real.pi / 2 := by
      dsimp [theta, rho]
      rw [Real.exp_neg]
      field_simp [(Real.exp_pos (Real.pi / 2)).ne']
    have hexp_im : (Complex.exp ((Real.pi : ℂ) / 2)).im = 0 := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_num]
      exact Complex.exp_ofReal_im (Real.pi / 2)
    have hexp_re : (Complex.exp ((Real.pi : ℂ) / 2)).re = Real.exp (Real.pi / 2) := by
      rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_num]
      exact Complex.exp_ofReal_re (Real.pi / 2)
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, hexp_im]
    · simp [Complex.mul_re, Complex.mul_im, hexp_re, htheta_mul]]
  simp

private theorem I_mem_seven :
    Complex.I ∈ a198683ValueSet 7 := by
  rw [← p3L_pow_p4B_eq_I]
  simp only [a198683ValueSet]
  refine ⟨2, p3L, ?_, p4B, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inl rfl)
  · exact mem_valueSet_four.2 (Or.inr (Or.inl rfl))

private theorem p6E_norm_lt_one_strict :
    ‖p6E‖ < 1 := by
  rw [p6E_eq_exp_neg_pi_div_two]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])

private theorem p6I_norm_lt_one_strict :
    ‖p6I‖ < 1 := by
  rw [p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr
    (by nlinarith [Real.pi_pos, Real.exp_pos (Real.pi / 2)])

private theorem p6J_norm_lt_one_strict :
    ‖p6J‖ < 1 := by
  rw [p6J_eq_exp_neg_angleC]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr (by linarith [angleC_pos])

private theorem p6L_norm_gt_one_strict :
    1 < ‖p6L‖ := by
  rw [p6L_eq_exp_theta]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  simpa using (Real.exp_lt_exp.mpr theta_pos)

private theorem p6N_norm_lt_one_strict :
    ‖p6N‖ < 1 := by
  rw [p6N_eq_exp_neg_angleF]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr (by linarith [angleF_pos])

private theorem p6O_norm_lt_one_strict :
    ‖p6O‖ < 1 := by
  rw [p6O_eq_exp_neg_beta]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_lt_one_iff.mpr (by linarith [beta_pos])

private theorem ne_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    z ≠ 1 := by
  intro h
  rw [h] at hz
  norm_num at hz

private theorem ne_one_of_norm_gt_one {z : ℂ} (hz : 1 < ‖z‖) :
    z ≠ 1 := by
  intro h
  rw [h] at hz
  norm_num at hz

private theorem a198683SixCandidateSet_ne_one {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) : z ≠ 1 := by
  have hone_im : ((1 : ℂ).im = 0) := by norm_num
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ne_of_im_pos_of_im_zero p6A_im_pos hone_im
  · exact ne_of_im_pos_of_im_zero p6B_im_pos hone_im
  · exact ne_of_im_pos_of_im_zero p6C_im_pos hone_im
  · exact ne_of_im_pos_of_im_zero p6D_im_pos hone_im
  · exact ne_one_of_norm_lt_one p6E_norm_lt_one_strict
  · exact ne_of_im_pos_of_im_zero p6F_im_pos hone_im
  · exact ne_of_im_pos_of_im_zero p6G_im_pos hone_im
  · exact ne_of_im_neg_of_im_zero p6H_im_neg hone_im
  · exact ne_one_of_norm_lt_one p6I_norm_lt_one_strict
  · exact ne_one_of_norm_lt_one p6J_norm_lt_one_strict
  · exact ne_of_im_pos_of_im_zero p6K_im_pos hone_im
  · exact ne_one_of_norm_gt_one p6L_norm_gt_one_strict
  · exact ne_of_im_neg_of_im_zero p6M_im_neg hone_im
  · exact ne_one_of_norm_lt_one p6N_norm_lt_one_strict
  · exact ne_one_of_norm_lt_one p6O_norm_lt_one_strict

private theorem I_notMem_I_pow_sixCandidateSet :
    Complex.I ∉ (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  have hzre := a198683SixCandidateSet_re_bounds hz
  change principalPow Complex.I z = Complex.I at hpow
  have hpow_one : principalPow Complex.I z = principalPow Complex.I (1 : ℂ) := by
    rw [hpow, principalPow_I_one_eq_I]
  exact a198683SixCandidateSet_ne_one hz
    (I_pow_inj_of_re_mem_two hzre.1 hzre.2 (by norm_num) (by norm_num) hpow_one)

/-! ## Unit-modulus witnesses ordered by cos-angle (p3R^p4B, p3R^p4C, p5G^p2)

Further unit-circle values separated from one another by their real parts, each equal to the cosine of an explicit angle. -/

private theorem p3R_pow_p4B_norm_eq_one :
    ‖principalPow p3R p4B‖ = 1 := by
  rw [← p6O_pow_I_eq_p3R_pow_p4B]
  dsimp [principalPow]
  rw [p6O_eq_exp_neg_beta, ← Complex.ofReal_log (Real.exp_pos (-beta)).le, Real.log_exp]
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem p3R_pow_p4B_re_pos :
    0 < (principalPow p3R p4B).re := by
  rw [← p6O_pow_I_eq_p3R_pow_p4B]
  dsimp [principalPow]
  rw [p6O_eq_exp_neg_beta, ← Complex.ofReal_log (Real.exp_pos (-beta)).le, Real.log_exp]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [beta_pos, Real.pi_pos], beta_lt_angleE⟩

private theorem p3R_pow_p4B_im_neg :
    (principalPow p3R p4B).im < 0 := by
  rw [← p6O_pow_I_eq_p3R_pow_p4B]
  dsimp [principalPow]
  rw [p6O_eq_exp_neg_beta, ← Complex.ofReal_log (Real.exp_pos (-beta)).le, Real.log_exp]
  rw [Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  have hsin : 0 < Real.sin beta :=
    Real.sin_pos_of_mem_Ioo ⟨beta_pos, beta_lt_angleE.trans angleE_lt_pi⟩
  linarith

private theorem p2_pow_norm_lt_one_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ‖principalPow p2 z‖ < 1 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p2_eq]
  simp [Complex.mul_re]
  nlinarith [Real.pi_pos, hz]

private theorem p2_pow_p5E_re_zero :
    (principalPow p2 p5E).re = 0 := by
  rw [p5E_eq_I]
  change p3R.re = 0
  rw [p3R_eq_neg_I]
  norm_num

private theorem p3R_pow_p4B_notMem_p2NegativeExponents :
    principalPow p3R p4B ∉
      (fun z : ℂ => principalPow p2 z) '' a198683SevenP2NegativeExponents := by
  rintro ⟨z, hz, hpow⟩
  change principalPow p2 z = principalPow p3R p4B at hpow
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · have hlt : ‖principalPow p2 p5A‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5A_re_pos
    rw [hpow, p3R_pow_p4B_norm_eq_one] at hlt
    norm_num at hlt
  · have hlt : ‖principalPow p2 p5B‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5B_re_pos
    rw [hpow, p3R_pow_p4B_norm_eq_one] at hlt
    norm_num at hlt
  · have hlt : ‖principalPow p2 p5C‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5C_re_pos
    rw [hpow, p3R_pow_p4B_norm_eq_one] at hlt
    norm_num at hlt
  · have hzero : (principalPow p2 p5E).re = 0 := p2_pow_p5E_re_zero
    rw [hpow] at hzero
    have hpos : 0 < (principalPow p3R p4B).re := p3R_pow_p4B_re_pos
    linarith
  · have hlt : ‖principalPow p2 p5F‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5F_re_pos
    rw [hpow, p3R_pow_p4B_norm_eq_one] at hlt
    norm_num at hlt

private theorem p3R_pow_p4B_mem_seven :
    principalPow p3R p4B ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨2, p3R, ?_, p4B, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inr rfl)
  · exact mem_valueSet_four.2 (Or.inr (Or.inl rfl))

private theorem unit_re_pos_notMem_p2NegativeExponents {x : ℂ}
    (hnorm : ‖x‖ = 1) (hre : 0 < x.re) :
    x ∉ (fun z : ℂ => principalPow p2 z) '' a198683SevenP2NegativeExponents := by
  rintro ⟨z, hz, hpow⟩
  change principalPow p2 z = x at hpow
  dsimp [a198683SevenP2NegativeExponents] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl
  · have hlt : ‖principalPow p2 p5A‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5A_re_pos
    rw [hpow, hnorm] at hlt
    norm_num at hlt
  · have hlt : ‖principalPow p2 p5B‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5B_re_pos
    rw [hpow, hnorm] at hlt
    norm_num at hlt
  · have hlt : ‖principalPow p2 p5C‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5C_re_pos
    rw [hpow, hnorm] at hlt
    norm_num at hlt
  · have hzero : (principalPow p2 p5E).re = 0 := p2_pow_p5E_re_zero
    rw [hpow] at hzero
    linarith
  · have hlt : ‖principalPow p2 p5F‖ < 1 :=
      p2_pow_norm_lt_one_of_re_pos p5F_re_pos
    rw [hpow, hnorm] at hlt
    norm_num at hlt

private theorem p3R_pow_p4B_re_eq_cos_beta :
    (principalPow p3R p4B).re = Real.cos beta := by
  rw [← p6O_pow_I_eq_p3R_pow_p4B]
  dsimp [principalPow]
  rw [p6O_eq_exp_neg_beta, ← Complex.ofReal_log (Real.exp_pos (-beta)).le, Real.log_exp]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem p3R_pow_p4C_norm_eq_one :
    ‖principalPow p3R p4C‖ = 1 := by
  rw [p3R_pow_p4C_eq_p6J_pow_I]
  dsimp [principalPow]
  rw [p6J_eq_exp_neg_angleC,
    ← Complex.ofReal_log (Real.exp_pos (-(Real.pi / 2 * Real.exp (-theta)))).le,
    Real.log_exp]
  rw [Complex.norm_exp]
  have hexp_neg_theta_im : (Complex.exp (-(theta : ℂ))).im = 0 := by
    simpa using Complex.exp_ofReal_im (-theta)
  simp [Complex.mul_re, Complex.mul_im, hexp_neg_theta_im]

private theorem p3R_pow_p4C_re_eq_cos_angleC :
    (principalPow p3R p4C).re = Real.cos (Real.pi / 2 * Real.exp (-theta)) := by
  rw [p3R_pow_p4C_eq_p6J_pow_I]
  dsimp [principalPow]
  rw [p6J_eq_exp_neg_angleC,
    ← Complex.ofReal_log (Real.exp_pos (-(Real.pi / 2 * Real.exp (-theta)))).le,
    Real.log_exp]
  rw [Complex.exp_re]
  have hexp_neg_theta_im : (Complex.exp (-(theta : ℂ))).im = 0 := by
    simpa using Complex.exp_ofReal_im (-theta)
  have hexp_neg_theta_re : (Complex.exp (-(theta : ℂ))).re = Real.exp (-theta) := by
    simpa using Complex.exp_ofReal_re (-theta)
  simp [Complex.mul_re, Complex.mul_im, hexp_neg_theta_im, hexp_neg_theta_re]

private theorem p3R_pow_p4C_re_pos :
    0 < (principalPow p3R p4C).re := by
  rw [p3R_pow_p4C_re_eq_cos_angleC]
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [angleC_pos, Real.pi_pos], angleC_lt_angleE⟩

private theorem p3R_pow_p4C_im_neg :
    (principalPow p3R p4C).im < 0 := by
  rw [p3R_pow_p4C_eq_p6J_pow_I]
  dsimp [principalPow]
  rw [p6J_eq_exp_neg_angleC,
    ← Complex.ofReal_log (Real.exp_pos (-(Real.pi / 2 * Real.exp (-theta)))).le,
    Real.log_exp]
  rw [Complex.exp_im]
  have hexp_neg_theta_im : (Complex.exp (-(theta : ℂ))).im = 0 := by
    simpa using Complex.exp_ofReal_im (-theta)
  have hexp_neg_theta_re : (Complex.exp (-(theta : ℂ))).re = Real.exp (-theta) := by
    simpa using Complex.exp_ofReal_re (-theta)
  simp [Complex.mul_re, Complex.mul_im, hexp_neg_theta_im, hexp_neg_theta_re]
  have hsin : 0 < Real.sin (Real.pi / 2 * Real.exp (-theta)) :=
    Real.sin_pos_of_mem_Ioo ⟨angleC_pos, angleC_lt_angleE.trans angleE_lt_pi⟩
  linarith

private theorem p3R_pow_p4B_re_lt_p3R_pow_p4C_re :
    (principalPow p3R p4B).re < (principalPow p3R p4C).re := by
  rw [p3R_pow_p4B_re_eq_cos_beta, p3R_pow_p4C_re_eq_cos_angleC]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := Real.pi / 2 * Real.exp (-theta)) (y := beta)
    angleC_pos.le beta_lt_angleE.le angleC_lt_beta

private theorem p3R_pow_p4C_mem_seven :
    principalPow p3R p4C ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨2, p3R, ?_, p4C, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inr rfl)
  · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))

private theorem p5G_pow_p2_norm_eq_one :
    ‖principalPow p5G p2‖ = 1 := by
  rw [p5G_pow_p2_eq_p6N_pow_I]
  dsimp [principalPow]
  rw [p6N_eq_exp_neg_angleF, ← Complex.ofReal_log (Real.exp_pos (-(theta * rho))).le,
    Real.log_exp]
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem p5G_pow_p2_re_eq_cos_angleF :
    (principalPow p5G p2).re = Real.cos (theta * rho) := by
  rw [p5G_pow_p2_eq_p6N_pow_I]
  dsimp [principalPow]
  rw [p6N_eq_exp_neg_angleF, ← Complex.ofReal_log (Real.exp_pos (-(theta * rho))).le,
    Real.log_exp]
  rw [Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem p5G_pow_p2_re_pos :
    0 < (principalPow p5G p2).re := by
  rw [p5G_pow_p2_re_eq_cos_angleF]
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [angleF_pos, Real.pi_pos],
      (angleF_lt_angleC.trans angleC_lt_angleE)⟩

private theorem p5G_pow_p2_im_neg :
    (principalPow p5G p2).im < 0 := by
  rw [p5G_pow_p2_eq_p6N_pow_I]
  dsimp [principalPow]
  rw [p6N_eq_exp_neg_angleF, ← Complex.ofReal_log (Real.exp_pos (-(theta * rho))).le,
    Real.log_exp]
  rw [Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  have hsin : 0 < Real.sin (theta * rho) :=
    Real.sin_pos_of_mem_Ioo
      ⟨angleF_pos, (angleF_lt_angleC.trans angleC_lt_angleE).trans angleE_lt_pi⟩
  linarith

private theorem p3R_pow_p4C_re_lt_p5G_pow_p2_re :
    (principalPow p3R p4C).re < (principalPow p5G p2).re := by
  rw [p3R_pow_p4C_re_eq_cos_angleC, p5G_pow_p2_re_eq_cos_angleF]
  exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := theta * rho) (y := Real.pi / 2 * Real.exp (-theta))
    angleF_pos.le angleC_lt_angleE.le angleF_lt_angleC

private theorem p5G_pow_p2_mem_seven :
    principalPow p5G p2 ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨4, p5G, ?_, p2, ?_, rfl⟩
  · exact mem_valueSet_five.2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  · exact mem_valueSet_two.2 rfl

/-! ## Irrational-angle witnesses via rho and sigma

The constants `rho` and `sigma` and the `p5F^p2`, `p5B^p2` values they certify through numeric real-part bounds. -/

private theorem rho_pos : 0 < rho := by
  dsimp [rho]
  positivity

private theorem rho_lt_one : rho < 1 := by
  dsimp [rho]
  exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])

private theorem rho_cubed_im_zero : ((rho : ℂ) ^ 3).im = 0 := by
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

private theorem rho_cubed_re_eq : ((rho : ℂ) ^ 3).re = rho ^ 3 := by
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im]

private theorem rho_cubed_re_bounds :
    -2 < (((rho : ℂ) ^ 3).re) ∧ (((rho : ℂ) ^ 3).re) ≤ 2 := by
  have hpos : 0 < rho ^ 3 := pow_pos rho_pos 3
  have hlt : rho ^ 3 < 1 := by
    exact pow_lt_one₀ rho_pos.le rho_lt_one (by norm_num : (3 : ℕ) ≠ 0)
  constructor
  · rw [rho_cubed_re_eq]
    nlinarith
  · rw [rho_cubed_re_eq]
    nlinarith

private theorem p5F_pow_p2_eq_I_pow_rho_cubed :
    principalPow p5F p2 = principalPow Complex.I ((rho : ℂ) ^ 3) := by
  dsimp [principalPow]
  rw [log_p5F_eq, p2_eq_rho, log_I_real]
  congr 1
  dsimp [theta]
  have hrho_im := rho_cubed_im_zero
  have hrho_re := rho_cubed_re_eq
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, hrho_im, hrho_re]
  · simp [Complex.mul_re, Complex.mul_im, hrho_im, hrho_re]
    ring_nf

private theorem rho_cubed_re_lt_p6E_re :
    (((rho : ℂ) ^ 3).re) < p6E.re := by
  have hE : p6E.re = rho := by
    rw [p6E_eq_p2, p2_eq_rho]
    exact Complex.ofReal_re _
  rw [hE, rho_cubed_re_eq]
  have hlt : rho ^ 3 < rho := by
    have hsq_lt_one : rho ^ 2 < 1 := by
      exact pow_lt_one₀ rho_pos.le rho_lt_one (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith [rho_pos, hsq_lt_one]
  exact hlt

private theorem p6I_re_lt_rho_cubed_re :
    p6I.re < (((rho : ℂ) ^ 3).re) := by
  have hI : p6I.re = Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2))) := by
    rw [p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]
    exact Complex.ofReal_re _
  rw [hI, rho_cubed_re_eq]
  dsimp [rho]
  rw [show Real.exp (-(Real.pi / 2)) ^ 3 = Real.exp (3 * (-(Real.pi / 2))) by
    rw [← Real.exp_nat_mul]
    norm_num]
  apply Real.exp_lt_exp.mpr
  nlinarith [Real.pi_pos, exp_pi_div_two_gt_24_div_5]

private theorem rho_cubed_re_lt_p6O_re :
    (((rho : ℂ) ^ 3).re) < p6O.re :=
  rho_cubed_re_lt_p6E_re.trans p6E_re_lt_p6O_re

private theorem rho_cubed_re_lt_p6J_re :
    (((rho : ℂ) ^ 3).re) < p6J.re :=
  rho_cubed_re_lt_p6O_re.trans p6O_re_lt_p6J_re

private theorem rho_cubed_re_lt_p6N_re :
    (((rho : ℂ) ^ 3).re) < p6N.re :=
  rho_cubed_re_lt_p6J_re.trans p6J_re_lt_p6N_re

private theorem rho_cubed_re_lt_p6L_re :
    (((rho : ℂ) ^ 3).re) < p6L.re :=
  rho_cubed_re_lt_p6N_re.trans p6N_re_lt_p6L_re

private theorem a198683SixCandidateSet_ne_rho_cubed {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) : z ≠ (rho : ℂ) ^ 3 := by
  have hrho_im : (((rho : ℂ) ^ 3).im = 0) := rho_cubed_im_zero
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ne_of_im_pos_of_im_zero p6A_im_pos hrho_im
  · exact ne_of_im_pos_of_im_zero p6B_im_pos hrho_im
  · exact ne_of_im_pos_of_im_zero p6C_im_pos hrho_im
  · exact ne_of_im_pos_of_im_zero p6D_im_pos hrho_im
  · exact (ne_of_re_lt rho_cubed_re_lt_p6E_re).symm
  · exact ne_of_im_pos_of_im_zero p6F_im_pos hrho_im
  · exact ne_of_im_pos_of_im_zero p6G_im_pos hrho_im
  · exact ne_of_im_neg_of_im_zero p6H_im_neg hrho_im
  · exact ne_of_re_lt p6I_re_lt_rho_cubed_re
  · exact (ne_of_re_lt rho_cubed_re_lt_p6J_re).symm
  · exact ne_of_im_pos_of_im_zero p6K_im_pos hrho_im
  · exact (ne_of_re_lt rho_cubed_re_lt_p6L_re).symm
  · exact ne_of_im_neg_of_im_zero p6M_im_neg hrho_im
  · exact (ne_of_re_lt rho_cubed_re_lt_p6N_re).symm
  · exact (ne_of_re_lt rho_cubed_re_lt_p6O_re).symm

private theorem p5F_pow_p2_notMem_I_pow_sixCandidateSet :
    principalPow p5F p2 ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p5F p2 at hpow
  rw [p5F_pow_p2_eq_I_pow_rho_cubed] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = (rho : ℂ) ^ 3 :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 rho_cubed_re_bounds.1
      rho_cubed_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_rho_cubed hz heq

private theorem p5F_pow_p2_norm_eq_one :
    ‖principalPow p5F p2‖ = 1 := by
  rw [p5F_pow_p2_eq_I_pow_rho_cubed]
  exact I_pow_norm_eq_one_of_im_zero rho_cubed_im_zero

private theorem p5F_pow_p2_re_pos :
    0 < (principalPow p5F p2).re := by
  rw [p5F_pow_p2_eq_I_pow_rho_cubed]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, rho_cubed_im_zero, rho_cubed_re_eq]
  have hcube_pos : 0 < rho ^ 3 := pow_pos rho_pos 3
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, hcube_pos]
  · have hlt : rho ^ 3 < 1 := by
      exact pow_lt_one₀ rho_pos.le rho_lt_one (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith [Real.pi_pos, hlt]

private theorem p5F_pow_p2_im_pos :
    0 < (principalPow p5F p2).im := by
  rw [p5F_pow_p2_eq_I_pow_rho_cubed]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, rho_cubed_im_zero, rho_cubed_re_eq]
  have hcube_pos : 0 < rho ^ 3 := pow_pos rho_pos 3
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, hcube_pos]
  · have hlt : rho ^ 3 < 1 := by
      exact pow_lt_one₀ rho_pos.le rho_lt_one (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith [Real.pi_pos, hlt]

private theorem p5F_pow_p2_mem_seven :
    principalPow p5F p2 ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨4, p5F, ?_, p2, ?_, rfl⟩
  · exact mem_valueSet_five.2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact mem_valueSet_two.2 rfl

private theorem rho_lt_five_div_twenty_four :
    rho < (5 : ℝ) / 24 := by
  dsimp [rho]
  rw [Real.exp_neg]
  have hrec := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < (24 : ℝ) / 5) exp_pi_div_two_gt_24_div_5
  norm_num [one_div] at hrec
  exact hrec

private theorem sigma_pos :
    0 < (1 : ℝ) - 4 * rho := by
  nlinarith [rho_lt_five_div_twenty_four]

private theorem rho_cubed_lt_sigma :
    rho ^ 3 < (1 : ℝ) - 4 * rho := by
  have hcube_lt : rho ^ 3 < (1 : ℝ) / 8 := by
    have hrho_lt_half : rho < (1 : ℝ) / 2 := by
      linarith [rho_lt_five_div_twenty_four]
    have hpow := pow_lt_pow_left₀ hrho_lt_half rho_pos.le (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at hpow
    exact hpow
  have hsigma_gt : (1 : ℝ) / 6 < (1 : ℝ) - 4 * rho := by
    nlinarith [rho_lt_five_div_twenty_four]
  linarith

private theorem sigma_lt_rho :
    (1 : ℝ) - 4 * rho < rho := by
  nlinarith [rho_gt_one_div_five]

private theorem sigma_re_bounds :
    -2 < (((1 : ℝ) - 4 * rho : ℝ) : ℂ).re ∧
      ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) ≤ 2 := by
  constructor
  · rw [Complex.ofReal_re]
    nlinarith [sigma_pos]
  · rw [Complex.ofReal_re]
    nlinarith [sigma_lt_rho, rho_lt_one]

private theorem p5B_pow_p2_eq_I_pow_sigma :
    principalPow p5B p2 =
      principalPow Complex.I (((1 : ℝ) - 4 * rho : ℝ) : ℂ) := by
  dsimp [principalPow]
  rw [log_p5B_eq, p2_eq_rho, log_I_real]
  congr 1
  have hrho_mul : rho * Real.exp (Real.pi / 2) = 1 := by
    dsimp [rho]
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos (Real.pi / 2)).ne']
  have hexp_re : (Complex.exp ((Real.pi : ℂ) / 2)).re = Real.exp (Real.pi / 2) := by
    rw [show (Real.pi : ℂ) / 2 = ((Real.pi / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.exp_ofReal_re (Real.pi / 2)
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
  · simp [Complex.mul_re, Complex.mul_im, beta]
    rw [hexp_re]
    nlinarith [Real.pi_pos, hrho_mul]

private theorem p6I_re_lt_sigma_re :
    p6I.re < ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) := by
  exact p6I_re_lt_rho_cubed_re.trans (by
    rw [rho_cubed_re_eq, Complex.ofReal_re]
    exact rho_cubed_lt_sigma)

private theorem sigma_re_lt_p6E_re :
    ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) < p6E.re := by
  have hE : p6E.re = rho := by
    rw [p6E_eq_p2, p2_eq_rho]
    exact Complex.ofReal_re _
  rw [Complex.ofReal_re, hE]
  exact sigma_lt_rho

private theorem sigma_re_lt_p6O_re :
    ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) < p6O.re :=
  sigma_re_lt_p6E_re.trans p6E_re_lt_p6O_re

private theorem sigma_re_lt_p6J_re :
    ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) < p6J.re :=
  sigma_re_lt_p6O_re.trans p6O_re_lt_p6J_re

private theorem sigma_re_lt_p6N_re :
    ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) < p6N.re :=
  sigma_re_lt_p6J_re.trans p6J_re_lt_p6N_re

private theorem sigma_re_lt_p6L_re :
    ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).re) < p6L.re :=
  sigma_re_lt_p6N_re.trans p6N_re_lt_p6L_re

private theorem a198683SixCandidateSet_ne_sigma {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ (((1 : ℝ) - 4 * rho : ℝ) : ℂ) := by
  have hsigma_im : ((((1 : ℝ) - 4 * rho : ℝ) : ℂ).im = 0) := Complex.ofReal_im _
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ne_of_im_pos_of_im_zero p6A_im_pos hsigma_im
  · exact ne_of_im_pos_of_im_zero p6B_im_pos hsigma_im
  · exact ne_of_im_pos_of_im_zero p6C_im_pos hsigma_im
  · exact ne_of_im_pos_of_im_zero p6D_im_pos hsigma_im
  · exact ne_of_re_lt sigma_re_lt_p6E_re |>.symm
  · exact ne_of_im_pos_of_im_zero p6F_im_pos hsigma_im
  · exact ne_of_im_pos_of_im_zero p6G_im_pos hsigma_im
  · exact ne_of_im_neg_of_im_zero p6H_im_neg hsigma_im
  · exact ne_of_re_lt p6I_re_lt_sigma_re
  · exact ne_of_re_lt sigma_re_lt_p6J_re |>.symm
  · exact ne_of_im_pos_of_im_zero p6K_im_pos hsigma_im
  · exact ne_of_re_lt sigma_re_lt_p6L_re |>.symm
  · exact ne_of_im_neg_of_im_zero p6M_im_neg hsigma_im
  · exact ne_of_re_lt sigma_re_lt_p6N_re |>.symm
  · exact ne_of_re_lt sigma_re_lt_p6O_re |>.symm

private theorem p5B_pow_p2_notMem_I_pow_sixCandidateSet :
    principalPow p5B p2 ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p5B p2 at hpow
  rw [p5B_pow_p2_eq_I_pow_sigma] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = (((1 : ℝ) - 4 * rho : ℝ) : ℂ) :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 sigma_re_bounds.1 sigma_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_sigma hz heq

private theorem p5B_pow_p2_norm_eq_one :
    ‖principalPow p5B p2‖ = 1 := by
  rw [p5B_pow_p2_eq_I_pow_sigma]
  exact I_pow_norm_eq_one_of_im_zero (Complex.ofReal_im _)

private theorem p5B_pow_p2_re_eq_cos_sigma :
    (principalPow p5B p2).re = Real.cos (Real.pi / 2 * ((1 : ℝ) - 4 * rho)) := by
  rw [p5B_pow_p2_eq_I_pow_sigma]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem p5F_pow_p2_re_eq_cos_rho_cubed :
    (principalPow p5F p2).re = Real.cos (Real.pi / 2 * rho ^ 3) := by
  rw [p5F_pow_p2_eq_I_pow_rho_cubed]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, rho_cubed_im_zero, rho_cubed_re_eq]

private theorem p5B_pow_p2_re_pos :
    0 < (principalPow p5B p2).re := by
  rw [p5B_pow_p2_re_eq_cos_sigma]
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, sigma_pos]
  · have hsigma_lt_one : (1 : ℝ) - 4 * rho < 1 := by
      nlinarith [rho_pos]
    nlinarith [Real.pi_pos, hsigma_lt_one]

private theorem p5B_pow_p2_im_pos :
    0 < (principalPow p5B p2).im := by
  rw [p5B_pow_p2_eq_I_pow_sigma]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, sigma_pos]
  · have hsigma_lt_one : (1 : ℝ) - 4 * rho < 1 := by
      nlinarith [rho_pos]
    nlinarith [Real.pi_pos, hsigma_lt_one]

private theorem p5B_pow_p2_re_lt_p5F_pow_p2_re :
    (principalPow p5B p2).re < (principalPow p5F p2).re := by
  rw [p5B_pow_p2_re_eq_cos_sigma, p5F_pow_p2_re_eq_cos_rho_cubed]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
  · nlinarith [Real.pi_pos, pow_pos rho_pos 3]
  · have hsigma_lt_one : (1 : ℝ) - 4 * rho < 1 := by
      nlinarith [rho_pos]
    nlinarith [Real.pi_pos, hsigma_lt_one]
  · nlinarith [Real.pi_pos, rho_cubed_lt_sigma]

private theorem p5B_pow_p2_mem_seven :
    principalPow p5B p2 ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨4, p5B, ?_, p2, ?_, rfl⟩
  · exact mem_valueSet_five.2 (Or.inr (Or.inl rfl))
  · exact mem_valueSet_two.2 rfl

/-! ## tau witnesses via exponential and trig bounds

The constant `tau` and the `p4C^p3L`, `p3L^p4C` values, distinguished with explicit exp and sin numeric estimates. -/

private theorem p4C_pow_p3L_norm_lt_one :
    ‖principalPow p4C p3L‖ < 1 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p4C_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  exact mul_pos theta_pos hcos_pos

private theorem p4C_pow_p3L_im_neg :
    (principalPow p4C p3L).im < 0 := by
  dsimp [principalPow]
  rw [log_p4C_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_pos : 0 < theta * Real.sin theta := mul_pos theta_pos sin_theta_pos
  have harg_lt_pi : theta * Real.sin theta < Real.pi := by
    have hsin_le_one : Real.sin theta ≤ 1 := Real.sin_le_one theta
    nlinarith [theta_lt_pi_div_two, Real.pi_pos, hsin_le_one, theta_pos]
  have hsin_pos : 0 < Real.sin (theta * Real.sin theta) :=
    Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩
  have hprod :
      0 < Real.exp (-(theta * Real.cos theta)) * Real.sin (theta * Real.sin theta) :=
    mul_pos (Real.exp_pos _) hsin_pos
  nlinarith [hprod]

private theorem p4C_pow_p3L_mem_seven :
    principalPow p4C p3L ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨3, p4C, ?_, p3L, ?_, rfl⟩
  · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))
  · exact mem_valueSet_three.2 (Or.inl rfl)

private theorem exp_neg_one_div_three_gt_seven_div_ten :
    (7 : ℝ) / 10 < Real.exp (-(1 / 3 : ℝ)) := by
  rw [Real.exp_neg]
  have hupper := Real.exp_bound' (x := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  have hpoly :
      (∑ m ∈ Finset.range 4, ((1 : ℝ) / 3) ^ m / (m.factorial : ℝ)) +
          ((1 : ℝ) / 3) ^ 4 * ((4 : ℝ) + 1) / ((Nat.factorial 4 : ℝ) * (4 : ℝ)) <
        (10 : ℝ) / 7 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp_lt : Real.exp ((1 : ℝ) / 3) < (10 : ℝ) / 7 :=
    hupper.trans_lt hpoly
  have hrec := one_div_lt_one_div_of_lt (Real.exp_pos ((1 : ℝ) / 3)) hexp_lt
  norm_num [one_div] at hrec
  exact hrec

private theorem p4C_pow_p3L_norm_gt_seven_div_ten :
    (7 : ℝ) / 10 < ‖principalPow p4C p3L‖ := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p4C_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have hu_lt : theta * Real.cos theta < (1 : ℝ) / 3 := by
    nlinarith [theta_pos, theta_lt_one_div_three, hcos_pos, hcos_le_one]
  have hmono :
      Real.exp (-(1 / 3 : ℝ)) < Real.exp (-(theta * Real.cos theta)) :=
    Real.exp_lt_exp.mpr (by linarith [hu_lt])
  exact exp_neg_one_div_three_gt_seven_div_ten.trans hmono

private theorem exp_neg_pi_div_eight_lt_seven_div_ten :
    Real.exp (-(Real.pi / 8)) < (7 : ℝ) / 10 := by
  rw [Real.exp_neg]
  have hsum_le := Real.sum_le_exp_of_nonneg (x := Real.pi / 8) (by positivity) 3
  have hsum_gt :
      (10 : ℝ) / 7 <
        ∑ m ∈ Finset.range 3, (Real.pi / 8) ^ m / (m.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
    nlinarith [Real.pi_gt_d2]
  have hexp_gt : (10 : ℝ) / 7 < Real.exp (Real.pi / 8) :=
    hsum_gt.trans_le hsum_le
  have hrec := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < (10 : ℝ) / 7) hexp_gt
  norm_num [one_div] at hrec
  exact hrec

private theorem p2_pow_norm_lt_seven_div_ten_of_re_gt_one_div_four {z : ℂ}
    (hz : (1 : ℝ) / 4 < z.re) :
    ‖principalPow p2 z‖ < (7 : ℝ) / 10 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_p2_eq]
  simp [Complex.mul_re]
  have harg : Real.pi / 8 < Real.pi / 2 * z.re := by
    nlinarith [Real.pi_pos, hz]
  have hmono :
      Real.exp (-(Real.pi / 2 * z.re)) < Real.exp (-(Real.pi / 8)) :=
    Real.exp_lt_exp.mpr (by linarith [harg])
  exact hmono.trans exp_neg_pi_div_eight_lt_seven_div_ten

private theorem exp_pi_div_two_lt_twenty_nine_div_six :
    Real.exp (Real.pi / 2) < (29 : ℝ) / 6 := by
  have hpi : Real.pi / 4 < (63 : ℝ) / 80 := by
    linarith [Real.pi_lt_d2]
  let b : ℝ :=
    (∑ m ∈ Finset.range 5, ((63 : ℝ) / 80) ^ m / (m.factorial : ℝ)) +
      ((63 : ℝ) / 80) ^ 5 * ((5 : ℝ) + 1) / ((Nat.factorial 5 : ℝ) * (5 : ℝ))
  have hupper : Real.exp ((63 : ℝ) / 80) ≤ b := by
    dsimp [b]
    exact Real.exp_bound' (x := (63 : ℝ) / 80)
      (by norm_num) (by norm_num) (n := 5) (by norm_num)
  have hexp_lt : Real.exp (Real.pi / 4) < b :=
    ((Real.exp_lt_exp).2 hpi).trans_le hupper
  have hsquare : Real.exp (Real.pi / 4) ^ 2 < b ^ 2 :=
    pow_lt_pow_left₀ hexp_lt (Real.exp_pos (Real.pi / 4)).le
      (by norm_num : (2 : ℕ) ≠ 0)
  have hpoly :
      b ^ 2 <
        (29 : ℝ) / 6 := by
    dsimp [b]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [show Real.exp (Real.pi / 2) = Real.exp (Real.pi / 4) ^ 2 by
    rw [show Real.pi / 2 = Real.pi / 4 + Real.pi / 4 by ring, Real.exp_add]
    ring]
  exact hsquare.trans hpoly

private theorem sin_pi_div_twelve_gt_one_div_four :
    (1 : ℝ) / 4 < Real.sin (Real.pi / 12) := by
  have h := Real.sin_gt_sub_cube
    (x := Real.pi / 12) (by positivity)
  have harg_gt : (157 : ℝ) / 600 < Real.pi / 12 := by
    linarith [Real.pi_gt_d2]
  have harg_lt : Real.pi / 12 < (21 : ℝ) / 80 := by
    linarith [Real.pi_lt_d2]
  have harg_nonneg : 0 ≤ Real.pi / 12 := by positivity
  have hcube_lt : (Real.pi / 12) ^ 3 < ((21 : ℝ) / 80) ^ 3 :=
    pow_lt_pow_left₀ harg_lt harg_nonneg (by norm_num : (3 : ℕ) ≠ 0)
  nlinarith [h, harg_gt, hcube_lt]

private theorem p5B_re_gt_one_div_four :
    (1 : ℝ) / 4 < p5B.re := by
  rw [p5B_eq_exp_beta]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  rw [show beta = Real.pi / 2 - (Real.pi / 2 * (5 - Real.exp (Real.pi / 2))) by
    dsimp [beta]
    ring]
  rw [Real.cos_pi_div_two_sub]
  have hdelta_gt : Real.pi / 12 < Real.pi / 2 * (5 - Real.exp (Real.pi / 2)) := by
    nlinarith [Real.pi_pos, exp_pi_div_two_lt_twenty_nine_div_six]
  have hdelta_le : Real.pi / 2 * (5 - Real.exp (Real.pi / 2)) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, exp_pi_div_two_gt_24_div_5]
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := Real.pi / 12) (y := Real.pi / 2 * (5 - Real.exp (Real.pi / 2)))
    (by linarith [Real.pi_pos]) hdelta_le hdelta_gt
  simpa [one_div] using sin_pi_div_twelve_gt_one_div_four.trans hmono

private theorem p5C_re_gt_one_div_four :
    (1 : ℝ) / 4 < p5C.re := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  rw [show (Complex.exp (-(theta : ℂ))).im = 0 by
    simpa using Complex.exp_ofReal_im (-theta)]
  rw [mul_zero, neg_zero, Real.exp_zero, one_mul]
  rw [show Real.pi / 2 * Real.exp (-theta) =
      Real.pi / 2 - (Real.pi / 2 * (1 - Real.exp (-theta))) by ring]
  rw [Real.cos_pi_div_two_sub]
  have hdelta_gt : Real.pi / 12 < Real.pi / 2 * (1 - Real.exp (-theta)) := by
    nlinarith [Real.pi_pos, exp_neg_theta_lt_four_div_five]
  have hdelta_le : Real.pi / 2 * (1 - Real.exp (-theta)) ≤ Real.pi / 2 := by
    have hexp_pos : 0 < Real.exp (-theta) := Real.exp_pos _
    nlinarith [Real.pi_pos, hexp_pos]
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := Real.pi / 12) (y := Real.pi / 2 * (1 - Real.exp (-theta)))
    (by linarith [Real.pi_pos]) hdelta_le hdelta_gt
  simpa [one_div] using sin_pi_div_twelve_gt_one_div_four.trans hmono

private theorem p2_pow_image_p2NegativeExponents_norm_lt_seven_div_ten_or_unit {z : ℂ}
    (hz : z ∈ (fun w : ℂ => principalPow p2 w) '' a198683SevenP2NegativeExponents) :
    ‖z‖ < (7 : ℝ) / 10 ∨ z = principalPow p2 p5E := by
  rcases hz with ⟨w, hw, rfl⟩
  dsimp [a198683SevenP2NegativeExponents] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (p2_pow_norm_lt_seven_div_ten_of_re_gt_one_div_four
      p5A_re_gt_one_div_four)
  · exact Or.inl (p2_pow_norm_lt_seven_div_ten_of_re_gt_one_div_four
      p5B_re_gt_one_div_four)
  · exact Or.inl (p2_pow_norm_lt_seven_div_ten_of_re_gt_one_div_four
      p5C_re_gt_one_div_four)
  · exact Or.inr rfl
  · exact Or.inl (p2_pow_norm_lt_seven_div_ten_of_re_gt_one_div_four
      (by linarith [p5F_re_gt_half]))

private theorem p4C_pow_p3L_notMem_p2NegativeExponents :
    principalPow p4C p3L ∉
      (fun z : ℂ => principalPow p2 z) '' a198683SevenP2NegativeExponents := by
  intro hz
  rcases p2_pow_image_p2NegativeExponents_norm_lt_seven_div_ten_or_unit hz with hlt | hunit
  · have hgt : (7 : ℝ) / 10 < ‖principalPow p4C p3L‖ :=
      p4C_pow_p3L_norm_gt_seven_div_ten
    linarith
  · have hlt : ‖principalPow p4C p3L‖ < 1 := p4C_pow_p3L_norm_lt_one
    have hunit_norm : ‖principalPow p2 p5E‖ = 1 := by
      rw [p5E_eq_I]
      change ‖p3R‖ = 1
      rw [p3R_eq_neg_I]
      norm_num
    rw [hunit, hunit_norm] at hlt
    norm_num at hlt

private theorem exp_neg_theta_gt_two_div_three :
    (2 : ℝ) / 3 < Real.exp (-theta) := by
  have h := Real.one_sub_lt_exp_neg theta_pos.ne'
  nlinarith [h, theta_lt_one_div_three]

private theorem tau_pos : 0 < tau := by
  dsimp [tau]
  exact mul_pos (Real.exp_pos _) rho_pos

private theorem tau_lt_rho : tau < rho := by
  dsimp [tau]
  have hexp_lt_one : Real.exp (-theta) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [theta_pos])
  nlinarith [rho_pos, hexp_lt_one]

private theorem tau_lt_one : tau < 1 := by
  exact tau_lt_rho.trans rho_lt_one

private theorem rho_cubed_lt_tau :
    rho ^ 3 < tau := by
  have hrho_lt_half : rho < (1 : ℝ) / 2 := by
    linarith [rho_lt_five_div_twenty_four]
  have hrho_sq_lt_quarter : rho ^ 2 < (1 : ℝ) / 4 := by
    have hpow := pow_lt_pow_left₀ hrho_lt_half rho_pos.le
      (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at hpow
    exact hpow
  have hsquare_lt_exp : rho ^ 2 < Real.exp (-theta) := by
    linarith [hrho_sq_lt_quarter, exp_neg_theta_gt_two_div_three]
  dsimp [tau]
  calc
    rho ^ 3 = rho * rho ^ 2 := by ring
    _ < rho * Real.exp (-theta) := mul_lt_mul_of_pos_left hsquare_lt_exp rho_pos
    _ = Real.exp (-theta) * rho := by ring

private theorem tau_lt_one_div_six :
    tau < (1 : ℝ) / 6 := by
  dsimp [tau]
  nlinarith [Real.exp_pos (-theta), rho_pos, exp_neg_theta_lt_four_div_five,
    rho_lt_five_div_twenty_four]

private theorem tau_lt_sigma :
    tau < (1 : ℝ) - 4 * rho := by
  have hsigma_gt : (1 : ℝ) / 6 < (1 : ℝ) - 4 * rho := by
    nlinarith [rho_lt_five_div_twenty_four]
  exact tau_lt_one_div_six.trans hsigma_gt

private theorem tau_re_bounds :
    -2 < (((tau : ℝ) : ℂ).re) ∧ ((((tau : ℝ) : ℂ).re) ≤ 2) := by
  constructor
  · rw [Complex.ofReal_re]
    nlinarith [tau_pos]
  · rw [Complex.ofReal_re]
    nlinarith [tau_lt_one]

private theorem p3L_pow_p4C_eq_I_pow_tau :
    principalPow p3L p4C = principalPow Complex.I ((tau : ℝ) : ℂ) := by
  rw [p3L_pow_p4C_eq_p5C_pow_p2]
  dsimp [principalPow]
  rw [log_p5C_eq, p2_eq_rho, log_I_real]
  congr 1
  dsimp [tau]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem p6I_re_lt_tau_re :
    p6I.re < (((tau : ℝ) : ℂ).re) := by
  exact p6I_re_lt_rho_cubed_re.trans (by
    rw [rho_cubed_re_eq, Complex.ofReal_re]
    exact rho_cubed_lt_tau)

private theorem tau_re_lt_p6E_re :
    (((tau : ℝ) : ℂ).re) < p6E.re := by
  have hE : p6E.re = rho := by
    rw [p6E_eq_p2, p2_eq_rho]
    exact Complex.ofReal_re _
  rw [Complex.ofReal_re, hE]
  exact tau_lt_rho

private theorem tau_re_lt_p6O_re :
    (((tau : ℝ) : ℂ).re) < p6O.re :=
  tau_re_lt_p6E_re.trans p6E_re_lt_p6O_re

private theorem tau_re_lt_p6J_re :
    (((tau : ℝ) : ℂ).re) < p6J.re :=
  tau_re_lt_p6O_re.trans p6O_re_lt_p6J_re

private theorem tau_re_lt_p6N_re :
    (((tau : ℝ) : ℂ).re) < p6N.re :=
  tau_re_lt_p6J_re.trans p6J_re_lt_p6N_re

private theorem tau_re_lt_p6L_re :
    (((tau : ℝ) : ℂ).re) < p6L.re :=
  tau_re_lt_p6N_re.trans p6N_re_lt_p6L_re

private theorem a198683SixCandidateSet_ne_tau {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ ((tau : ℝ) : ℂ) := by
  have htau_im : (((tau : ℝ) : ℂ).im = 0) := Complex.ofReal_im _
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ne_of_im_pos_of_im_zero p6A_im_pos htau_im
  · exact ne_of_im_pos_of_im_zero p6B_im_pos htau_im
  · exact ne_of_im_pos_of_im_zero p6C_im_pos htau_im
  · exact ne_of_im_pos_of_im_zero p6D_im_pos htau_im
  · exact ne_of_re_lt tau_re_lt_p6E_re |>.symm
  · exact ne_of_im_pos_of_im_zero p6F_im_pos htau_im
  · exact ne_of_im_pos_of_im_zero p6G_im_pos htau_im
  · exact ne_of_im_neg_of_im_zero p6H_im_neg htau_im
  · exact ne_of_re_lt p6I_re_lt_tau_re
  · exact ne_of_re_lt tau_re_lt_p6J_re |>.symm
  · exact ne_of_im_pos_of_im_zero p6K_im_pos htau_im
  · exact ne_of_re_lt tau_re_lt_p6L_re |>.symm
  · exact ne_of_im_neg_of_im_zero p6M_im_neg htau_im
  · exact ne_of_re_lt tau_re_lt_p6N_re |>.symm
  · exact ne_of_re_lt tau_re_lt_p6O_re |>.symm

private theorem p3L_pow_p4C_notMem_I_pow_sixCandidateSet :
    principalPow p3L p4C ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p3L p4C at hpow
  rw [p3L_pow_p4C_eq_I_pow_tau] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = ((tau : ℝ) : ℂ) :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 tau_re_bounds.1 tau_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_tau hz heq

private theorem p3L_pow_p4C_norm_eq_one :
    ‖principalPow p3L p4C‖ = 1 := by
  rw [p3L_pow_p4C_eq_I_pow_tau]
  exact I_pow_norm_eq_one_of_im_zero (Complex.ofReal_im _)

private theorem p3L_pow_p4C_re_eq_cos_tau :
    (principalPow p3L p4C).re = Real.cos (Real.pi / 2 * tau) := by
  rw [p3L_pow_p4C_eq_I_pow_tau]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im]

private theorem p3L_pow_p4C_re_pos :
    0 < (principalPow p3L p4C).re := by
  rw [p3L_pow_p4C_re_eq_cos_tau]
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, tau_pos]
  · nlinarith [Real.pi_pos, tau_lt_one]

private theorem p3L_pow_p4C_im_pos :
    0 < (principalPow p3L p4C).im := by
  rw [p3L_pow_p4C_eq_I_pow_tau]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, tau_pos]
  · nlinarith [Real.pi_pos, tau_lt_one]

private theorem p5B_pow_p2_re_lt_p3L_pow_p4C_re :
    (principalPow p5B p2).re < (principalPow p3L p4C).re := by
  rw [p5B_pow_p2_re_eq_cos_sigma, p3L_pow_p4C_re_eq_cos_tau]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := Real.pi / 2 * tau) (y := Real.pi / 2 * ((1 : ℝ) - 4 * rho))
  · nlinarith [Real.pi_pos, tau_pos]
  · have hsigma_lt_one : (1 : ℝ) - 4 * rho < 1 := by
      nlinarith [rho_pos]
    nlinarith [Real.pi_pos, hsigma_lt_one]
  · nlinarith [Real.pi_pos, tau_lt_sigma]

private theorem p3L_pow_p4C_re_lt_p5F_pow_p2_re :
    (principalPow p3L p4C).re < (principalPow p5F p2).re := by
  rw [p3L_pow_p4C_re_eq_cos_tau, p5F_pow_p2_re_eq_cos_rho_cubed]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := Real.pi / 2 * rho ^ 3) (y := Real.pi / 2 * tau)
  · nlinarith [Real.pi_pos, pow_pos rho_pos 3]
  · nlinarith [Real.pi_pos, tau_lt_one]
  · nlinarith [Real.pi_pos, rho_cubed_lt_tau]

private theorem p3L_pow_p4C_mem_seven :
    principalPow p3L p4C ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨2, p3L, ?_, p4C, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inl rfl)
  · exact mem_valueSet_four.2 (Or.inr (Or.inr rfl))

/-! ## Squared and product witnesses (p3L², I·p5G)

Principal values arising from squares and products of base towers, with their distinctness proofs. -/

private theorem p3L_norm_eq_one :
    ‖p3L‖ = 1 := by
  rw [p3L_eq_exp_theta, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem p3L_sq_norm_eq_one :
    ‖p3L * p3L‖ = 1 := by
  rw [norm_mul, p3L_norm_eq_one]
  norm_num

private theorem p3L_sq_im_pos :
    0 < (p3L * p3L).im := by
  rw [p3L_eq_exp_theta]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  nlinarith [sin_theta_pos, hcos_pos]

private theorem p3L_sq_im_gt_one_div_three :
    (1 : ℝ) / 3 < (p3L * p3L).im := by
  rw [p3L_eq_exp_theta]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  nlinarith [sin_theta_gt_seven_div_thirty, cos_theta_gt_seventeen_div_eighteen]

private theorem p3L_sq_re_bounds :
    -2 < (p3L * p3L).re ∧ (p3L * p3L).re ≤ 2 := by
  exact re_bounds_of_norm_le_one (by rw [p3L_sq_norm_eq_one])

private theorem p3L_sq_re_lt_two :
    (p3L * p3L).re < 2 := by
  exact re_lt_two_of_norm_le_one (by rw [p3L_sq_norm_eq_one])

private theorem p4A_pow_p3L_eq_I_pow_p3L_sq :
    principalPow p4A p3L = principalPow Complex.I (p3L * p3L) := by
  dsimp [principalPow]
  rw [log_p4A_eq, log_I_real]
  congr 1
  ring

private theorem norm_gt_one_ne_norm_one {z w : ℂ} (hz : 1 < ‖z‖) (hw : ‖w‖ = 1) :
    z ≠ w := by
  intro h
  rw [h, hw] at hz
  exact (lt_irrefl (1 : ℝ)) hz

private theorem a198683SixCandidateSet_ne_p3L_sq {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ p3L * p3L := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact norm_lt_one_ne_norm_one p6A_norm_lt_one p3L_sq_norm_eq_one
  · exact norm_lt_one_ne_norm_one (p6B_norm_lt_four_div_five.trans (by norm_num))
      p3L_sq_norm_eq_one
  · exact norm_lt_one_ne_norm_one (p6C_norm_lt_four_div_five.trans (by norm_num))
      p3L_sq_norm_eq_one
  · exact norm_gt_one_ne_norm_one p6D_norm_gt_one p3L_sq_norm_eq_one
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6E_im_zero).symm
  · exact norm_lt_one_ne_norm_one p6F_norm_lt_one p3L_sq_norm_eq_one
  · exact norm_gt_one_ne_norm_one p6G_norm_gt_one p3L_sq_norm_eq_one
  · exact (ne_of_im_pos_of_im_neg p3L_sq_im_pos p6H_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6I_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6J_im_zero).symm
  · exact norm_lt_one_ne_norm_one p6K_norm_lt_one p3L_sq_norm_eq_one
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6L_im_zero).symm
  · exact (ne_of_im_pos_of_im_neg p3L_sq_im_pos p6M_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6N_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero p3L_sq_im_pos p6O_im_zero).symm

private theorem p4A_pow_p3L_notMem_I_pow_sixCandidateSet :
    principalPow p4A p3L ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p4A p3L at hpow
  rw [p4A_pow_p3L_eq_I_pow_p3L_sq] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = p3L * p3L :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 p3L_sq_re_bounds.1 p3L_sq_re_bounds.2
      hpow
  exact a198683SixCandidateSet_ne_p3L_sq hz heq

private theorem p4A_pow_p3L_norm_lt_one :
    ‖principalPow p4A p3L‖ < 1 := by
  rw [p4A_pow_p3L_eq_I_pow_p3L_sq]
  exact I_pow_norm_lt_one_of_im_pos p3L_sq_im_pos

private theorem p4A_pow_p3L_im_pos :
    0 < (principalPow p4A p3L).im := by
  rw [p4A_pow_p3L_eq_I_pow_p3L_sq]
  exact I_pow_im_pos_of_re_pos_of_re_lt_two
    (by
      rw [p3L_eq_exp_theta]
      simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
      have hsin_lt_one_div_three : Real.sin theta < (1 : ℝ) / 3 :=
        (Real.sin_lt theta_pos).trans theta_lt_one_div_three
      have hsin_sq_lt : Real.sin theta ^ 2 < ((1 : ℝ) / 3) ^ 2 :=
        pow_lt_pow_left₀ hsin_lt_one_div_three sin_theta_pos.le
          (by norm_num : (2 : ℕ) ≠ 0)
      have hcos_sq_gt : ((17 : ℝ) / 18) ^ 2 < Real.cos theta ^ 2 :=
        pow_lt_pow_left₀ cos_theta_gt_seventeen_div_eighteen
          (by norm_num : (0 : ℝ) ≤ (17 : ℝ) / 18)
          (by norm_num : (2 : ℕ) ≠ 0)
      nlinarith [hsin_sq_lt, hcos_sq_gt])
    p3L_sq_re_lt_two

private theorem p4A_pow_p3L_mem_seven :
    principalPow p4A p3L ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨3, p4A, ?_, p3L, ?_, rfl⟩
  · exact mem_valueSet_four.2 (Or.inl rfl)
  · exact mem_valueSet_three.2 (Or.inl rfl)

private theorem p2_pow_p5G_eq_I_pow_I_mul_p5G :
    principalPow p2 p5G = principalPow Complex.I (Complex.I * p5G) := by
  dsimp [principalPow]
  rw [log_p2_eq, log_I_real]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem I_mul_p5G_norm_eq_one :
    ‖Complex.I * p5G‖ = 1 := by
  rw [norm_mul, p5G_norm_eq_one]
  norm_num

private theorem I_mul_p5G_im_pos :
    0 < (Complex.I * p5G).im := by
  have h : (Complex.I * p5G).im = p5G.re := by
    simp [Complex.mul_im]
  rw [h]
  exact p5G_re_pos

private theorem I_mul_p5G_re_bounds :
    -2 < (Complex.I * p5G).re ∧ (Complex.I * p5G).re ≤ 2 := by
  exact re_bounds_of_norm_le_one (by rw [I_mul_p5G_norm_eq_one])

private theorem a198683SixCandidateSet_ne_I_mul_p5G {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ Complex.I * p5G := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact norm_lt_one_ne_norm_one p6A_norm_lt_one I_mul_p5G_norm_eq_one
  · exact norm_lt_one_ne_norm_one (p6B_norm_lt_four_div_five.trans (by norm_num))
      I_mul_p5G_norm_eq_one
  · exact norm_lt_one_ne_norm_one (p6C_norm_lt_four_div_five.trans (by norm_num))
      I_mul_p5G_norm_eq_one
  · exact norm_gt_one_ne_norm_one p6D_norm_gt_one I_mul_p5G_norm_eq_one
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6E_im_zero).symm
  · exact norm_lt_one_ne_norm_one p6F_norm_lt_one I_mul_p5G_norm_eq_one
  · exact norm_gt_one_ne_norm_one p6G_norm_gt_one I_mul_p5G_norm_eq_one
  · exact (ne_of_im_pos_of_im_neg I_mul_p5G_im_pos p6H_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6I_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6J_im_zero).symm
  · exact norm_lt_one_ne_norm_one p6K_norm_lt_one I_mul_p5G_norm_eq_one
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6L_im_zero).symm
  · exact (ne_of_im_pos_of_im_neg I_mul_p5G_im_pos p6M_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6N_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero I_mul_p5G_im_pos p6O_im_zero).symm

private theorem p2_pow_p5G_notMem_I_pow_sixCandidateSet :
    principalPow p2 p5G ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p2 p5G at hpow
  rw [p2_pow_p5G_eq_I_pow_I_mul_p5G] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = Complex.I * p5G :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 I_mul_p5G_re_bounds.1
      I_mul_p5G_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_I_mul_p5G hz heq

private theorem I_pow_norm_lt_of_im_gt {z w : ℂ} (h : w.im < z.im) :
    ‖principalPow Complex.I z‖ < ‖principalPow Complex.I w‖ := by
  dsimp [principalPow]
  rw [log_I_real, Complex.norm_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]
  nlinarith [Real.pi_pos, h]

private theorem p3L_sq_im_lt_I_mul_p5G_im :
    (p3L * p3L).im < (Complex.I * p5G).im := by
  rw [p3L_eq_exp_theta, p5G_eq_exp_neg_theta]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im, Real.cos_neg,
    Real.sin_neg]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hsin_lt_half : Real.sin theta < (1 : ℝ) / 2 := by
    nlinarith [Real.sin_lt theta_pos, theta_lt_one_div_three]
  nlinarith [hcos_pos, hsin_lt_half]

private theorem p2_pow_p5G_norm_lt_p4A_pow_p3L_norm :
    ‖principalPow p2 p5G‖ < ‖principalPow p4A p3L‖ := by
  rw [p2_pow_p5G_eq_I_pow_I_mul_p5G, p4A_pow_p3L_eq_I_pow_p3L_sq]
  exact I_pow_norm_lt_of_im_gt p3L_sq_im_lt_I_mul_p5G_im

private theorem p2_pow_p5G_norm_lt_one :
    ‖principalPow p2 p5G‖ < 1 := by
  rw [p2_pow_p5G_eq_I_pow_I_mul_p5G]
  exact I_pow_norm_lt_one_of_im_pos I_mul_p5G_im_pos

private theorem p2_pow_p5G_im_pos :
    0 < (principalPow p2 p5G).im := by
  rw [p2_pow_p5G_eq_I_pow_I_mul_p5G]
  exact I_pow_im_pos_of_re_pos_of_re_lt_two
    (by
      have h : (Complex.I * p5G).re = -p5G.im := by
        simp [Complex.mul_re]
      rw [h]
      nlinarith [p5G_im_neg])
    (re_lt_two_of_norm_le_one (by rw [I_mul_p5G_norm_eq_one]))

private theorem p2_pow_p5G_mem_seven :
    principalPow p2 p5G ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨1, p2, ?_, p5G, ?_, rfl⟩
  · exact mem_valueSet_two.2 rfl
  · exact mem_valueSet_five.2
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

/-! ## Final small-norm witnesses (rho·p4A, I·p5D)

The last low-modulus principal values completing the collection of thirty-four distinct points. -/

private theorem p4A_norm_lt_two_div_three :
    ‖p4A‖ < (2 : ℝ) / 3 := by
  dsimp [p4A, principalPow]
  rw [Complex.norm_exp, log_I_real, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  exact p4A_exp_factor_lt_two_div_three

private theorem rho_mul_p4A_norm_lt_one_div_six :
    ‖(rho : ℂ) * p4A‖ < (1 : ℝ) / 6 := by
  rw [norm_mul]
  have hrho_norm : ‖(rho : ℂ)‖ = rho := by
    rw [Complex.norm_of_nonneg rho_pos.le]
  rw [hrho_norm]
  nlinarith [rho_pos, rho_lt_five_div_twenty_four, p4A_norm_lt_two_div_three,
    norm_nonneg p4A]

private theorem rho_mul_p4A_norm_lt_one_div_five :
    ‖(rho : ℂ) * p4A‖ < (1 : ℝ) / 5 := by
  exact rho_mul_p4A_norm_lt_one_div_six.trans (by norm_num)

private theorem rho_mul_p4A_im_pos :
    0 < ((rho : ℂ) * p4A).im := by
  simp [Complex.mul_im]
  nlinarith [rho_pos, p4A_im_pos]

private theorem rho_mul_p4A_re_pos :
    0 < ((rho : ℂ) * p4A).re := by
  simp [Complex.mul_re]
  nlinarith [rho_pos, p4A_re_pos]

private theorem rho_mul_p4A_re_bounds :
    -2 < (((rho : ℂ) * p4A).re) ∧ (((rho : ℂ) * p4A).re) ≤ 2 := by
  exact re_bounds_of_norm_le_one
    (by
      exact rho_mul_p4A_norm_lt_one_div_six.le.trans (by norm_num))

private theorem p3L_pow_p4A_eq_I_pow_rho_mul_p4A :
    principalPow p3L p4A = principalPow Complex.I ((rho : ℂ) * p4A) := by
  dsimp [principalPow]
  rw [log_p3L_eq, log_I_real]
  congr 1
  dsimp [theta]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem I_pow_norm_ge_rho_of_im_le_one {z : ℂ} (hz : z.im ≤ 1) :
    rho ≤ ‖principalPow Complex.I z‖ := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  dsimp [rho]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz])

private theorem I_pow_norm_gt_one_div_five_of_im_le_one {z : ℂ} (hz : z.im ≤ 1) :
    (1 : ℝ) / 5 < ‖principalPow Complex.I z‖ :=
  rho_gt_one_div_five.trans_le (I_pow_norm_ge_rho_of_im_le_one hz)

private theorem im_le_one_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    z.im ≤ 1 := by
  exact (abs_le.mp ((Complex.abs_im_le_norm z).trans hz)).2

private theorem p6K_norm_gt_one_div_five :
    (1 : ℝ) / 5 < ‖p6K‖ := by
  nlinarith [Complex.re_le_norm p6K, p6K_re_gt_four_div_five]

private theorem a198683SixCandidateSet_ne_rho_mul_p4A {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ (rho : ℂ) * p4A := by
  dsimp [a198683SixCandidateSet] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5A_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5B_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5C_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5D_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6E_im_zero).symm
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5F_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      (I_pow_norm_gt_one_div_five_of_im_le_one (im_le_one_of_norm_le_one p5G_norm_le_one))
      rho_mul_p4A_norm_lt_one_div_five
  · exact (ne_of_im_pos_of_im_neg rho_mul_p4A_im_pos p6H_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6I_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6J_im_zero).symm
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 5)
      p6K_norm_gt_one_div_five rho_mul_p4A_norm_lt_one_div_five
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6L_im_zero).symm
  · exact (ne_of_im_pos_of_im_neg rho_mul_p4A_im_pos p6M_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6N_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero rho_mul_p4A_im_pos p6O_im_zero).symm

private theorem p3L_pow_p4A_notMem_I_pow_sixCandidateSet :
    principalPow p3L p4A ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p3L p4A at hpow
  rw [p3L_pow_p4A_eq_I_pow_rho_mul_p4A] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = (rho : ℂ) * p4A :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 rho_mul_p4A_re_bounds.1
      rho_mul_p4A_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_rho_mul_p4A hz heq

private theorem p3L_pow_p4A_norm_lt_one :
    ‖principalPow p3L p4A‖ < 1 := by
  rw [p3L_pow_p4A_eq_I_pow_rho_mul_p4A]
  exact I_pow_norm_lt_one_of_im_pos rho_mul_p4A_im_pos

private theorem p3L_pow_p4A_im_pos :
    0 < (principalPow p3L p4A).im := by
  rw [p3L_pow_p4A_eq_I_pow_rho_mul_p4A]
  exact I_pow_im_pos_of_re_pos_of_re_lt_two rho_mul_p4A_re_pos
    (re_lt_two_of_norm_le_one
      (rho_mul_p4A_norm_lt_one_div_six.le.trans (by norm_num)))

private theorem rho_mul_p4A_im_lt_p3L_sq_im :
    ((rho : ℂ) * p4A).im < (p3L * p3L).im := by
  have him_lt_norm : ((rho : ℂ) * p4A).im < (1 : ℝ) / 6 :=
    (Complex.im_le_norm ((rho : ℂ) * p4A)).trans_lt rho_mul_p4A_norm_lt_one_div_six
  have hsq_gt : (1 : ℝ) / 3 < (p3L * p3L).im := by
    rw [p3L_eq_exp_theta]
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
    nlinarith [sin_theta_gt_seven_div_thirty, cos_theta_gt_seventeen_div_eighteen]
  linarith

private theorem p4A_pow_p3L_norm_lt_p3L_pow_p4A_norm :
    ‖principalPow p4A p3L‖ < ‖principalPow p3L p4A‖ := by
  rw [p4A_pow_p3L_eq_I_pow_p3L_sq, p3L_pow_p4A_eq_I_pow_rho_mul_p4A]
  exact I_pow_norm_lt_of_im_gt rho_mul_p4A_im_lt_p3L_sq_im

private theorem p2_pow_p5G_norm_lt_p3L_pow_p4A_norm :
    ‖principalPow p2 p5G‖ < ‖principalPow p3L p4A‖ :=
  p2_pow_p5G_norm_lt_p4A_pow_p3L_norm.trans p4A_pow_p3L_norm_lt_p3L_pow_p4A_norm

private theorem p3L_pow_p4A_mem_seven :
    principalPow p3L p4A ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨2, p3L, ?_, p4A, ?_, rfl⟩
  · exact mem_valueSet_three.2 (Or.inl rfl)
  · exact mem_valueSet_four.2 (Or.inl rfl)

private theorem exp_neg_one_div_three_gt_five_div_seven :
    (5 : ℝ) / 7 < Real.exp (-(1 : ℝ) / 3) := by
  rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring, Real.exp_neg]
  have hbound := Real.exp_lt_two_add_div_two_sub
    (by norm_num : (0 : ℝ) < (1 : ℝ) / 3)
    (by norm_num : (1 : ℝ) / 3 < 2)
  have hexp_lt : Real.exp ((1 : ℝ) / 3) < (7 : ℝ) / 5 := by
    calc
      Real.exp ((1 : ℝ) / 3) <
          (2 + ((3 : ℝ)⁻¹)) / (2 - ((3 : ℝ)⁻¹)) := by
        simpa [one_div] using hbound
      _ = (7 : ℝ) / 5 := by
        norm_num
  have hpos : 0 < Real.exp ((1 : ℝ) / 3) := Real.exp_pos _
  have hrec : (5 : ℝ) / 7 < 1 / Real.exp ((1 : ℝ) / 3) := by
    rw [lt_div_iff₀ hpos]
    nlinarith [hexp_lt]
  simpa [one_div] using hrec

private theorem exp_neg_theta_gt_five_div_seven :
    (5 : ℝ) / 7 < Real.exp (-theta) := by
  have hmono : Real.exp (-(1 : ℝ) / 3) < Real.exp (-theta) :=
    (Real.exp_lt_exp).2 (by linarith [theta_lt_one_div_three])
  exact exp_neg_one_div_three_gt_five_div_seven.trans hmono

private theorem cos_pi_div_seven_gt_eight_div_nine :
    (8 : ℝ) / 9 < Real.cos (Real.pi / 7) := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 7)
  have hsq : (Real.pi / 7) ^ 2 / 2 < (1 : ℝ) / 9 := by
    have hpi_lt : Real.pi < (63 : ℝ) / 20 := by
      have h := Real.pi_lt_d2
      norm_num at h
      exact h
    have hpi_sq : Real.pi ^ 2 < ((63 : ℝ) / 20) ^ 2 :=
      pow_lt_pow_left₀ hpi_lt Real.pi_pos.le (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith [hpi_sq]
  nlinarith [h, hsq]

private theorem sin_pi_div_seven_lt_nine_div_twenty :
    Real.sin (Real.pi / 7) < (9 : ℝ) / 20 := by
  have hsin_lt : Real.sin (Real.pi / 7) < Real.pi / 7 :=
    Real.sin_lt (by positivity)
  nlinarith [hsin_lt, Real.pi_lt_d2]

private theorem angleC_gt_five_pi_div_fourteen :
    (5 : ℝ) * Real.pi / 14 < Real.pi / 2 * Real.exp (-theta) := by
  nlinarith [Real.pi_pos, exp_neg_theta_gt_five_div_seven]

private theorem p5C_im_gt_eight_div_nine :
    (8 : ℝ) / 9 < p5C.im := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta]
  simp only [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num
  have hbase : (8 : ℝ) / 9 < Real.sin ((5 : ℝ) * Real.pi / 14) := by
    rw [show (5 : ℝ) * Real.pi / 14 = Real.pi / 2 - Real.pi / 7 by ring]
    rw [Real.sin_pi_div_two_sub]
    exact cos_pi_div_seven_gt_eight_div_nine
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := (5 : ℝ) * Real.pi / 14)
    (y := Real.pi / 2 * Real.exp (-theta))
    (by nlinarith [Real.pi_pos])
    angleC_lt_angleE.le
    angleC_gt_five_pi_div_fourteen
  exact hbase.trans hmono

private theorem p5B_im_gt_eight_div_nine :
    (8 : ℝ) / 9 < p5B.im := by
  rw [p5B_eq_exp_beta]
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hbase : (8 : ℝ) / 9 < Real.sin ((5 : ℝ) * Real.pi / 14) := by
    rw [show (5 : ℝ) * Real.pi / 14 = Real.pi / 2 - Real.pi / 7 by ring]
    rw [Real.sin_pi_div_two_sub]
    exact cos_pi_div_seven_gt_eight_div_nine
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := (5 : ℝ) * Real.pi / 14)
    (y := beta)
    (by nlinarith [Real.pi_pos])
    beta_lt_angleE.le
    (angleC_gt_five_pi_div_fourteen.trans angleC_lt_beta)
  exact hbase.trans hmono

private theorem p5C_re_lt_nine_div_twenty :
    p5C.re < (9 : ℝ) / 20 := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta]
  simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := (5 : ℝ) * Real.pi / 14)
    (y := Real.pi / 2 * Real.exp (-theta))
    (by nlinarith [Real.pi_pos])
    angleC_lt_angleE.le
    angleC_gt_five_pi_div_fourteen
  have hcos_base :
      Real.cos ((5 : ℝ) * Real.pi / 14) < (9 : ℝ) / 20 := by
    rw [show (5 : ℝ) * Real.pi / 14 = Real.pi / 2 - Real.pi / 7 by ring]
    rw [Real.cos_pi_div_two_sub]
    exact sin_pi_div_seven_lt_nine_div_twenty
  exact hcos.trans hcos_base

private theorem p5B_re_lt_nine_div_twenty :
    p5B.re < (9 : ℝ) / 20 := by
  rw [p5B_eq_exp_beta]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := (5 : ℝ) * Real.pi / 14)
    (y := beta)
    (by nlinarith [Real.pi_pos])
    beta_lt_angleE.le
    (angleC_gt_five_pi_div_fourteen.trans angleC_lt_beta)
  have hcos_base :
      Real.cos ((5 : ℝ) * Real.pi / 14) < (9 : ℝ) / 20 := by
    rw [show (5 : ℝ) * Real.pi / 14 = Real.pi / 2 - Real.pi / 7 by ring]
    rw [Real.cos_pi_div_two_sub]
    exact sin_pi_div_seven_lt_nine_div_twenty
  exact hcos.trans hcos_base

private theorem exp_neg_four_pi_div_nine_lt_one_div_four :
    Real.exp (-(4 * Real.pi / 9)) < (1 : ℝ) / 4 := by
  rw [show -(4 * Real.pi / 9) = -(4 * Real.pi / 9) by ring, Real.exp_neg]
  have hpi18_pos : 0 < Real.pi / 18 := by positivity
  have hpi18_lt_two : Real.pi / 18 < 2 := by nlinarith [Real.pi_lt_d2]
  have hbound := Real.exp_lt_two_add_div_two_sub hpi18_pos hpi18_lt_two
  have hfrac :
      (2 + Real.pi / 18) / (2 - Real.pi / 18) < (6 : ℝ) / 5 := by
    have hden : 0 < 2 - Real.pi / 18 := by nlinarith [Real.pi_lt_d2]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_lt_d2]
  have hexp_pi18_lt : Real.exp (Real.pi / 18) < (6 : ℝ) / 5 :=
    hbound.trans hfrac
  have hprod_gt :
      (4 : ℝ) * Real.exp (Real.pi / 18) < Real.exp (4 * Real.pi / 9) *
        Real.exp (Real.pi / 18) := by
    rw [← Real.exp_add]
    have hsum : 4 * Real.pi / 9 + Real.pi / 18 = Real.pi / 2 := by ring
    rw [hsum]
    nlinarith [exp_pi_div_two_gt_24_div_5, hexp_pi18_lt, Real.exp_pos (Real.pi / 18)]
  have hexp_gt : (4 : ℝ) < Real.exp (4 * Real.pi / 9) :=
    lt_of_mul_lt_mul_right hprod_gt (Real.exp_pos (Real.pi / 18)).le
  have hrec := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (4 : ℝ)) hexp_gt
  norm_num [one_div] at hrec
  exact hrec

private theorem I_pow_norm_lt_one_div_four_of_im_gt_eight_div_nine {z : ℂ}
    (hz : (8 : ℝ) / 9 < z.im) :
    ‖principalPow Complex.I z‖ < (1 : ℝ) / 4 := by
  dsimp [principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  have harg : 4 * Real.pi / 9 < Real.pi / 2 * z.im := by
    nlinarith [Real.pi_pos, hz]
  have hmono : Real.exp (-(Real.pi / 2 * z.im)) < Real.exp (-(4 * Real.pi / 9)) :=
    (Real.exp_lt_exp).2 (by linarith [harg])
  exact hmono.trans (by simpa [one_div] using exp_neg_four_pi_div_nine_lt_one_div_four)

private theorem sin_nine_pi_div_forty_lt_two_div_three :
    Real.sin (9 * Real.pi / 40) < (2 : ℝ) / 3 := by
  let a : ℝ := 9 * Real.pi / 40
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hcos_lb := Real.one_sub_sq_div_two_le_cos (x := a)
  have hsq : a ^ 2 / 2 < (63 : ℝ) / 250 := by
    dsimp [a]
    have hpi_lt : Real.pi < (63 : ℝ) / 20 := by
      have h := Real.pi_lt_d2
      norm_num at h
      exact h
    have hpi_sq : Real.pi ^ 2 < ((63 : ℝ) / 20) ^ 2 :=
      pow_lt_pow_left₀ hpi_lt Real.pi_pos.le (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith [hpi_sq]
  have hcos_gt : (187 : ℝ) / 250 < Real.cos a := by
    nlinarith [hcos_lb, hsq]
  have htrig := Real.sin_sq_add_cos_sq a
  by_contra hnot
  have hge : (2 : ℝ) / 3 ≤ Real.sin a := le_of_not_gt hnot
  nlinarith [htrig, hcos_gt, hge]

private theorem I_pow_im_lt_one_div_six_of_re_lt_nine_div_twenty_of_norm_lt_one_div_four
    {z : ℂ} (hre_pos : 0 < z.re) (hre : z.re < (9 : ℝ) / 20)
    (hnorm : ‖principalPow Complex.I z‖ < (1 : ℝ) / 4) :
    (principalPow Complex.I z).im < (1 : ℝ) / 6 := by
  dsimp [principalPow] at hnorm ⊢
  rw [Complex.norm_exp, log_I_real] at hnorm
  rw [log_I_real, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im] at hnorm ⊢
  have hnorm' : Real.exp (-(Real.pi / 2 * z.im)) < (1 : ℝ) / 4 := by
    simpa [one_div] using hnorm
  have harg_pos : 0 < Real.pi / 2 * z.re := by
    nlinarith [Real.pi_pos, hre_pos]
  have harg_lt : Real.pi / 2 * z.re < 9 * Real.pi / 40 := by
    nlinarith [Real.pi_pos, hre]
  have hsin_lt : Real.sin (Real.pi / 2 * z.re) < (2 : ℝ) / 3 := by
    have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := Real.pi / 2 * z.re)
      (y := 9 * Real.pi / 40)
      (by nlinarith [Real.pi_pos, harg_pos])
      (by nlinarith [Real.pi_pos, Real.pi_lt_d2])
      harg_lt
    exact hmono.trans sin_nine_pi_div_forty_lt_two_div_three
  have hsin_pos : 0 < Real.sin (Real.pi / 2 * z.re) :=
    Real.sin_pos_of_mem_Ioo
      ⟨harg_pos, by nlinarith [Real.pi_pos, harg_lt, Real.pi_lt_d2]⟩
  have hmul₁ :
      Real.exp (-(Real.pi / 2 * z.im)) * Real.sin (Real.pi / 2 * z.re)
        < (1 : ℝ) / 4 * Real.sin (Real.pi / 2 * z.re) :=
    mul_lt_mul_of_pos_right hnorm' hsin_pos
  have hmul₂ :
      (1 : ℝ) / 4 * Real.sin (Real.pi / 2 * z.re) <
        (1 : ℝ) / 4 * ((2 : ℝ) / 3) :=
    mul_lt_mul_of_pos_left hsin_lt (by norm_num)
  nlinarith [hmul₁, hmul₂]

private theorem p6C_im_lt_one_div_six :
    p6C.im < (1 : ℝ) / 6 := by
  have hnorm : ‖principalPow Complex.I p5C‖ < (1 : ℝ) / 4 :=
    I_pow_norm_lt_one_div_four_of_im_gt_eight_div_nine p5C_im_gt_eight_div_nine
  simpa [p6C] using
    I_pow_im_lt_one_div_six_of_re_lt_nine_div_twenty_of_norm_lt_one_div_four
      p5C_re_pos p5C_re_lt_nine_div_twenty hnorm

private theorem p6B_im_lt_one_div_six :
    p6B.im < (1 : ℝ) / 6 := by
  have hnorm : ‖principalPow Complex.I p5B‖ < (1 : ℝ) / 4 :=
    I_pow_norm_lt_one_div_four_of_im_gt_eight_div_nine p5B_im_gt_eight_div_nine
  simpa [p6B] using
    I_pow_im_lt_one_div_six_of_re_lt_nine_div_twenty_of_norm_lt_one_div_four
      p5B_re_pos p5B_re_lt_nine_div_twenty hnorm

private theorem p5D_re_gt_one_div_six :
    (1 : ℝ) / 6 < p5D.re := by
  dsimp [p5D, principalPow]
  rw [Complex.exp_re, log_p2_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hexp_gt : (1 : ℝ) / 5 < Real.exp (-(Real.pi / 2 * Real.cos theta)) := by
    have harg : -(Real.pi / 2) < -(Real.pi / 2 * Real.cos theta) := by
      nlinarith [Real.pi_pos, cos_theta_lt_one]
    exact rho_gt_one_div_five.trans ((Real.exp_lt_exp).2 harg)
  have hangle_lt : Real.pi / 2 * Real.sin theta < Real.pi / 6 := by
    have hsin_lt_theta : Real.sin theta < theta := Real.sin_lt theta_pos
    nlinarith [Real.pi_pos, hsin_lt_theta, theta_lt_one_div_three]
  have hcos_lb := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 * Real.sin theta)
  have hsq : (Real.pi / 2 * Real.sin theta) ^ 2 / 2 < (1 : ℝ) / 6 := by
    have hangle_pos : 0 < Real.pi / 2 * Real.sin theta := by
      nlinarith [Real.pi_pos, sin_theta_pos]
    have hangle_lt_rational : Real.pi / 2 * Real.sin theta < (21 : ℝ) / 40 := by
      nlinarith [hangle_lt, Real.pi_lt_d2, Real.pi_pos]
    have hangle_sq : (Real.pi / 2 * Real.sin theta) ^ 2 < ((21 : ℝ) / 40) ^ 2 :=
      pow_lt_pow_left₀ hangle_lt_rational hangle_pos.le
        (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith [hangle_sq]
  have hcos_gt : (5 : ℝ) / 6 < Real.cos (Real.pi / 2 * Real.sin theta) := by
    nlinarith [hcos_lb, hsq]
  have hprod :
      (1 : ℝ) / 5 * ((5 : ℝ) / 6) <
        Real.exp (-(Real.pi / 2 * Real.cos theta)) *
          Real.cos (Real.pi / 2 * Real.sin theta) :=
    mul_lt_mul hexp_gt hcos_gt.le (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem I_mul_p5D_norm_lt_one_div_three :
    ‖Complex.I * p5D‖ < (1 : ℝ) / 3 := by
  rw [norm_mul]
  norm_num
  exact p5D_norm_lt_one_div_three

private theorem I_mul_p5D_im_gt_one_div_six :
    (1 : ℝ) / 6 < (Complex.I * p5D).im := by
  have h : (Complex.I * p5D).im = p5D.re := by
    simp [Complex.mul_im]
  rw [h]
  exact p5D_re_gt_one_div_six

private theorem I_mul_p5D_re_pos :
    0 < (Complex.I * p5D).re := by
  have h : (Complex.I * p5D).re = -p5D.im := by
    simp [Complex.mul_re]
  rw [h]
  nlinarith [p5D_im_neg]

private theorem I_mul_p5D_re_bounds :
    -2 < (Complex.I * p5D).re ∧ (Complex.I * p5D).re ≤ 2 := by
  exact re_bounds_of_norm_le_one (I_mul_p5D_norm_lt_one_div_three.le.trans (by norm_num))

private theorem p2_pow_p5D_eq_I_pow_I_mul_p5D :
    principalPow p2 p5D = principalPow Complex.I (Complex.I * p5D) := by
  dsimp [principalPow]
  rw [log_p2_eq, log_I_real]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem I_mul_p5D_im_lt_one_div_three :
    (Complex.I * p5D).im < (1 : ℝ) / 3 := by
  exact (Complex.im_le_norm (Complex.I * p5D)).trans_lt I_mul_p5D_norm_lt_one_div_three

private theorem p5F_im_lt_one_div_three :
    p5F.im < (1 : ℝ) / 3 := by
  rw [p5F_eq_exp_theta_mul_rho]
  simp [Complex.exp_im, Complex.mul_re, Complex.mul_im]
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hangle_nonneg : 0 ≤ theta * rho := mul_nonneg theta_pos.le rho_pos.le
  have hsin_le : Real.sin (theta * rho) ≤ theta * rho :=
    Real.sin_le hangle_nonneg
  have hangle_lt : theta * rho < (1 : ℝ) / 3 := by
    exact (mul_lt_of_lt_one_right theta_pos hrho_lt_one).trans theta_lt_one_div_three
  simpa [one_div] using hsin_le.trans_lt hangle_lt

private theorem p6F_norm_gt_one_div_three :
    (1 : ℝ) / 3 < ‖p6F‖ := by
  dsimp [p6F, principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  rw [Real.exp_neg]
  have harg_lt_log : Real.pi / 2 * p5F.im < Real.log 2 := by
    have harg_lt_pi_div_six : Real.pi / 2 * p5F.im < Real.pi / 6 := by
      nlinarith [Real.pi_pos, p5F_im_pos, p5F_im_lt_one_div_three]
    have hpi_div_six_lt_log_two : Real.pi / 6 < Real.log 2 := by
      nlinarith [Real.pi_lt_d2, Real.log_two_gt_d9]
    exact harg_lt_pi_div_six.trans hpi_div_six_lt_log_two
  have hexp_lt : Real.exp (Real.pi / 2 * p5F.im) < 2 :=
    exp_lt_two_of_lt_log_two harg_lt_log
  have hrec := one_div_lt_one_div_of_lt (Real.exp_pos (Real.pi / 2 * p5F.im)) hexp_lt
  norm_num [one_div] at hrec
  linarith

private theorem p6K_norm_gt_one_div_three :
    (1 : ℝ) / 3 < ‖p6K‖ := by
  nlinarith [Complex.re_le_norm p6K, p6K_re_gt_four_div_five]

private theorem a198683SixCandidateSet_ne_I_mul_p5D {z : ℂ}
    (hz : z ∈ a198683SixCandidateSet) :
    z ≠ Complex.I * p5D := by
  dsimp [a198683SixCandidateSet] at hz
  have htarget_im_pos : 0 < (Complex.I * p5D).im := by
    linarith [I_mul_p5D_im_gt_one_div_six]
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact (ne_of_im_lt (I_mul_p5D_im_lt_one_div_three.trans p6A_im_gt_one_div_three)).symm
  · exact ne_of_im_lt (p6B_im_lt_one_div_six.trans I_mul_p5D_im_gt_one_div_six)
  · exact ne_of_im_lt (p6C_im_lt_one_div_six.trans I_mul_p5D_im_gt_one_div_six)
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 3)
      (by linarith [p6D_norm_gt_one]) I_mul_p5D_norm_lt_one_div_three
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6E_im_zero).symm
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 3)
      p6F_norm_gt_one_div_three I_mul_p5D_norm_lt_one_div_three
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 3)
      (by linarith [p6G_norm_gt_one]) I_mul_p5D_norm_lt_one_div_three
  · exact (ne_of_im_pos_of_im_neg htarget_im_pos p6H_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6I_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6J_im_zero).symm
  · exact ne_of_norm_gt_norm_lt (r := (1 : ℝ) / 3)
      p6K_norm_gt_one_div_three I_mul_p5D_norm_lt_one_div_three
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6L_im_zero).symm
  · exact (ne_of_im_pos_of_im_neg htarget_im_pos p6M_im_neg).symm
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6N_im_zero).symm
  · exact (ne_of_im_pos_of_im_zero htarget_im_pos p6O_im_zero).symm

private theorem p2_pow_p5D_notMem_I_pow_sixCandidateSet :
    principalPow p2 p5D ∉
      (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet := by
  rintro ⟨z, hz, hpow⟩
  change principalPow Complex.I z = principalPow p2 p5D at hpow
  rw [p2_pow_p5D_eq_I_pow_I_mul_p5D] at hpow
  have hzre := a198683SixCandidateSet_re_bounds hz
  have heq : z = Complex.I * p5D :=
    I_pow_inj_of_re_mem_two hzre.1 hzre.2 I_mul_p5D_re_bounds.1
      I_mul_p5D_re_bounds.2 hpow
  exact a198683SixCandidateSet_ne_I_mul_p5D hz heq

private theorem p2_pow_p5D_norm_lt_one :
    ‖principalPow p2 p5D‖ < 1 := by
  rw [p2_pow_p5D_eq_I_pow_I_mul_p5D]
  exact I_pow_norm_lt_one_of_im_pos (by linarith [I_mul_p5D_im_gt_one_div_six])

private theorem p2_pow_p5D_im_pos :
    0 < (principalPow p2 p5D).im := by
  rw [p2_pow_p5D_eq_I_pow_I_mul_p5D]
  exact I_pow_im_pos_of_re_pos_of_re_lt_two I_mul_p5D_re_pos
    (re_lt_two_of_norm_le_one (I_mul_p5D_norm_lt_one_div_three.le.trans (by norm_num)))

private theorem I_mul_p5D_im_lt_p3L_sq_im :
    (Complex.I * p5D).im < (p3L * p3L).im := by
  exact I_mul_p5D_im_lt_one_div_three.trans p3L_sq_im_gt_one_div_three

private theorem p4A_pow_p3L_norm_lt_p2_pow_p5D_norm :
    ‖principalPow p4A p3L‖ < ‖principalPow p2 p5D‖ := by
  rw [p4A_pow_p3L_eq_I_pow_p3L_sq, p2_pow_p5D_eq_I_pow_I_mul_p5D]
  exact I_pow_norm_lt_of_im_gt I_mul_p5D_im_lt_p3L_sq_im

private theorem p2_pow_p5D_norm_lt_p3L_pow_p4A_norm :
    ‖principalPow p2 p5D‖ < ‖principalPow p3L p4A‖ := by
  rw [p2_pow_p5D_eq_I_pow_I_mul_p5D, p3L_pow_p4A_eq_I_pow_rho_mul_p4A]
  exact I_pow_norm_lt_of_im_gt
    ((Complex.im_le_norm ((rho : ℂ) * p4A)).trans_lt rho_mul_p4A_norm_lt_one_div_six
      |>.trans I_mul_p5D_im_gt_one_div_six)

private theorem p2_pow_p5G_norm_lt_p2_pow_p5D_norm :
    ‖principalPow p2 p5G‖ < ‖principalPow p2 p5D‖ :=
  p2_pow_p5G_norm_lt_p4A_pow_p3L_norm.trans p4A_pow_p3L_norm_lt_p2_pow_p5D_norm

private theorem p2_pow_p5D_mem_seven :
    principalPow p2 p5D ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  refine ⟨1, p2, ?_, p5D, ?_, rfl⟩
  · exact mem_valueSet_two.2 rfl
  · exact mem_valueSet_five.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-! ## Lower bound: thirty-four distinct principal values

Assembling every witness into the disjointness argument that proves `thirty_four_le_a198683_seven`. -/

theorem thirty_four_le_a198683_seven : 34 ≤ a198683 7 := by
  classical
  rw [a198683_eq_valueSet_ncard]
  let s : Set ℂ := (fun z : ℂ => principalPow Complex.I z) '' a198683SixCandidateSet
  let t : Set ℂ := (fun z : ℂ => principalPow p2 z) '' a198683SevenP2NegativeExponents
  let u : Set ℂ := s ∪ t
  let v : ℂ := principalPow p3R p4A
  let w : ℂ := principalPow p4B p3L
  let q : Set ℂ := insert v u
  let r : Set ℂ := insert w q
  let b : Set ℂ := insert Complex.I r
  let m : ℂ := principalPow p3R p4B
  let n : ℂ := principalPow p3R p4C
  let c : Set ℂ := insert m b
  let d : Set ℂ := insert n c
  let g : ℂ := principalPow p5G p2
  let e : Set ℂ := insert g d
  let f : ℂ := principalPow p5F p2
  let k : Set ℂ := insert f e
  let y : ℂ := principalPow p5B p2
  let h : Set ℂ := insert y k
  let x : ℂ := principalPow p4C p3L
  let zeta : ℂ := principalPow p3L p4C
  let eta : ℂ := principalPow p4A p3L
  let xi : ℂ := principalPow p2 p5G
  let omega : ℂ := principalPow p3L p4A
  let chi : ℂ := principalPow p2 p5D
  have hfinite7 : (a198683ValueSet 7).Finite := by
    let rep : Fin a198683SevenCanonicalReps.length → ℂ :=
      fun i => a198683SevenCanonicalReps.get i
    have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
      simpa [rep] using a198683_seven_subset_canonicalReps
    exact (Set.finite_range rep).subset hsubset
  have hs_card : s.ncard = 15 := by
    dsimp [s]
    rw [I_pow_injOn_a198683SixCandidateSet.ncard_image, a198683SixCandidateSet_ncard]
  have ht_card : t.ncard = 5 := by
    dsimp [t]
    rw [p2_pow_injOn_p2NegativeExponents.ncard_image,
      a198683SevenP2NegativeExponents_ncard]
  have hs_finite : s.Finite := by
    dsimp [s]
    exact (by simp [a198683SixCandidateSet] : a198683SixCandidateSet.Finite).image _
  have ht_finite : t.Finite := by
    dsimp [t]
    exact (by simp [a198683SevenP2NegativeExponents] :
      a198683SevenP2NegativeExponents.Finite).image _
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    intro z hzS hzT
    have hpos : 0 < z.im := by
      exact I_pow_image_sixCandidateSet_im_pos (by simpa [s] using hzS)
    have hneg : z.im < 0 := by
      exact p2_pow_image_p2NegativeExponents_im_neg (by simpa [t] using hzT)
    exact (lt_asymm hneg hpos).elim
  have hu_card : u.ncard = 20 := by
    dsimp [u]
    rw [Set.ncard_union_eq hdisj hs_finite ht_finite, hs_card, ht_card]
  have hu_finite : u.Finite := by
    dsimp [u]
    exact hs_finite.union ht_finite
  have hv_notMem : v ∉ u := by
    intro hv
    rcases hv with hvS | hvT
    · have hpos : 0 < v.im := by
        exact I_pow_image_sixCandidateSet_im_pos (by simpa [s, v] using hvS)
      have hneg : v.im < 0 := by
        simpa [v] using p3R_pow_p4A_im_neg
      exact (lt_asymm hneg hpos).elim
    · have hle : ‖v‖ ≤ 1 := by
        exact p2_pow_image_p2NegativeExponents_norm_le_one (by simpa [t, v] using hvT)
      have hgt : 1 < ‖v‖ := by
        simpa [v] using p3R_pow_p4A_norm_gt_one
      linarith
  have hq_card : q.ncard = 21 := by
    dsimp [q]
    rw [Set.ncard_insert_of_notMem hv_notMem hu_finite, hu_card]
  have hq_finite : q.Finite := by
    dsimp [q]
    exact hu_finite.insert v
  have hw_notMem : w ∉ q := by
    intro hw
    rcases hw with hwv | hwu
    · have hpos : 0 < w.im := by
        simpa [w] using p4B_pow_p3L_im_pos
      have hneg : v.im < 0 := by
        simpa [v] using p3R_pow_p4A_im_neg
      rw [hwv] at hpos
      exact (lt_asymm hneg hpos).elim
    · rcases hwu with hwS | hwT
      · exact p4B_pow_p3L_notMem_I_pow_sixCandidateSet (by simpa [s, w] using hwS)
      · have hle : ‖w‖ ≤ 1 := by
          exact p2_pow_image_p2NegativeExponents_norm_le_one (by simpa [t, w] using hwT)
        have hgt : 4 < ‖w‖ := by
          simpa [w] using p4B_pow_p3L_norm_gt_four
        linarith
  have hr_card : r.ncard = 22 := by
    dsimp [r]
    rw [Set.ncard_insert_of_notMem hw_notMem hq_finite, hq_card]
  have hr_finite : r.Finite := by
    dsimp [r]
    exact hq_finite.insert w
  have hI_notMem : Complex.I ∉ r := by
    intro hI
    rcases hI with hIw | hIq
    · have hgt : 4 < ‖w‖ := by
        simpa [w] using p4B_pow_p3L_norm_gt_four
      rw [← hIw] at hgt
      norm_num at hgt
    · rcases hIq with hIv | hIu
      · have hpos : 0 < Complex.I.im := by norm_num
        have hneg : v.im < 0 := by
          simpa [v] using p3R_pow_p4A_im_neg
        rw [hIv] at hpos
        exact (lt_asymm hneg hpos).elim
      · rcases hIu with hIS | hIT
        · exact I_notMem_I_pow_sixCandidateSet (by simpa [s] using hIS)
        · have hneg : Complex.I.im < 0 := by
            exact p2_pow_image_p2NegativeExponents_im_neg (by simpa [t] using hIT)
          norm_num at hneg
  have hb_card : b.ncard = 23 := by
    dsimp [b]
    rw [Set.ncard_insert_of_notMem hI_notMem hr_finite, hr_card]
  have hb_finite : b.Finite := by
    dsimp [b]
    exact hr_finite.insert Complex.I
  have hm_notMem : m ∉ b := by
    intro hm
    rcases hm with hmI | hmr
    · have hneg : m.im < 0 := by
        simpa [m] using p3R_pow_p4B_im_neg
      rw [hmI] at hneg
      norm_num at hneg
    · rcases hmr with hmw | hmq
      · have hneg : m.im < 0 := by
          simpa [m] using p3R_pow_p4B_im_neg
        have hpos : 0 < w.im := by
          simpa [w] using p4B_pow_p3L_im_pos
        rw [hmw] at hneg
        exact (lt_asymm hneg hpos).elim
      · rcases hmq with hmv | hmu
        · have hnorm : ‖m‖ = 1 := by
            simpa [m] using p3R_pow_p4B_norm_eq_one
          have hgt : 1 < ‖v‖ := by
            simpa [v] using p3R_pow_p4A_norm_gt_one
          rw [hmv] at hnorm
          linarith
        · rcases hmu with hmS | hmT
          · have hpos : 0 < m.im := by
              exact I_pow_image_sixCandidateSet_im_pos (by simpa [s, m] using hmS)
            have hneg : m.im < 0 := by
              simpa [m] using p3R_pow_p4B_im_neg
            exact (lt_asymm hneg hpos).elim
          · exact p3R_pow_p4B_notMem_p2NegativeExponents (by simpa [t, m] using hmT)
  have hc_card : c.ncard = 24 := by
    dsimp [c]
    rw [Set.ncard_insert_of_notMem hm_notMem hb_finite, hb_card]
  have hc_finite : c.Finite := by
    dsimp [c]
    exact hb_finite.insert m
  have hn_notMem : n ∉ c := by
    intro hn
    rcases hn with hnm | hnb
    · have hlt : m.re < n.re := by
        simpa [m, n] using p3R_pow_p4B_re_lt_p3R_pow_p4C_re
      rw [hnm] at hlt
      linarith
    · rcases hnb with hnI | hnr
      · have hneg : n.im < 0 := by
          simpa [n] using p3R_pow_p4C_im_neg
        rw [hnI] at hneg
        norm_num at hneg
      · rcases hnr with hnw | hnq
        · have hneg : n.im < 0 := by
            simpa [n] using p3R_pow_p4C_im_neg
          have hpos : 0 < w.im := by
            simpa [w] using p4B_pow_p3L_im_pos
          rw [hnw] at hneg
          exact (lt_asymm hneg hpos).elim
        · rcases hnq with hnv | hnu
          · have hnorm : ‖n‖ = 1 := by
              simpa [n] using p3R_pow_p4C_norm_eq_one
            have hgt : 1 < ‖v‖ := by
              simpa [v] using p3R_pow_p4A_norm_gt_one
            rw [hnv] at hnorm
            linarith
          · rcases hnu with hnS | hnT
            · have hpos : 0 < n.im := by
                exact I_pow_image_sixCandidateSet_im_pos (by simpa [s, n] using hnS)
              have hneg : n.im < 0 := by
                simpa [n] using p3R_pow_p4C_im_neg
              exact (lt_asymm hneg hpos).elim
            · exact unit_re_pos_notMem_p2NegativeExponents
                (by simpa [n] using p3R_pow_p4C_norm_eq_one)
                (by simpa [n] using p3R_pow_p4C_re_pos)
                (by simpa [t, n] using hnT)
  have hd_card : d.ncard = 25 := by
    dsimp [d]
    rw [Set.ncard_insert_of_notMem hn_notMem hc_finite, hc_card]
  have hd_finite : d.Finite := by
    dsimp [d]
    exact hc_finite.insert n
  have hg_notMem : g ∉ d := by
    intro hg
    rcases hg with hgn | hgc
    · have hlt : n.re < g.re := by
        simpa [n, g] using p3R_pow_p4C_re_lt_p5G_pow_p2_re
      rw [hgn] at hlt
      linarith
    · rcases hgc with hgm | hgb
      · have hmn : m.re < n.re := by
          simpa [m, n] using p3R_pow_p4B_re_lt_p3R_pow_p4C_re
        have hng : n.re < g.re := by
          simpa [n, g] using p3R_pow_p4C_re_lt_p5G_pow_p2_re
        rw [hgm] at hng
        linarith
      · rcases hgb with hgI | hgr
        · have hneg : g.im < 0 := by
            simpa [g] using p5G_pow_p2_im_neg
          rw [hgI] at hneg
          norm_num at hneg
        · rcases hgr with hgw | hgq
          · have hneg : g.im < 0 := by
              simpa [g] using p5G_pow_p2_im_neg
            have hpos : 0 < w.im := by
              simpa [w] using p4B_pow_p3L_im_pos
            rw [hgw] at hneg
            exact (lt_asymm hneg hpos).elim
          · rcases hgq with hgv | hgu
            · have hnorm : ‖g‖ = 1 := by
                simpa [g] using p5G_pow_p2_norm_eq_one
              have hgt : 1 < ‖v‖ := by
                simpa [v] using p3R_pow_p4A_norm_gt_one
              rw [hgv] at hnorm
              linarith
            · rcases hgu with hgS | hgT
              · have hpos : 0 < g.im := by
                  exact I_pow_image_sixCandidateSet_im_pos (by simpa [s, g] using hgS)
                have hneg : g.im < 0 := by
                  simpa [g] using p5G_pow_p2_im_neg
                exact (lt_asymm hneg hpos).elim
              · exact unit_re_pos_notMem_p2NegativeExponents
                  (by simpa [g] using p5G_pow_p2_norm_eq_one)
                  (by simpa [g] using p5G_pow_p2_re_pos)
                  (by simpa [t, g] using hgT)
  have he_card : e.ncard = 26 := by
    dsimp [e]
    rw [Set.ncard_insert_of_notMem hg_notMem hd_finite, hd_card]
  have he_finite : e.Finite := by
    dsimp [e]
    exact hd_finite.insert g
  have hf_notMem : f ∉ e := by
    intro hf
    rcases hf with hfg | hfd
    · have hpos : 0 < f.im := by
        simpa [f] using p5F_pow_p2_im_pos
      have hneg : g.im < 0 := by
        simpa [g] using p5G_pow_p2_im_neg
      rw [hfg] at hpos
      exact (lt_asymm hneg hpos).elim
    · rcases hfd with hfn | hfc
      · have hpos : 0 < f.im := by
          simpa [f] using p5F_pow_p2_im_pos
        have hneg : n.im < 0 := by
          simpa [n] using p3R_pow_p4C_im_neg
        rw [hfn] at hpos
        exact (lt_asymm hneg hpos).elim
      · rcases hfc with hfm | hfb
        · have hpos : 0 < f.im := by
            simpa [f] using p5F_pow_p2_im_pos
          have hneg : m.im < 0 := by
            simpa [m] using p3R_pow_p4B_im_neg
          rw [hfm] at hpos
          exact (lt_asymm hneg hpos).elim
        · rcases hfb with hfI | hfr
          · have hre : 0 < f.re := by
              simpa [f] using p5F_pow_p2_re_pos
            rw [hfI] at hre
            norm_num at hre
          · rcases hfr with hfw | hfq
            · have hnorm : ‖f‖ = 1 := by
                simpa [f] using p5F_pow_p2_norm_eq_one
              have hgt : 4 < ‖w‖ := by
                simpa [w] using p4B_pow_p3L_norm_gt_four
              rw [hfw] at hnorm
              linarith
            · rcases hfq with hfv | hfu
              · have hnorm : ‖f‖ = 1 := by
                  simpa [f] using p5F_pow_p2_norm_eq_one
                have hgt : 1 < ‖v‖ := by
                  simpa [v] using p3R_pow_p4A_norm_gt_one
                rw [hfv] at hnorm
                linarith
              · rcases hfu with hfS | hfT
                · exact p5F_pow_p2_notMem_I_pow_sixCandidateSet (by simpa [s, f] using hfS)
                · exact unit_re_pos_notMem_p2NegativeExponents
                    (by simpa [f] using p5F_pow_p2_norm_eq_one)
                    (by simpa [f] using p5F_pow_p2_re_pos)
                    (by simpa [t, f] using hfT)
  have hk_card : k.ncard = 27 := by
    dsimp [k]
    rw [Set.ncard_insert_of_notMem hf_notMem he_finite, he_card]
  have hk_finite : k.Finite := by
    dsimp [k]
    exact he_finite.insert f
  have hy_notMem : y ∉ k := by
    intro hy
    rcases hy with hyf | hye
    · have hlt : y.re < f.re := by
        simpa [y, f] using p5B_pow_p2_re_lt_p5F_pow_p2_re
      rw [hyf] at hlt
      linarith
    · rcases hye with hyg | hyd
      · have hpos : 0 < y.im := by
          simpa [y] using p5B_pow_p2_im_pos
        have hneg : g.im < 0 := by
          simpa [g] using p5G_pow_p2_im_neg
        rw [hyg] at hpos
        exact (lt_asymm hneg hpos).elim
      · rcases hyd with hyn | hyc
        · have hpos : 0 < y.im := by
            simpa [y] using p5B_pow_p2_im_pos
          have hneg : n.im < 0 := by
            simpa [n] using p3R_pow_p4C_im_neg
          rw [hyn] at hpos
          exact (lt_asymm hneg hpos).elim
        · rcases hyc with hym | hyb
          · have hpos : 0 < y.im := by
              simpa [y] using p5B_pow_p2_im_pos
            have hneg : m.im < 0 := by
              simpa [m] using p3R_pow_p4B_im_neg
            rw [hym] at hpos
            exact (lt_asymm hneg hpos).elim
          · rcases hyb with hyI | hyr
            · have hre : 0 < y.re := by
                simpa [y] using p5B_pow_p2_re_pos
              rw [hyI] at hre
              norm_num at hre
            · rcases hyr with hyw | hyq
              · have hnorm : ‖y‖ = 1 := by
                  simpa [y] using p5B_pow_p2_norm_eq_one
                have hgt : 4 < ‖w‖ := by
                  simpa [w] using p4B_pow_p3L_norm_gt_four
                rw [hyw] at hnorm
                linarith
              · rcases hyq with hyv | hyu
                · have hnorm : ‖y‖ = 1 := by
                    simpa [y] using p5B_pow_p2_norm_eq_one
                  have hgt : 1 < ‖v‖ := by
                    simpa [v] using p3R_pow_p4A_norm_gt_one
                  rw [hyv] at hnorm
                  linarith
                · rcases hyu with hyS | hyT
                  · exact p5B_pow_p2_notMem_I_pow_sixCandidateSet
                      (by simpa [s, y] using hyS)
                  · exact unit_re_pos_notMem_p2NegativeExponents
                      (by simpa [y] using p5B_pow_p2_norm_eq_one)
                      (by simpa [y] using p5B_pow_p2_re_pos)
                      (by simpa [t, y] using hyT)
  have h_card : h.ncard = 28 := by
    dsimp [h]
    rw [Set.ncard_insert_of_notMem hy_notMem hk_finite, hk_card]
  have h_finite : h.Finite := by
    dsimp [h]
    exact hk_finite.insert y
  have hx_notMem : x ∉ h := by
    intro hxmem
    dsimp [h] at hxmem
    rcases hxmem with hxy | hxk
    · have hneg : x.im < 0 := by
        simpa [x] using p4C_pow_p3L_im_neg
      have hpos : 0 < y.im := by
        simpa [y] using p5B_pow_p2_im_pos
      rw [hxy] at hneg
      exact (lt_asymm hneg hpos).elim
    · rcases hxk with hxf | hxe
      · have hneg : x.im < 0 := by
          simpa [x] using p4C_pow_p3L_im_neg
        have hpos : 0 < f.im := by
          simpa [f] using p5F_pow_p2_im_pos
        rw [hxf] at hneg
        exact (lt_asymm hneg hpos).elim
      · rcases hxe with hxg | hxd
        · have hlt : ‖x‖ < 1 := by
            simpa [x] using p4C_pow_p3L_norm_lt_one
          have hnorm : ‖g‖ = 1 := by
            simpa [g] using p5G_pow_p2_norm_eq_one
          rw [hxg, hnorm] at hlt
          norm_num at hlt
        · rcases hxd with hxn | hxc
          · have hlt : ‖x‖ < 1 := by
              simpa [x] using p4C_pow_p3L_norm_lt_one
            have hnorm : ‖n‖ = 1 := by
              simpa [n] using p3R_pow_p4C_norm_eq_one
            rw [hxn, hnorm] at hlt
            norm_num at hlt
          · rcases hxc with hxm | hxb
            · have hlt : ‖x‖ < 1 := by
                simpa [x] using p4C_pow_p3L_norm_lt_one
              have hnorm : ‖m‖ = 1 := by
                simpa [m] using p3R_pow_p4B_norm_eq_one
              rw [hxm, hnorm] at hlt
              norm_num at hlt
            · rcases hxb with hxI | hxr
              · have hlt : ‖x‖ < 1 := by
                  simpa [x] using p4C_pow_p3L_norm_lt_one
                rw [hxI] at hlt
                norm_num at hlt
              · rcases hxr with hxw | hxq
                · have hlt : ‖x‖ < 1 := by
                    simpa [x] using p4C_pow_p3L_norm_lt_one
                  have hgt : 4 < ‖w‖ := by
                    simpa [w] using p4B_pow_p3L_norm_gt_four
                  rw [hxw] at hlt
                  linarith
                · rcases hxq with hxv | hxu
                  · have hlt : ‖x‖ < 1 := by
                      simpa [x] using p4C_pow_p3L_norm_lt_one
                    have hgt : 1 < ‖v‖ := by
                      simpa [v] using p3R_pow_p4A_norm_gt_one
                    rw [hxv] at hlt
                    linarith
                  · rcases hxu with hxS | hxT
                    · have hpos : 0 < x.im := by
                        exact I_pow_image_sixCandidateSet_im_pos (by simpa [s, x] using hxS)
                      have hneg : x.im < 0 := by
                        simpa [x] using p4C_pow_p3L_im_neg
                      exact (lt_asymm hneg hpos).elim
                    · exact p4C_pow_p3L_notMem_p2NegativeExponents
                        (by simpa [t, x] using hxT)
  have hx_card : (insert x h).ncard = 29 := by
    rw [Set.ncard_insert_of_notMem hx_notMem h_finite, h_card]
  have hx_finite : (insert x h).Finite := by
    exact h_finite.insert x
  have hzeta_notMem : zeta ∉ insert x h := by
    intro hzeta_mem
    rcases hzeta_mem with hzetax | hzetah
    · have hpos : 0 < zeta.im := by
        simpa [zeta] using p3L_pow_p4C_im_pos
      have hneg : x.im < 0 := by
        simpa [x] using p4C_pow_p3L_im_neg
      rw [hzetax] at hpos
      exact (lt_asymm hneg hpos).elim
    · dsimp [h] at hzetah
      rcases hzetah with hzetay | hzetak
      · have hlt : y.re < zeta.re := by
          simpa [y, zeta] using p5B_pow_p2_re_lt_p3L_pow_p4C_re
        rw [hzetay] at hlt
        linarith
      · rcases hzetak with hzetaf | hzetae
        · have hlt : zeta.re < f.re := by
            simpa [zeta, f] using p3L_pow_p4C_re_lt_p5F_pow_p2_re
          rw [hzetaf] at hlt
          linarith
        · rcases hzetae with hzetag | hzetad
          · have hpos : 0 < zeta.im := by
              simpa [zeta] using p3L_pow_p4C_im_pos
            have hneg : g.im < 0 := by
              simpa [g] using p5G_pow_p2_im_neg
            rw [hzetag] at hpos
            exact (lt_asymm hneg hpos).elim
          · rcases hzetad with hzetan | hzetac
            · have hpos : 0 < zeta.im := by
                simpa [zeta] using p3L_pow_p4C_im_pos
              have hneg : n.im < 0 := by
                simpa [n] using p3R_pow_p4C_im_neg
              rw [hzetan] at hpos
              exact (lt_asymm hneg hpos).elim
            · rcases hzetac with hzetam | hzetab
              · have hpos : 0 < zeta.im := by
                  simpa [zeta] using p3L_pow_p4C_im_pos
                have hneg : m.im < 0 := by
                  simpa [m] using p3R_pow_p4B_im_neg
                rw [hzetam] at hpos
                exact (lt_asymm hneg hpos).elim
              · rcases hzetab with hzetaI | hzetar
                · have hre : 0 < zeta.re := by
                    simpa [zeta] using p3L_pow_p4C_re_pos
                  rw [hzetaI] at hre
                  norm_num at hre
                · rcases hzetar with hzetaw | hzetaq
                  · have hnorm : ‖zeta‖ = 1 := by
                      simpa [zeta] using p3L_pow_p4C_norm_eq_one
                    have hgt : 4 < ‖w‖ := by
                      simpa [w] using p4B_pow_p3L_norm_gt_four
                    rw [hzetaw] at hnorm
                    linarith
                  · rcases hzetaq with hzetav | hzetau
                    · have hnorm : ‖zeta‖ = 1 := by
                        simpa [zeta] using p3L_pow_p4C_norm_eq_one
                      have hgt : 1 < ‖v‖ := by
                        simpa [v] using p3R_pow_p4A_norm_gt_one
                      rw [hzetav] at hnorm
                      linarith
                    · rcases hzetau with hzetaS | hzetaT
                      · exact p3L_pow_p4C_notMem_I_pow_sixCandidateSet
                          (by simpa [s, zeta] using hzetaS)
                      · exact unit_re_pos_notMem_p2NegativeExponents
                          (by simpa [zeta] using p3L_pow_p4C_norm_eq_one)
                          (by simpa [zeta] using p3L_pow_p4C_re_pos)
                          (by simpa [t, zeta] using hzetaT)
  have hzeta_card : (insert zeta (insert x h)).ncard = 30 := by
    rw [Set.ncard_insert_of_notMem hzeta_notMem hx_finite, hx_card]
  have hzeta_finite : (insert zeta (insert x h)).Finite := by
    exact hx_finite.insert zeta
  have heta_notMem : eta ∉ insert zeta (insert x h) := by
    intro heta_mem
    rcases heta_mem with hetazeta | hetaxh
    · have hlt : ‖eta‖ < 1 := by
        simpa [eta] using p4A_pow_p3L_norm_lt_one
      have hnorm : ‖zeta‖ = 1 := by
        simpa [zeta] using p3L_pow_p4C_norm_eq_one
      rw [hetazeta, hnorm] at hlt
      norm_num at hlt
    · rcases hetaxh with hetax | hetah
      · have hpos : 0 < eta.im := by
          simpa [eta] using p4A_pow_p3L_im_pos
        have hneg : x.im < 0 := by
          simpa [x] using p4C_pow_p3L_im_neg
        rw [hetax] at hpos
        exact (lt_asymm hneg hpos).elim
      · dsimp [h] at hetah
        rcases hetah with hetay | hetak
        · have hlt : ‖eta‖ < 1 := by
            simpa [eta] using p4A_pow_p3L_norm_lt_one
          have hnorm : ‖y‖ = 1 := by
            simpa [y] using p5B_pow_p2_norm_eq_one
          rw [hetay, hnorm] at hlt
          norm_num at hlt
        · rcases hetak with hetaf | hetae
          · have hlt : ‖eta‖ < 1 := by
              simpa [eta] using p4A_pow_p3L_norm_lt_one
            have hnorm : ‖f‖ = 1 := by
              simpa [f] using p5F_pow_p2_norm_eq_one
            rw [hetaf, hnorm] at hlt
            norm_num at hlt
          · rcases hetae with hetag | hetad
            · have hpos : 0 < eta.im := by
                simpa [eta] using p4A_pow_p3L_im_pos
              have hneg : g.im < 0 := by
                simpa [g] using p5G_pow_p2_im_neg
              rw [hetag] at hpos
              exact (lt_asymm hneg hpos).elim
            · rcases hetad with hetan | hetac
              · have hpos : 0 < eta.im := by
                  simpa [eta] using p4A_pow_p3L_im_pos
                have hneg : n.im < 0 := by
                  simpa [n] using p3R_pow_p4C_im_neg
                rw [hetan] at hpos
                exact (lt_asymm hneg hpos).elim
              · rcases hetac with hetam | hetab
                · have hpos : 0 < eta.im := by
                    simpa [eta] using p4A_pow_p3L_im_pos
                  have hneg : m.im < 0 := by
                    simpa [m] using p3R_pow_p4B_im_neg
                  rw [hetam] at hpos
                  exact (lt_asymm hneg hpos).elim
                · rcases hetab with hetaI | hetar
                  · have hlt : ‖eta‖ < 1 := by
                      simpa [eta] using p4A_pow_p3L_norm_lt_one
                    rw [hetaI] at hlt
                    norm_num at hlt
                  · rcases hetar with hetaw | hetaq
                    · have hlt : ‖eta‖ < 1 := by
                        simpa [eta] using p4A_pow_p3L_norm_lt_one
                      have hgt : 4 < ‖w‖ := by
                        simpa [w] using p4B_pow_p3L_norm_gt_four
                      rw [hetaw] at hlt
                      linarith
                    · rcases hetaq with hetav | hetau
                      · have hlt : ‖eta‖ < 1 := by
                          simpa [eta] using p4A_pow_p3L_norm_lt_one
                        have hgt : 1 < ‖v‖ := by
                          simpa [v] using p3R_pow_p4A_norm_gt_one
                        rw [hetav] at hlt
                        linarith
                      · rcases hetau with hetaS | hetaT
                        · exact p4A_pow_p3L_notMem_I_pow_sixCandidateSet
                            (by simpa [s, eta] using hetaS)
                        · have hpos : 0 < eta.im := by
                            simpa [eta] using p4A_pow_p3L_im_pos
                          have hneg : eta.im < 0 :=
                            p2_pow_image_p2NegativeExponents_im_neg
                              (by simpa [t, eta] using hetaT)
                          exact (lt_asymm hneg hpos).elim
  have heta_card : (insert eta (insert zeta (insert x h))).ncard = 31 := by
    rw [Set.ncard_insert_of_notMem heta_notMem hzeta_finite, hzeta_card]
  have heta_finite : (insert eta (insert zeta (insert x h))).Finite := by
    exact hzeta_finite.insert eta
  have hxi_notMem : xi ∉ insert eta (insert zeta (insert x h)) := by
    intro hxi_mem
    rcases hxi_mem with hxieta | hxizx
    · have hlt : ‖xi‖ < ‖eta‖ := by
        simpa [xi, eta] using p2_pow_p5G_norm_lt_p4A_pow_p3L_norm
      rw [hxieta] at hlt
      exact (lt_irrefl ‖eta‖) hlt
    · rcases hxizx with hxizeta | hxixh
      · have hlt : ‖xi‖ < 1 := by
          simpa [xi] using p2_pow_p5G_norm_lt_one
        have hnorm : ‖zeta‖ = 1 := by
          simpa [zeta] using p3L_pow_p4C_norm_eq_one
        rw [hxizeta, hnorm] at hlt
        norm_num at hlt
      · rcases hxixh with hxix | hxih
        · have hpos : 0 < xi.im := by
            simpa [xi] using p2_pow_p5G_im_pos
          have hneg : x.im < 0 := by
            simpa [x] using p4C_pow_p3L_im_neg
          rw [hxix] at hpos
          exact (lt_asymm hneg hpos).elim
        · dsimp [h] at hxih
          rcases hxih with hxiy | hxik
          · have hlt : ‖xi‖ < 1 := by
              simpa [xi] using p2_pow_p5G_norm_lt_one
            have hnorm : ‖y‖ = 1 := by
              simpa [y] using p5B_pow_p2_norm_eq_one
            rw [hxiy, hnorm] at hlt
            norm_num at hlt
          · rcases hxik with hxif | hxie
            · have hlt : ‖xi‖ < 1 := by
                simpa [xi] using p2_pow_p5G_norm_lt_one
              have hnorm : ‖f‖ = 1 := by
                simpa [f] using p5F_pow_p2_norm_eq_one
              rw [hxif, hnorm] at hlt
              norm_num at hlt
            · rcases hxie with hxig | hxid
              · have hlt : ‖xi‖ < 1 := by
                  simpa [xi] using p2_pow_p5G_norm_lt_one
                have hnorm : ‖g‖ = 1 := by
                  simpa [g] using p5G_pow_p2_norm_eq_one
                rw [hxig, hnorm] at hlt
                norm_num at hlt
              · rcases hxid with hxin | hxic
                · have hlt : ‖xi‖ < 1 := by
                    simpa [xi] using p2_pow_p5G_norm_lt_one
                  have hnorm : ‖n‖ = 1 := by
                    simpa [n] using p3R_pow_p4C_norm_eq_one
                  rw [hxin, hnorm] at hlt
                  norm_num at hlt
                · rcases hxic with hxim | hxib
                  · have hlt : ‖xi‖ < 1 := by
                      simpa [xi] using p2_pow_p5G_norm_lt_one
                    have hnorm : ‖m‖ = 1 := by
                      simpa [m] using p3R_pow_p4B_norm_eq_one
                    rw [hxim, hnorm] at hlt
                    norm_num at hlt
                  · rcases hxib with hxiI | hxir
                    · have hlt : ‖xi‖ < 1 := by
                        simpa [xi] using p2_pow_p5G_norm_lt_one
                      rw [hxiI] at hlt
                      norm_num at hlt
                    · rcases hxir with hxiw | hxiq
                      · have hlt : ‖xi‖ < 1 := by
                          simpa [xi] using p2_pow_p5G_norm_lt_one
                        have hgt : 4 < ‖w‖ := by
                          simpa [w] using p4B_pow_p3L_norm_gt_four
                        rw [hxiw] at hlt
                        linarith
                      · rcases hxiq with hxiv | hxiu
                        · have hlt : ‖xi‖ < 1 := by
                            simpa [xi] using p2_pow_p5G_norm_lt_one
                          have hgt : 1 < ‖v‖ := by
                            simpa [v] using p3R_pow_p4A_norm_gt_one
                          rw [hxiv] at hlt
                          linarith
                        · rcases hxiu with hxiS | hxiT
                          · exact p2_pow_p5G_notMem_I_pow_sixCandidateSet
                              (by simpa [s, xi] using hxiS)
                          · have hpos : 0 < xi.im := by
                              simpa [xi] using p2_pow_p5G_im_pos
                            have hneg : xi.im < 0 :=
                              p2_pow_image_p2NegativeExponents_im_neg
                                (by simpa [t, xi] using hxiT)
                            exact (lt_asymm hneg hpos).elim
  have hxi_card : (insert xi (insert eta (insert zeta (insert x h)))).ncard = 32 := by
    rw [Set.ncard_insert_of_notMem hxi_notMem heta_finite, heta_card]
  have hxi_finite : (insert xi (insert eta (insert zeta (insert x h)))).Finite := by
    exact heta_finite.insert xi
  have homega_notMem : omega ∉ insert xi (insert eta (insert zeta (insert x h))) := by
    intro homega_mem
    rcases homega_mem with homegaxi | homegae
    · have hlt : ‖xi‖ < ‖omega‖ := by
        simpa [xi, omega] using p2_pow_p5G_norm_lt_p3L_pow_p4A_norm
      rw [homegaxi] at hlt
      exact (lt_irrefl _) hlt
    · rcases homegae with homegaeta | homegazx
      · have hlt : ‖eta‖ < ‖omega‖ := by
          simpa [eta, omega] using p4A_pow_p3L_norm_lt_p3L_pow_p4A_norm
        rw [homegaeta] at hlt
        exact (lt_irrefl _) hlt
      · rcases homegazx with homegazeta | homegaxh
        · have hlt : ‖omega‖ < 1 := by
            simpa [omega] using p3L_pow_p4A_norm_lt_one
          have hnorm : ‖zeta‖ = 1 := by
            simpa [zeta] using p3L_pow_p4C_norm_eq_one
          rw [homegazeta, hnorm] at hlt
          norm_num at hlt
        · rcases homegaxh with homegax | homegah
          · have hpos : 0 < omega.im := by
              simpa [omega] using p3L_pow_p4A_im_pos
            have hneg : x.im < 0 := by
              simpa [x] using p4C_pow_p3L_im_neg
            rw [homegax] at hpos
            exact (lt_asymm hneg hpos).elim
          · dsimp [h] at homegah
            rcases homegah with homegay | homegak
            · have hlt : ‖omega‖ < 1 := by
                simpa [omega] using p3L_pow_p4A_norm_lt_one
              have hnorm : ‖y‖ = 1 := by
                simpa [y] using p5B_pow_p2_norm_eq_one
              rw [homegay, hnorm] at hlt
              norm_num at hlt
            · rcases homegak with homegaf | homegae
              · have hlt : ‖omega‖ < 1 := by
                  simpa [omega] using p3L_pow_p4A_norm_lt_one
                have hnorm : ‖f‖ = 1 := by
                  simpa [f] using p5F_pow_p2_norm_eq_one
                rw [homegaf, hnorm] at hlt
                norm_num at hlt
              · rcases homegae with homegag | homegad
                · have hlt : ‖omega‖ < 1 := by
                    simpa [omega] using p3L_pow_p4A_norm_lt_one
                  have hnorm : ‖g‖ = 1 := by
                    simpa [g] using p5G_pow_p2_norm_eq_one
                  rw [homegag, hnorm] at hlt
                  norm_num at hlt
                · rcases homegad with homegan | homegac
                  · have hlt : ‖omega‖ < 1 := by
                      simpa [omega] using p3L_pow_p4A_norm_lt_one
                    have hnorm : ‖n‖ = 1 := by
                      simpa [n] using p3R_pow_p4C_norm_eq_one
                    rw [homegan, hnorm] at hlt
                    norm_num at hlt
                  · rcases homegac with homegam | homegab
                    · have hlt : ‖omega‖ < 1 := by
                        simpa [omega] using p3L_pow_p4A_norm_lt_one
                      have hnorm : ‖m‖ = 1 := by
                        simpa [m] using p3R_pow_p4B_norm_eq_one
                      rw [homegam, hnorm] at hlt
                      norm_num at hlt
                    · rcases homegab with homegaI | homegar
                      · have hlt : ‖omega‖ < 1 := by
                          simpa [omega] using p3L_pow_p4A_norm_lt_one
                        rw [homegaI] at hlt
                        norm_num at hlt
                      · rcases homegar with homegaw | homegaq
                        · have hlt : ‖omega‖ < 1 := by
                            simpa [omega] using p3L_pow_p4A_norm_lt_one
                          have hgt : 4 < ‖w‖ := by
                            simpa [w] using p4B_pow_p3L_norm_gt_four
                          rw [homegaw] at hlt
                          linarith
                        · rcases homegaq with homegav | homegau
                          · have hlt : ‖omega‖ < 1 := by
                              simpa [omega] using p3L_pow_p4A_norm_lt_one
                            have hgt : 1 < ‖v‖ := by
                              simpa [v] using p3R_pow_p4A_norm_gt_one
                            rw [homegav] at hlt
                            linarith
                          · rcases homegau with homegaS | homegaT
                            · exact p3L_pow_p4A_notMem_I_pow_sixCandidateSet
                                (by simpa [s, omega] using homegaS)
                            · have hpos : 0 < omega.im := by
                                simpa [omega] using p3L_pow_p4A_im_pos
                              have hneg : omega.im < 0 :=
                                p2_pow_image_p2NegativeExponents_im_neg
                                  (by simpa [t, omega] using homegaT)
                              exact (lt_asymm hneg hpos).elim
  have homega_card :
      (insert omega (insert xi (insert eta (insert zeta (insert x h))))).ncard = 33 := by
    rw [Set.ncard_insert_of_notMem homega_notMem hxi_finite, hxi_card]
  have homega_finite :
      (insert omega (insert xi (insert eta (insert zeta (insert x h))))).Finite := by
    exact hxi_finite.insert omega
  have hchi_notMem : chi ∉ insert omega (insert xi (insert eta (insert zeta (insert x h)))) := by
    intro hchi_mem
    rcases hchi_mem with hchiomega | hchix
    · have hlt : ‖chi‖ < ‖omega‖ := by
        simpa [chi, omega] using p2_pow_p5D_norm_lt_p3L_pow_p4A_norm
      rw [hchiomega] at hlt
      exact (lt_irrefl _) hlt
    · rcases hchix with hchixi | hchieta
      · have hlt : ‖xi‖ < ‖chi‖ := by
          simpa [xi, chi] using p2_pow_p5G_norm_lt_p2_pow_p5D_norm
        rw [hchixi] at hlt
        exact (lt_irrefl _) hlt
      · rcases hchieta with hchieta | hchizx
        · have hlt : ‖eta‖ < ‖chi‖ := by
            simpa [eta, chi] using p4A_pow_p3L_norm_lt_p2_pow_p5D_norm
          rw [hchieta] at hlt
          exact (lt_irrefl _) hlt
        · rcases hchizx with hchizeta | hchixh
          · have hlt : ‖chi‖ < 1 := by
              simpa [chi] using p2_pow_p5D_norm_lt_one
            have hnorm : ‖zeta‖ = 1 := by
              simpa [zeta] using p3L_pow_p4C_norm_eq_one
            rw [hchizeta, hnorm] at hlt
            norm_num at hlt
          · rcases hchixh with hchix | hchih
            · have hpos : 0 < chi.im := by
                simpa [chi] using p2_pow_p5D_im_pos
              have hneg : x.im < 0 := by
                simpa [x] using p4C_pow_p3L_im_neg
              rw [hchix] at hpos
              exact (lt_asymm hneg hpos).elim
            · dsimp [h] at hchih
              rcases hchih with hchiy | hchik
              · have hlt : ‖chi‖ < 1 := by
                  simpa [chi] using p2_pow_p5D_norm_lt_one
                have hnorm : ‖y‖ = 1 := by
                  simpa [y] using p5B_pow_p2_norm_eq_one
                rw [hchiy, hnorm] at hlt
                norm_num at hlt
              · rcases hchik with hchif | hchie
                · have hlt : ‖chi‖ < 1 := by
                    simpa [chi] using p2_pow_p5D_norm_lt_one
                  have hnorm : ‖f‖ = 1 := by
                    simpa [f] using p5F_pow_p2_norm_eq_one
                  rw [hchif, hnorm] at hlt
                  norm_num at hlt
                · rcases hchie with hchig | hchid
                  · have hlt : ‖chi‖ < 1 := by
                      simpa [chi] using p2_pow_p5D_norm_lt_one
                    have hnorm : ‖g‖ = 1 := by
                      simpa [g] using p5G_pow_p2_norm_eq_one
                    rw [hchig, hnorm] at hlt
                    norm_num at hlt
                  · rcases hchid with hchin | hchic
                    · have hlt : ‖chi‖ < 1 := by
                        simpa [chi] using p2_pow_p5D_norm_lt_one
                      have hnorm : ‖n‖ = 1 := by
                        simpa [n] using p3R_pow_p4C_norm_eq_one
                      rw [hchin, hnorm] at hlt
                      norm_num at hlt
                    · rcases hchic with hchim | hchib
                      · have hlt : ‖chi‖ < 1 := by
                          simpa [chi] using p2_pow_p5D_norm_lt_one
                        have hnorm : ‖m‖ = 1 := by
                          simpa [m] using p3R_pow_p4B_norm_eq_one
                        rw [hchim, hnorm] at hlt
                        norm_num at hlt
                      · rcases hchib with hchiI | hchir
                        · have hlt : ‖chi‖ < 1 := by
                            simpa [chi] using p2_pow_p5D_norm_lt_one
                          rw [hchiI] at hlt
                          norm_num at hlt
                        · rcases hchir with hchiw | hchiq
                          · have hlt : ‖chi‖ < 1 := by
                              simpa [chi] using p2_pow_p5D_norm_lt_one
                            have hgt : 4 < ‖w‖ := by
                              simpa [w] using p4B_pow_p3L_norm_gt_four
                            rw [hchiw] at hlt
                            linarith
                          · rcases hchiq with hchiv | hchiu
                            · have hlt : ‖chi‖ < 1 := by
                                simpa [chi] using p2_pow_p5D_norm_lt_one
                              have hgt : 1 < ‖v‖ := by
                                simpa [v] using p3R_pow_p4A_norm_gt_one
                              rw [hchiv] at hlt
                              linarith
                            · rcases hchiu with hchiS | hchiT
                              · exact p2_pow_p5D_notMem_I_pow_sixCandidateSet
                                  (by simpa [s, chi] using hchiS)
                              · have hpos : 0 < chi.im := by
                                  simpa [chi] using p2_pow_p5D_im_pos
                                have hneg : chi.im < 0 :=
                                  p2_pow_image_p2NegativeExponents_im_neg
                                    (by simpa [t, chi] using hchiT)
                                exact (lt_asymm hneg hpos).elim
  have hchi_card :
      (insert chi (insert omega (insert xi (insert eta (insert zeta (insert x h)))))).ncard =
        34 := by
    rw [Set.ncard_insert_of_notMem hchi_notMem homega_finite, homega_card]
  have hsubset :
      insert chi (insert omega (insert xi (insert eta (insert zeta (insert x h))))) ⊆
        a198683ValueSet 7 := by
    intro z hz
    rcases hz with rfl | hz
    · exact p2_pow_p5D_mem_seven
    · rcases hz with rfl | hz
      · exact p3L_pow_p4A_mem_seven
      · rcases hz with rfl | hz
        · exact p2_pow_p5G_mem_seven
        · rcases hz with rfl | hz
          · exact p4A_pow_p3L_mem_seven
          · rcases hz with rfl | hz
            · exact p3L_pow_p4C_mem_seven
            · rcases hz with rfl | hz
              · exact p4C_pow_p3L_mem_seven
              · dsimp [h] at hz
                rcases hz with rfl | hz
                · exact p5B_pow_p2_mem_seven
                · rcases hz with rfl | hz
                  · exact p5F_pow_p2_mem_seven
                  · rcases hz with rfl | hz
                    · exact p5G_pow_p2_mem_seven
                    · rcases hz with rfl | hz
                      · exact p3R_pow_p4C_mem_seven
                      · rcases hz with rfl | hz
                        · exact p3R_pow_p4B_mem_seven
                        · rcases hz with rfl | hz
                          · exact I_mem_seven
                          · rcases hz with rfl | hz
                            · exact p4B_pow_p3L_mem_seven
                            · rcases hz with rfl | hz
                              · exact p3R_pow_p4A_mem_seven
                              · rcases hz with hzS | hzT
                                · exact I_pow_image_sixCandidateSet_subset_seven
                                    (by simpa [s, u, q, r, b, c, d, e, k, h] using hzS)
                                · exact p2_pow_image_p2NegativeExponents_subset_seven
                                    (by simpa [t, u, q, r, b, c, d, e, k, h] using hzT)
  calc
    34 = (insert chi (insert omega (insert xi (insert eta (insert zeta (insert x h)))))).ncard :=
      hchi_card.symm
    _ ≤ (a198683ValueSet 7).ncard := Set.ncard_le_ncard hsubset hfinite7

/-! ## Assembled value and historical bounds

The identity `a198683 7 = 34` together with the weaker lower and upper bounds restated as corollaries. -/

theorem thirty_three_le_a198683_seven : 33 ≤ a198683 7 := by
  exact (by norm_num : 33 ≤ 34).trans thirty_four_le_a198683_seven

theorem a198683_seven : a198683 7 = 34 :=
  le_antisymm a198683_seven_le_thirty_four thirty_four_le_a198683_seven

theorem thirty_two_le_a198683_seven : 32 ≤ a198683 7 := by
  exact (by norm_num : 32 ≤ 33).trans thirty_three_le_a198683_seven

theorem thirty_one_le_a198683_seven : 31 ≤ a198683 7 := by
  exact (by norm_num : 31 ≤ 32).trans thirty_two_le_a198683_seven

theorem thirty_le_a198683_seven : 30 ≤ a198683 7 := by
  exact (by norm_num : 30 ≤ 31).trans thirty_one_le_a198683_seven

theorem twenty_nine_le_a198683_seven : 29 ≤ a198683 7 := by
  exact (by norm_num : 29 ≤ 30).trans thirty_le_a198683_seven

theorem twenty_eight_le_a198683_seven : 28 ≤ a198683 7 := by
  exact (by norm_num : 28 ≤ 29).trans twenty_nine_le_a198683_seven

theorem twenty_seven_le_a198683_seven : 27 ≤ a198683 7 := by
  exact (by norm_num : 27 ≤ 28).trans twenty_eight_le_a198683_seven

theorem twenty_six_le_a198683_seven : 26 ≤ a198683 7 := by
  exact (by norm_num : 26 ≤ 27).trans twenty_seven_le_a198683_seven

theorem twenty_five_le_a198683_seven : 25 ≤ a198683 7 := by
  exact (by norm_num : 25 ≤ 26).trans twenty_six_le_a198683_seven

theorem twenty_four_le_a198683_seven : 24 ≤ a198683 7 := by
  exact (by norm_num : 24 ≤ 25).trans twenty_five_le_a198683_seven

theorem twenty_three_le_a198683_seven : 23 ≤ a198683 7 := by
  exact (by norm_num : 23 ≤ 24).trans twenty_four_le_a198683_seven

theorem twenty_two_le_a198683_seven : 22 ≤ a198683 7 := by
  exact (by norm_num : 22 ≤ 23).trans twenty_three_le_a198683_seven

theorem twenty_one_le_a198683_seven : 21 ≤ a198683 7 := by
  exact (by norm_num : 21 ≤ 22).trans twenty_two_le_a198683_seven

theorem twenty_le_a198683_seven : 20 ≤ a198683 7 := by
  exact (by norm_num : 20 ≤ 21).trans twenty_one_le_a198683_seven

theorem fifteen_le_a198683_seven : 15 ≤ a198683 7 := by
  exact (by norm_num : 15 ≤ 20).trans twenty_le_a198683_seven

theorem fourteen_le_a198683_seven : 14 ≤ a198683 7 := by
  exact (by norm_num : 14 ≤ 15).trans fifteen_le_a198683_seven

theorem eleven_le_a198683_seven : 11 ≤ a198683 7 := by
  exact (by norm_num : 11 ≤ 14).trans fourteen_le_a198683_seven

theorem a198683_seven_le_thirty_eight : a198683 7 ≤ 38 :=
  a198683_seven_le_thirty_four.trans (by norm_num)

theorem a198683_seven_le_forty_four : a198683 7 ≤ 44 :=
  a198683_seven_le_thirty_eight.trans (by norm_num)

theorem a198683_seven_le_forty_five : a198683 7 ≤ 45 :=
  a198683_seven_le_forty_four.trans (by norm_num)

theorem a198683_seven_le_fifty_one : a198683 7 ≤ 51 :=
  a198683_seven_le_forty_five.trans (by norm_num)

theorem a198683_seven_le_fifty_six : a198683 7 ≤ 56 :=
  a198683_seven_le_fifty_one.trans (by norm_num)

end

end LeanProofs
