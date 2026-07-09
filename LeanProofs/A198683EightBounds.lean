import LeanProofs.A198683SevenUpper

/-!
# Unconditional bounds on `A198683(8)`: `16 ≤ a(8) ≤ 127`

The recurrence presents level `8` as principal powers `x^y` with
`x ∈ valueSet k`, `y ∈ valueSet (8-k)`, and the certified value lists for
levels `1..7` bound the raw candidate pool by
`Σ_k a(k)·a(8-k) = 34+15+14+9+14+15+34 = 135`.  This module tightens both
ends unconditionally:

* `a198683_eight_le : a198683 8 ≤ 127` — eight of the 135 candidates are
  proved equal to retained candidates (islands of associativity: the
  `e^{π/2}`, `e^{-θ}`, `e^{-π/2}`, `e^{-θe^{-θ}}`, and `e^{θρ}` classes each
  absorb duplicates), so the candidate list shrinks to 127 entries;
* `a198683_eight_ge : 16 ≤ a198683 8` — fifteen real-exponential candidate
  values are pairwise separated by a strictly decreasing chain of exponents
  (each link riding the proved `0 < θρ < π/2·e^{-θ} < β < π/2` angle
  ladder, plus one crude numeric estimate), and the non-real `p4A` joins
  them via its proved `im > 1/2`.

The heuristically expected value is `77`; closing `[16, 127]` down to `77`
is the merge/separation campaign measured in the wave-5 status ledger
(`Oeis/A198683/reports/wave-5/a198683-formalization-status-and-remaining-work.md`).
-/

namespace LeanProofs

open A198683Support

/-! ## Real-exponential principal powers

For positive real bases the principal power is an exponential of a real
product; every closed form below flows through this single lemma. -/

private theorem log_exp_ofReal (a : ℝ) :
    Complex.log ((Real.exp a : ℝ) : ℂ) = (a : ℂ) := by
  rw [← Complex.ofReal_log (Real.exp_pos a).le, Real.log_exp]

private theorem expPow (a b : ℝ) :
    principalPow ((Real.exp a : ℝ) : ℂ) ((Real.exp b : ℝ) : ℂ) =
      ((Real.exp (a * Real.exp b) : ℝ) : ℂ) := by
  dsimp [principalPow]
  rw [log_exp_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

private theorem p2_eq_exp : p2 = ((Real.exp (-(Real.pi / 2)) : ℝ) : ℂ) :=
  p2_eq_rho

/-! ## Closed forms of the distinguished level-8 candidates -/

private theorem p4B_pow_p4B_eq :
    principalPow p4B p4B =
      ((Real.exp (Real.pi / 2 * Real.exp (Real.pi / 2)) : ℝ) : ℂ) := by
  rw [p4B_eq_exp_pi_div_two]; exact expPow _ _

private theorem p4B_pow_p4C_eq :
    principalPow p4B p4C =
      ((Real.exp (Real.pi / 2 * Real.exp (-theta)) : ℝ) : ℂ) := by
  rw [p4B_eq_exp_pi_div_two, p4C_eq_exp_neg_theta]; exact expPow _ _

private theorem p4C_pow_p4B_eq :
    principalPow p4C p4B =
      ((Real.exp (-theta * Real.exp (Real.pi / 2)) : ℝ) : ℂ) := by
  rw [p4B_eq_exp_pi_div_two, p4C_eq_exp_neg_theta]; exact expPow _ _

private theorem p4C_pow_p4C_eq :
    principalPow p4C p4C =
      ((Real.exp (-theta * Real.exp (-theta)) : ℝ) : ℂ) := by
  rw [p4C_eq_exp_neg_theta]; exact expPow _ _

private theorem p2_pow_p6E_eq :
    principalPow p2 p6E = ((Real.exp (-(Real.pi / 2) * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6E_eq_exp_neg_pi_div_two]; exact expPow _ _

private theorem p6E_pow_p2_eq :
    principalPow p6E p2 = ((Real.exp (-(Real.pi / 2) * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6E_eq_exp_neg_pi_div_two]; exact expPow _ _

private theorem p2_pow_p6I_eq :
    principalPow p2 p6I =
      ((Real.exp (-(Real.pi / 2) *
        Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2)))) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]; exact expPow _ _

private theorem p6I_pow_p2_eq :
    principalPow p6I p2 =
      ((Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2)) * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]; exact expPow _ _

private theorem p2_pow_p6J_eq :
    principalPow p2 p6J =
      ((Real.exp (-(Real.pi / 2) *
        Real.exp (-(Real.pi / 2 * Real.exp (-theta)))) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6J_eq_exp_neg_angleC]; exact expPow _ _

private theorem p6J_pow_p2_eq :
    principalPow p6J p2 =
      ((Real.exp (-(Real.pi / 2 * Real.exp (-theta)) * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6J_eq_exp_neg_angleC]; exact expPow _ _

private theorem p2_pow_p6L_eq :
    principalPow p2 p6L =
      ((Real.exp (-(Real.pi / 2) * Real.exp theta) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6L_eq_exp_theta]; exact expPow _ _

private theorem p6L_pow_p2_eq :
    principalPow p6L p2 = ((Real.exp (theta * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6L_eq_exp_theta]; exact expPow _ _

private theorem p2_pow_p6N_eq :
    principalPow p2 p6N =
      ((Real.exp (-(Real.pi / 2) * Real.exp (-(theta * rho))) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6N_eq_exp_neg_angleF]; exact expPow _ _

private theorem p6N_pow_p2_eq :
    principalPow p6N p2 = ((Real.exp (-(theta * rho) * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6N_eq_exp_neg_angleF]; exact expPow _ _

private theorem p2_pow_p6O_eq :
    principalPow p2 p6O =
      ((Real.exp (-(Real.pi / 2) * Real.exp (-beta)) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6O_eq_exp_neg_beta]; exact expPow _ _

private theorem p6O_pow_p2_eq :
    principalPow p6O p2 = ((Real.exp (-beta * rho) : ℝ) : ℂ) := by
  rw [p2_eq_exp, p6O_eq_exp_neg_beta]; exact expPow _ _

private theorem p3R_pow_p5E_eq :
    principalPow p3R p5E = ((Real.exp (Real.pi / 2) : ℝ) : ℂ) := by
  rw [p3R_eq_neg_I, p5E_eq_I]; exact neg_i_pow_i_eq

private theorem p5E_pow_p3R_eq :
    principalPow p5E p3R = ((Real.exp (Real.pi / 2) : ℝ) : ℂ) := by
  rw [p5E_eq_I, p3R_eq_neg_I]; exact i_pow_neg_i_eq

private theorem p3L_pow_p5E_eq :
    principalPow p3L p5E = ((Real.exp (-theta) : ℝ) : ℂ) := by
  rw [p5E_eq_I]; exact i_pow_ii_pow_i_eq_theta

/-- A unit-circle base `exp(t·i)` raised to `-i` is the real `exp t`. -/
private theorem pow_neg_I_of_log_mul_I {x : ℂ} {t : ℝ}
    (h : Complex.log x = (t : ℂ) * Complex.I) :
    principalPow x (-Complex.I) = ((Real.exp t : ℝ) : ℂ) := by
  dsimp [principalPow]
  rw [h]
  rw [show (t : ℂ) * Complex.I * -Complex.I = ((t : ℝ) : ℂ) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  exact (Complex.ofReal_exp t).symm

private theorem p5B_pow_p3R_eq :
    principalPow p5B p3R = ((Real.exp beta : ℝ) : ℂ) := by
  rw [p3R_eq_neg_I]
  exact pow_neg_I_of_log_mul_I log_p5B_eq

private theorem p5C_pow_p3R_eq :
    principalPow p5C p3R =
      ((Real.exp (Real.pi / 2 * Real.exp (-theta)) : ℝ) : ℂ) := by
  rw [p3R_eq_neg_I]
  exact pow_neg_I_of_log_mul_I log_p5C_eq

private theorem p5F_pow_p3R_eq :
    principalPow p5F p3R = ((Real.exp (theta * rho) : ℝ) : ℂ) := by
  rw [p3R_eq_neg_I]
  exact pow_neg_I_of_log_mul_I log_p5F_eq

private theorem p5G_pow_p3R_eq :
    principalPow p5G p3R = ((Real.exp (-theta) : ℝ) : ℂ) := by
  rw [p3R_eq_neg_I]
  exact pow_neg_I_of_log_mul_I (by rw [log_p5G_eq]; push_cast; ring)

/-! ## The eight proved merges among the 135 raw candidates -/

private theorem neg_theta_eq : -theta = -(Real.pi / 2) * rho := by
  dsimp [theta]; ring

private theorem p3L_pow_p5E_redirect :
    principalPow p3L p5E = principalPow p2 p6E := by
  rw [p3L_pow_p5E_eq, p2_pow_p6E_eq, neg_theta_eq]

private theorem p5G_pow_p3R_redirect :
    principalPow p5G p3R = principalPow p2 p6E := by
  rw [p5G_pow_p3R_eq, p2_pow_p6E_eq, neg_theta_eq]

private theorem p6E_pow_p2_redirect :
    principalPow p6E p2 = principalPow p2 p6E :=
  p6E_pow_p2_eq.trans p2_pow_p6E_eq.symm

private theorem p5E_pow_p3R_redirect :
    principalPow p5E p3R = principalPow p3R p5E :=
  p5E_pow_p3R_eq.trans p3R_pow_p5E_eq.symm

private theorem p5F_pow_p3R_redirect :
    principalPow p5F p3R = principalPow p6L p2 :=
  p5F_pow_p3R_eq.trans p6L_pow_p2_eq.symm

private theorem p5C_pow_p3R_redirect :
    principalPow p5C p3R = principalPow p4B p4C :=
  p5C_pow_p3R_eq.trans p4B_pow_p4C_eq.symm

private theorem p6I_pow_p2_redirect :
    principalPow p6I p2 = principalPow p4C p4B := by
  rw [p6I_pow_p2_eq, p4C_pow_p4B_eq,
    show -(Real.pi / 2 * Real.exp (Real.pi / 2)) * rho =
        -theta * Real.exp (Real.pi / 2) by dsimp [theta]; ring]

private theorem p6J_pow_p2_redirect :
    principalPow p6J p2 = principalPow p4C p4C := by
  rw [p6J_pow_p2_eq, p4C_pow_p4C_eq,
    show -(Real.pi / 2 * Real.exp (-theta)) * rho =
        -theta * Real.exp (-theta) by dsimp [theta]; ring]

/-! ## The 127-entry candidate list -/

/-- One split block of level-8 candidates: all `x^y` with `x` drawn from a
level-`k` list and `y` from a level-`(8-k)` list. -/
private noncomputable def block (L L' : List ℂ) : List ℂ :=
  L.flatMap fun x => L'.map fun y => principalPow x y

private theorem mem_block {x y : ℂ} {L L' : List ℂ}
    (hx : x ∈ L) (hy : y ∈ L') :
    principalPow x y ∈ block L L' :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

private theorem block_length (L L' : List ℂ) :
    (block L L').length = L.length * L'.length := by
  simp [block, List.length_flatMap]

/-- The certified cover lists for levels `1..7`, plus the pruned variants
with the proved-duplicate entries removed. -/
private noncomputable def L1 : List ℂ := [Complex.I]
private noncomputable def L2 : List ℂ := [p2]
private noncomputable def L3 : List ℂ := [p3L, p3R]
private noncomputable def L4 : List ℂ := [p4A, p4B, p4C]
private noncomputable def L5 : List ℂ := [p5A, p5B, p5C, p5D, p5E, p5F, p5G]
private noncomputable def L5noE : List ℂ := [p5A, p5B, p5C, p5D, p5F, p5G]
private noncomputable def L5r : List ℂ := [p5A, p5B, p5D]
private noncomputable def L6 : List ℂ :=
  [p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O]
private noncomputable def L6r : List ℂ :=
  [p6A, p6B, p6C, p6D, p6F, p6G, p6H, p6K, p6L, p6M, p6N, p6O]
private noncomputable def L7 : List ℂ := a198683SevenCanonicalReps

/-- The `127` level-8 candidate values: the recurrence pool of `135` with
the eight proved duplicates removed (`p3L^p5E`, `p5C^p3R`, `p5E^p3R`,
`p5F^p3R`, `p5G^p3R`, `p6E^p2`, `p6I^p2`, `p6J^p2`). -/
noncomputable def a198683EightCandidates : List ℂ :=
  block L1 L7 ++ (block L2 L6 ++ (block [p3L] L5noE ++ (block [p3R] L5 ++
    (block L4 L4 ++ (block L5 [p3L] ++ (block L5r [p3R] ++
      (block L6r L2 ++ block L7 L1)))))))

theorem a198683EightCandidates_length :
    a198683EightCandidates.length = 127 := by
  simp [a198683EightCandidates, block_length, L1, L2, L4, L5, L5noE, L5r,
    L6, L6r, L7, a198683SevenCanonicalReps]

/-! Chunk-membership helpers, one per surviving block. -/

private theorem mem_cand_17 {y : ℂ} (hy : y ∈ L7) :
    principalPow Complex.I y ∈ a198683EightCandidates :=
  List.mem_append_left _ (mem_block (by simp [L1]) hy)

private theorem mem_cand_26 {y : ℂ} (hy : y ∈ L6) :
    principalPow p2 y ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_left _
    (mem_block (by simp [L2]) hy))

private theorem mem_cand_35L {y : ℂ} (hy : y ∈ L5noE) :
    principalPow p3L y ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
    (mem_block (by simp) hy)))

private theorem mem_cand_35R {y : ℂ} (hy : y ∈ L5) :
    principalPow p3R y ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (mem_block (by simp) hy))))

private theorem mem_cand_44 {x y : ℂ} (hx : x ∈ L4) (hy : y ∈ L4) :
    principalPow x y ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ (mem_block hx hy)))))

private theorem mem_cand_53L {x : ℂ} (hx : x ∈ L5) :
    principalPow x p3L ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (mem_block hx (by simp)))))))

private theorem mem_cand_53R {x : ℂ} (hx : x ∈ L5r) :
    principalPow x p3R ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (mem_block hx (by simp))))))))

private theorem mem_cand_62 {x : ℂ} (hx : x ∈ L6r) :
    principalPow x p2 ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _
        (mem_block hx (by simp [L2])))))))))

private theorem mem_cand_71 {x : ℂ} (hx : x ∈ L7) :
    principalPow x Complex.I ∈ a198683EightCandidates :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (mem_block hx (by simp [L1])))))))))

/-- Every level-8 value is one of the `127` pruned recurrence candidates. -/
theorem a198683ValueSet_eight_subset :
    a198683ValueSet 8 ⊆ {z | z ∈ a198683EightCandidates} := by
  intro z hz
  simp only [a198683ValueSet] at hz
  obtain ⟨k, x, hx, y, hy, rfl⟩ := hz
  have hmem7 : ∀ {w : ℂ}, w ∈ a198683ValueSet 7 → w ∈ L7 := by
    intro w hw
    obtain ⟨i, rfl⟩ := a198683_seven_subset_canonicalReps hw
    exact List.get_mem _ i
  fin_cases k <;> norm_num at hx hy ⊢
  · -- split 1 + 7
    rw [mem_valueSet_one] at hx
    subst hx
    exact mem_cand_17 (hmem7 hy)
  · -- split 2 + 6
    replace hx : x = p2 := by rw [mem_valueSet_two] at hx; exact hx
    subst hx
    have hy' : y ∈ L6 := by rw [mem_valueSet_six] at hy; simp [L6]; tauto
    exact mem_cand_26 hy'
  · -- split 3 + 5
    replace hx : x = p3L ∨ x = p3R := by rw [mem_valueSet_three] at hx; exact hx
    rw [mem_valueSet_five] at hy
    rcases hx with rfl | rfl
    · rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact mem_cand_35L (by simp [L5noE])
      · exact mem_cand_35L (by simp [L5noE])
      · exact mem_cand_35L (by simp [L5noE])
      · exact mem_cand_35L (by simp [L5noE])
      · rw [p3L_pow_p5E_redirect]
        exact mem_cand_26 (by simp [L6])
      · exact mem_cand_35L (by simp [L5noE])
      · exact mem_cand_35L (by simp [L5noE])
    · have hy' : y ∈ L5 := by simp [L5]; tauto
      exact mem_cand_35R hy'
  · -- split 4 + 4
    rw [mem_valueSet_four] at hx hy
    have hx' : x ∈ L4 := by simp [L4]; tauto
    have hy' : y ∈ L4 := by simp [L4]; tauto
    exact mem_cand_44 hx' hy'
  · -- split 5 + 3
    rw [mem_valueSet_five] at hx
    replace hy : y = p3L ∨ y = p3R := by rw [mem_valueSet_three] at hy; exact hy
    rcases hy with rfl | rfl
    · have hx' : x ∈ L5 := by simp [L5]; tauto
      exact mem_cand_53L hx'
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact mem_cand_53R (by simp [L5r])
      · exact mem_cand_53R (by simp [L5r])
      · rw [p5C_pow_p3R_redirect]
        exact mem_cand_44 (by simp [L4]) (by simp [L4])
      · exact mem_cand_53R (by simp [L5r])
      · rw [p5E_pow_p3R_redirect]
        exact mem_cand_35R (by simp [L5])
      · rw [p5F_pow_p3R_redirect]
        exact mem_cand_62 (by simp [L6r])
      · rw [p5G_pow_p3R_redirect]
        exact mem_cand_26 (by simp [L6])
  · -- split 6 + 2
    rw [mem_valueSet_six] at hx
    replace hy : y = p2 := by rw [mem_valueSet_two] at hy; exact hy
    subst hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · rw [p6E_pow_p2_redirect]
      exact mem_cand_26 (by simp [L6])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · rw [p6I_pow_p2_redirect]
      exact mem_cand_44 (by simp [L4]) (by simp [L4])
    · rw [p6J_pow_p2_redirect]
      exact mem_cand_44 (by simp [L4]) (by simp [L4])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
    · exact mem_cand_62 (by simp [L6r])
  · -- split 7 + 1
    rw [mem_valueSet_one] at hy
    subst hy
    exact mem_cand_71 (hmem7 hx)

/-- The level-8 value set is finite. -/
theorem a198683ValueSet_eight_finite : (a198683ValueSet 8).Finite := by
  classical
  refine Set.Finite.subset (a198683EightCandidates.toFinset.finite_toSet) ?_
  intro z hz
  simpa using a198683ValueSet_eight_subset hz

/-- **Unconditional upper bound at `n = 8`**: the recurrence pool minus the
eight proved island merges. -/
theorem a198683_eight_le : a198683 8 ≤ 127 := by
  classical
  rw [a198683_eq_valueSet_ncard]
  have hsub : a198683ValueSet 8 ⊆ (a198683EightCandidates.toFinset : Set ℂ) := by
    intro z hz
    simpa using a198683ValueSet_eight_subset hz
  calc (a198683ValueSet 8).ncard
      ≤ (a198683EightCandidates.toFinset : Set ℂ).ncard :=
        Set.ncard_le_ncard hsub (a198683EightCandidates.toFinset.finite_toSet)
    _ = a198683EightCandidates.toFinset.card := Set.ncard_coe_finset _
    _ ≤ a198683EightCandidates.length := a198683EightCandidates.toFinset_card_le
    _ = 127 := a198683EightCandidates_length

/-! ## Sixteen pairwise-distinct level-8 values

Fifteen real exponentials whose exponents form a strictly decreasing chain,
plus the non-real `p4A` (which reappears at level 8 as `i^(i^(i^i))` with
the inner tower built from six `i`s through `p6E`). -/

private theorem mem8_17 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 1) (hy : y ∈ a198683ValueSet 7) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨0, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem8_26 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 2) (hy : y ∈ a198683ValueSet 6) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨1, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem8_35 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 3) (hy : y ∈ a198683ValueSet 5) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨2, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem8_44 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 4) (hy : y ∈ a198683ValueSet 4) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨3, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem8_53 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 5) (hy : y ∈ a198683ValueSet 3) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨4, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem8_62 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 6) (hy : y ∈ a198683ValueSet 2) :
    principalPow x y ∈ a198683ValueSet 8 := by
  simp only [a198683ValueSet]
  exact ⟨⟨5, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem mem7_16 {x y : ℂ}
    (hx : x ∈ a198683ValueSet 1) (hy : y ∈ a198683ValueSet 6) :
    principalPow x y ∈ a198683ValueSet 7 := by
  simp only [a198683ValueSet]
  exact ⟨⟨0, by norm_num⟩, x, hx, y, hy, rfl⟩

private theorem hI_mem : Complex.I ∈ a198683ValueSet 1 :=
  mem_valueSet_one.mpr rfl
private theorem hp2_mem : p2 ∈ a198683ValueSet 2 :=
  mem_valueSet_two.mpr rfl
private theorem hp3R_mem : p3R ∈ a198683ValueSet 3 :=
  mem_valueSet_three.mpr (Or.inr rfl)
private theorem hp4B_mem : p4B ∈ a198683ValueSet 4 :=
  mem_valueSet_four.mpr (Or.inr (Or.inl rfl))
private theorem hp4C_mem : p4C ∈ a198683ValueSet 4 :=
  mem_valueSet_four.mpr (Or.inr (Or.inr rfl))
private theorem hp5B_mem : p5B ∈ a198683ValueSet 5 :=
  mem_valueSet_five.mpr (by simp)
private theorem hp5E_mem : p5E ∈ a198683ValueSet 5 :=
  mem_valueSet_five.mpr (by simp)
private theorem hp6E_mem : p6E ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)
private theorem hp6I_mem : p6I ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)
private theorem hp6J_mem : p6J ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)
private theorem hp6L_mem : p6L ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)
private theorem hp6N_mem : p6N ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)
private theorem hp6O_mem : p6O ∈ a198683ValueSet 6 :=
  mem_valueSet_six.mpr (by simp)

/-- The fifteen separated real exponents, in strictly decreasing order. -/
noncomputable def a198683EightSeparatedExponents : List ℝ :=
  [Real.pi / 2 * Real.exp (Real.pi / 2),
   Real.pi / 2,
   beta,
   Real.pi / 2 * Real.exp (-theta),
   theta * rho,
   -(Real.pi / 2) * Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2))),
   -(theta * rho) * rho,
   -theta * Real.exp (-theta),
   -beta * rho,
   -(Real.pi / 2) * rho,
   -(Real.pi / 2) * Real.exp (-beta),
   -(Real.pi / 2) * Real.exp (-(Real.pi / 2 * Real.exp (-theta))),
   -(Real.pi / 2) * Real.exp (-(theta * rho)),
   -theta * Real.exp (Real.pi / 2),
   -(Real.pi / 2) * Real.exp theta]

private theorem exponents_chain :
    a198683EightSeparatedExponents.IsChain (· > ·) := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ' : Real.pi < 3.15 := Real.pi_lt_d2
  have hρpos : (0 : ℝ) < rho := Real.exp_pos _
  have hρ5 : (1 : ℝ) / 5 < rho := rho_gt_one_div_five
  have hθ3 : (3 : ℝ) / 10 < theta := theta_gt_three_div_ten
  have hθ13 : theta < 1 / 3 := theta_lt_one_div_three
  have hθpos : (0 : ℝ) < theta := theta_pos
  have hβpos : (0 : ℝ) < beta := beta_pos
  have hβhalf : beta < Real.pi / 2 := beta_lt_angleE
  have hCβ : Real.pi / 2 * Real.exp (-theta) < beta := angleC_lt_beta
  have hFC : theta * rho < Real.pi / 2 * Real.exp (-theta) := angleF_lt_angleC
  have hθdef : theta = Real.pi / 2 * rho := rfl
  have hρdef : rho = Real.exp (-(Real.pi / 2)) := rfl
  have hexpθpos : (0 : ℝ) < Real.exp (-theta) := Real.exp_pos _
  have hid : theta * Real.exp (Real.pi / 2) = Real.pi / 2 := by
    rw [hθdef, hρdef, mul_assoc, ← Real.exp_add]
    norm_num
  simp only [a198683EightSeparatedExponents, List.isChain_cons_cons,
    List.isChain_singleton, and_true, gt_iff_lt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- π/2 < π/2 · e^{π/2}
    have h1 : (1 : ℝ) < Real.exp (Real.pi / 2) := by
      have := Real.exp_lt_exp.mpr (show (0 : ℝ) < Real.pi / 2 by linarith)
      simpa using this
    nlinarith
  · -- β < π/2
    exact hβhalf
  · -- π/2 · e^{-θ} < β
    exact hCβ
  · -- θρ < π/2 · e^{-θ}
    exact hFC
  · -- -(π/2)·e^{-(π/2 e^{π/2})} < θρ
    have := Real.exp_pos (-(Real.pi / 2 * Real.exp (Real.pi / 2)))
    nlinarith
  · -- -(θρ)ρ < -(π/2)·e^{-(π/2 e^{π/2})}  (the one numeric estimate)
    have hE : (24 : ℝ) / 5 < Real.exp (Real.pi / 2) := exp_pi_div_two_gt_24_div_5
    have hbig : (7 : ℝ) < Real.pi / 2 * Real.exp (Real.pi / 2) := by nlinarith
    have hX : Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2))) <
        Real.exp (-7) := Real.exp_lt_exp.mpr (by linarith)
    have h1000 : (1000 : ℝ) < Real.exp 7 := by
      have h27 : (2.7 : ℝ) < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have hpow : Real.exp 7 = Real.exp 1 ^ 7 := by
        rw [← Real.exp_nat_mul]
        norm_num
      rw [hpow]
      calc (1000 : ℝ) < 2.7 ^ 7 := by norm_num
        _ < Real.exp 1 ^ 7 := by gcongr
    have hXsmall : Real.exp (-7) < 1 / 1000 := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) h1000
    have hXpos := Real.exp_pos (-(Real.pi / 2 * Real.exp (Real.pi / 2)))
    have hρ2 : (1 : ℝ) / 25 < rho * rho := by nlinarith
    have htriple : (3 : ℝ) / 250 < theta * rho * rho := by nlinarith
    have hm := mul_lt_mul_of_pos_left (hX.trans hXsmall)
      (show (0 : ℝ) < Real.pi / 2 by linarith)
    linarith
  · -- -θ e^{-θ} < -(θρ)ρ
    have hρρ : rho * rho = Real.exp (-Real.pi) := by
      rw [hρdef, ← Real.exp_add]
      congr 1
      ring
    have h : Real.exp (-Real.pi) < Real.exp (-theta) :=
      Real.exp_lt_exp.mpr (by linarith)
    nlinarith [hρρ]
  · -- -βρ < -θ e^{-θ}
    have h : theta * Real.exp (-theta) =
        Real.pi / 2 * Real.exp (-theta) * rho := by
      rw [hθdef]; ring
    nlinarith [mul_lt_mul_of_pos_right hCβ hρpos]
  · -- -(π/2)ρ < -βρ
    nlinarith [mul_lt_mul_of_pos_right hβhalf hρpos]
  · -- -(π/2)e^{-β} < -(π/2)ρ
    have h : Real.exp (-(Real.pi / 2)) < Real.exp (-beta) :=
      Real.exp_lt_exp.mpr (by linarith)
    rw [hρdef]
    nlinarith
  · -- -(π/2)e^{-(π/2 e^{-θ})} < -(π/2)e^{-β}
    have h : Real.exp (-beta) <
        Real.exp (-(Real.pi / 2 * Real.exp (-theta))) :=
      Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  · -- -(π/2)e^{-θρ} < -(π/2)e^{-(π/2 e^{-θ})}
    have h : Real.exp (-(Real.pi / 2 * Real.exp (-theta))) <
        Real.exp (-(theta * rho)) :=
      Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  · -- -θ e^{π/2} < -(π/2)e^{-θρ}
    have h : Real.exp (-(theta * rho)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith)
    nlinarith [hid]
  · -- -(π/2)e^{θ} < -θ e^{π/2}
    have h : (1 : ℝ) < Real.exp theta := by
      have := Real.exp_lt_exp.mpr hθpos
      simpa using this
    nlinarith [hid]

/-- The sixteen separated level-8 values: the non-real `p4A` and the
fifteen real exponentials. -/
noncomputable def a198683EightSeparatedValues : List ℂ :=
  p4A :: a198683EightSeparatedExponents.map fun r => ((Real.exp r : ℝ) : ℂ)

private theorem separatedValues_nodup : a198683EightSeparatedValues.Nodup := by
  have hpair : a198683EightSeparatedExponents.Pairwise (· > ·) :=
    List.isChain_iff_pairwise.mp exponents_chain
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · intro hmem
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hmem
    have him := p4A_im_gt_one_div_two
    rw [← hr] at him
    norm_num [Complex.ofReal_im] at him
  · refine List.Nodup.map ?_ (List.Pairwise.imp ne_of_gt hpair)
    intro a b h
    exact Real.exp_injective (Complex.ofReal_injective h)

private theorem separatedValues_length :
    a198683EightSeparatedValues.length = 16 := by
  simp [a198683EightSeparatedValues, a198683EightSeparatedExponents]

private theorem separatedValues_subset :
    ∀ z ∈ a198683EightSeparatedValues, z ∈ a198683ValueSet 8 := by
  intro z hz
  simp only [a198683EightSeparatedValues, a198683EightSeparatedExponents,
    List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | ⟨r, hr, rfl⟩
  · -- p4A = i^(i^(i^i)) reappears at level 8 as i^(i^p6E)
    have h7 : principalPow Complex.I p6E ∈ a198683ValueSet 7 :=
      mem7_16 hI_mem hp6E_mem
    have h8 : principalPow Complex.I (principalPow Complex.I p6E) ∈
        a198683ValueSet 8 := mem8_17 hI_mem h7
    rw [I_pow_p6E_eq_p3L] at h8
    exact h8
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · rw [← p4B_pow_p4B_eq]; exact mem8_44 hp4B_mem hp4B_mem
    · rw [← p3R_pow_p5E_eq]; exact mem8_35 hp3R_mem hp5E_mem
    · rw [← p5B_pow_p3R_eq]; exact mem8_53 hp5B_mem hp3R_mem
    · rw [← p4B_pow_p4C_eq]; exact mem8_44 hp4B_mem hp4C_mem
    · rw [← p6L_pow_p2_eq]; exact mem8_62 hp6L_mem hp2_mem
    · rw [← p2_pow_p6I_eq]; exact mem8_26 hp2_mem hp6I_mem
    · rw [← p6N_pow_p2_eq]; exact mem8_62 hp6N_mem hp2_mem
    · rw [← p4C_pow_p4C_eq]; exact mem8_44 hp4C_mem hp4C_mem
    · rw [← p6O_pow_p2_eq]; exact mem8_62 hp6O_mem hp2_mem
    · rw [← p2_pow_p6E_eq]; exact mem8_26 hp2_mem hp6E_mem
    · rw [← p2_pow_p6O_eq]; exact mem8_26 hp2_mem hp6O_mem
    · rw [← p2_pow_p6J_eq]; exact mem8_26 hp2_mem hp6J_mem
    · rw [← p2_pow_p6N_eq]; exact mem8_26 hp2_mem hp6N_mem
    · rw [← p4C_pow_p4B_eq]; exact mem8_44 hp4C_mem hp4B_mem
    · rw [← p2_pow_p6L_eq]; exact mem8_26 hp2_mem hp6L_mem

/-- **Unconditional lower bound at `n = 8`**: sixteen pairwise-distinct
level-8 values. -/
theorem a198683_eight_ge : 16 ≤ a198683 8 := by
  classical
  rw [a198683_eq_valueSet_ncard]
  have hsub : (a198683EightSeparatedValues.toFinset : Set ℂ) ⊆
      a198683ValueSet 8 := by
    intro z hz
    exact separatedValues_subset z (by simpa using hz)
  calc (16 : ℕ) = a198683EightSeparatedValues.toFinset.card := by
        rw [List.toFinset_card_of_nodup separatedValues_nodup,
          separatedValues_length]
    _ = (a198683EightSeparatedValues.toFinset : Set ℂ).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (a198683ValueSet 8).ncard :=
        Set.ncard_le_ncard hsub a198683ValueSet_eight_finite

theorem a198683_eight_pos : 1 ≤ a198683 8 :=
  le_trans (by norm_num) a198683_eight_ge

end LeanProofs
