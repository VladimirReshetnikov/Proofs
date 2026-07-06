import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Initial values of OEIS A198683

OEIS A198683 counts the distinct principal values of all binary
parenthesizations of `i^i^...^i`.  This module defines the value set directly
over `ℂ`, with principal power interpreted as `exp (log z * w)`.

The accepted OEIS data currently run through `n = 11`; `n = 12` is deliberately
not included in the OEIS data field because the local corpus records it as
still awaiting a proof-quality certificate.
-/

namespace LeanProofs

noncomputable section

open Complex

/-- Principal complex power, written separately from Lean's `Pow` instance so
the definition used for the sequence is visible in this module. -/
def principalPow (z w : ℂ) : ℂ :=
  Complex.exp (Complex.log z * w)

/--
The set of values produced by all binary parenthesizations of `n` copies of
`i`, with every binary node interpreted as principal complex power.

The `0` case is an empty convenience case; OEIS A198683 has offset `1`.
-/
def a198683ValueSet : Nat → Set ℂ
  | 0 => ∅
  | 1 => {Complex.I}
  | n + 2 =>
      {z | ∃ k : Fin (n + 1),
        ∃ x ∈ a198683ValueSet (k.1 + 1),
        ∃ y ∈ a198683ValueSet (n + 1 - k.1),
          z = principalPow x y}
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- OEIS A198683, as a cardinality of the semantic value set above. -/
def a198683 (n : Nat) : Nat :=
  (a198683ValueSet n).ncard

private noncomputable def p2 : ℂ :=
  principalPow Complex.I Complex.I

private noncomputable def p3L : ℂ :=
  principalPow Complex.I p2

private noncomputable def p3R : ℂ :=
  principalPow p2 Complex.I

private noncomputable def p4A : ℂ :=
  principalPow Complex.I p3L

private noncomputable def p4B : ℂ :=
  principalPow Complex.I p3R

private noncomputable def p4C : ℂ :=
  principalPow p2 p2

private noncomputable def p5A : ℂ :=
  principalPow Complex.I p4A

private noncomputable def p5B : ℂ :=
  principalPow Complex.I p4B

private noncomputable def p5C : ℂ :=
  principalPow Complex.I p4C

private noncomputable def p5D : ℂ :=
  principalPow p2 p3L

private noncomputable def p5E : ℂ :=
  principalPow p2 p3R

private noncomputable def p5F : ℂ :=
  principalPow p3L p2

private noncomputable def p5G : ℂ :=
  principalPow p3R p2

/-- `A198683(1) = 1`. -/
theorem a198683_one : a198683 1 = 1 := by
  simp [a198683, a198683ValueSet]

/-- `A198683(2) = 1`. -/
theorem a198683_two : a198683 2 = 1 := by
  simp [a198683, a198683ValueSet]

private theorem log_I_real :
    Complex.log Complex.I = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log_I]
  norm_num

private noncomputable def rho : ℝ :=
  Real.exp (-(Real.pi / 2))

private noncomputable def theta : ℝ :=
  Real.pi / 2 * rho

private theorem theta_pos : 0 < theta := by
  dsimp [theta, rho]
  positivity

private theorem theta_lt_pi_div_two : theta < Real.pi / 2 := by
  dsimp [theta, rho]
  have hexp_lt_one : Real.exp (-(Real.pi / 2)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  simpa using mul_lt_mul_of_pos_left hexp_lt_one (show 0 < Real.pi / 2 by positivity)

private theorem neg_pi_lt_theta : -Real.pi < theta := by
  linarith [theta_pos, Real.pi_pos]

private theorem theta_le_pi : theta ≤ Real.pi := by
  linarith [theta_lt_pi_div_two, Real.pi_pos]

private theorem theta_mem_half : theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  constructor <;> linarith [theta_pos, theta_lt_pi_div_two, Real.pi_pos]

private theorem i_pow_i_eq :
    principalPow Complex.I Complex.I = (Real.exp (-(Real.pi / 2)) : ℂ) := by
  dsimp [principalPow]
  rw [log_I_real]
  rw [show (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * Complex.I =
      (-(Real.pi / 2) : ℂ) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  rw [show (-(↑Real.pi / 2) : ℂ) = ↑(-(Real.pi / 2)) by norm_num]
  exact (Complex.ofReal_exp (-(Real.pi / 2))).symm

private theorem i_pow_i_eq_rho :
    principalPow Complex.I Complex.I = (rho : ℂ) := by
  simpa [rho] using i_pow_i_eq

private theorem ii_pow_i_eq_neg_I :
    principalPow (principalPow Complex.I Complex.I) Complex.I = -Complex.I := by
  rw [i_pow_i_eq]
  dsimp [principalPow]
  have hlog :
      Complex.log ((Real.exp (-(Real.pi / 2)) : ℝ) : ℂ) =
        (-(Real.pi / 2) : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    norm_num
  rw [hlog, Complex.exp_mul_I]
  apply Complex.ext <;> simp

private theorem i_pow_ii_re_pos :
    0 < (principalPow Complex.I (principalPow Complex.I Complex.I)).re := by
  rw [i_pow_i_eq]
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
  apply mul_pos
  · positivity
  apply Real.cos_pos_of_mem_Ioo
  have htheta_pos : 0 < Real.pi / 2 * Real.exp (-(Real.pi / 2)) := by positivity
  have hexp_lt_one : Real.exp (-(Real.pi / 2)) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hupper : Real.pi / 2 * Real.exp (-(Real.pi / 2)) < Real.pi / 2 := by
    simpa using mul_lt_mul_of_pos_left hexp_lt_one (show 0 < Real.pi / 2 by positivity)
  constructor <;> linarith [Real.pi_pos, htheta_pos, hupper]

private theorem i_pow_ii_ne_ii_pow_i :
    principalPow Complex.I (principalPow Complex.I Complex.I) ≠
      principalPow (principalPow Complex.I Complex.I) Complex.I := by
  intro h
  have hre := congrArg Complex.re h
  rw [ii_pow_i_eq_neg_I] at hre
  have hzero : (principalPow Complex.I (principalPow Complex.I Complex.I)).re = 0 := by
    simpa using hre
  linarith [i_pow_ii_re_pos]

/-- `A198683(3) = 2`. -/
theorem a198683_three : a198683 3 = 2 := by
  simp [a198683, a198683ValueSet]
  simpa [Set.setOf_or] using Set.ncard_pair (Ne.symm i_pow_ii_ne_ii_pow_i)

private theorem log_neg_I_real :
    Complex.log (-Complex.I) = (-(Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.log_neg_I]
  norm_num

private theorem i_pow_neg_i_eq :
    principalPow Complex.I (-Complex.I) = (Real.exp (Real.pi / 2) : ℂ) := by
  dsimp [principalPow]
  rw [log_I_real]
  rw [show (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) * (-Complex.I) =
      (Real.pi / 2 : ℂ) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  rw [show (↑Real.pi / 2 : ℂ) = ↑(Real.pi / 2) by norm_num]
  exact (Complex.ofReal_exp (Real.pi / 2)).symm

private theorem neg_i_pow_i_eq :
    principalPow (-Complex.I) Complex.I = (Real.exp (Real.pi / 2) : ℂ) := by
  dsimp [principalPow]
  rw [log_neg_I_real]
  rw [show (-(↑(Real.pi / 2) : ℂ) * Complex.I * Complex.I) =
      (Real.pi / 2 : ℂ) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  rw [show (↑Real.pi / 2 : ℂ) = ↑(Real.pi / 2) by norm_num]
  exact (Complex.ofReal_exp (Real.pi / 2)).symm

private theorem v4b_eq_v4e :
    principalPow Complex.I (principalPow (principalPow Complex.I Complex.I) Complex.I) =
      principalPow (principalPow (principalPow Complex.I Complex.I) Complex.I) Complex.I := by
  rw [ii_pow_i_eq_neg_I, i_pow_neg_i_eq, neg_i_pow_i_eq]

private theorem ii_pow_ii_eq_theta :
    principalPow (principalPow Complex.I Complex.I) (principalPow Complex.I Complex.I) =
      (Real.exp (-theta) : ℂ) := by
  rw [i_pow_i_eq_rho]
  dsimp [principalPow]
  have hlog : Complex.log (rho : ℂ) = (-(Real.pi / 2) : ℂ) := by
    dsimp [rho]
    rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
    norm_num
  rw [hlog]
  rw [show (-(↑Real.pi / 2) : ℂ) * (rho : ℂ) = ↑(-theta) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, theta]]
  exact (Complex.ofReal_exp (-theta)).symm

private theorem i_pow_ii_eq_exp_theta :
    principalPow Complex.I (principalPow Complex.I Complex.I) =
      Complex.exp ((theta : ℂ) * Complex.I) := by
  rw [i_pow_i_eq_rho]
  dsimp [principalPow, theta]
  rw [log_I_real]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, rho]

private theorem log_i_pow_ii_eq :
    Complex.log (principalPow Complex.I (principalPow Complex.I Complex.I)) =
      (theta : ℂ) * Complex.I := by
  rw [i_pow_ii_eq_exp_theta]
  rw [Complex.log_exp]
  · simpa [Complex.mul_im] using neg_pi_lt_theta
  · simpa [Complex.mul_im] using theta_le_pi

private theorem i_pow_ii_pow_i_eq_theta :
    principalPow (principalPow Complex.I (principalPow Complex.I Complex.I)) Complex.I =
      (Real.exp (-theta) : ℂ) := by
  change Complex.exp
      (Complex.log (principalPow Complex.I (principalPow Complex.I Complex.I)) * Complex.I) =
    (Real.exp (-theta) : ℂ)
  rw [log_i_pow_ii_eq]
  rw [show ((theta : ℂ) * Complex.I) * Complex.I = (-theta : ℂ) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  rw [show (-↑theta : ℂ) = ↑(-theta) by norm_num]
  exact (Complex.ofReal_exp (-theta)).symm

private theorem v4c_eq_v4d :
    principalPow (principalPow Complex.I Complex.I) (principalPow Complex.I Complex.I) =
      principalPow (principalPow Complex.I (principalPow Complex.I Complex.I)) Complex.I := by
  rw [ii_pow_ii_eq_theta, i_pow_ii_pow_i_eq_theta]

private theorem v4a_im_pos :
    0 <
      (principalPow Complex.I
        (principalPow Complex.I (principalPow Complex.I Complex.I))).im := by
  rw [i_pow_ii_eq_exp_theta]
  change 0 < (Complex.exp
    (Complex.log Complex.I * Complex.exp ((theta : ℂ) * Complex.I))).im
  rw [log_I_real, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_pos : 0 < Real.pi / 2 * Real.cos theta := by positivity
  have harg_lt_pi : Real.pi / 2 * Real.cos theta < Real.pi := by
    have hle : Real.pi / 2 * Real.cos theta ≤ Real.pi / 2 := by
      simpa using mul_le_mul_of_nonneg_left hcos_le (show 0 ≤ Real.pi / 2 by positivity)
    linarith [hle, Real.pi_pos]
  constructor
  · simpa [Real.exp_zero] using harg_pos
  · simpa [Real.exp_zero] using harg_lt_pi

private theorem v4a_ne_v4b :
    principalPow Complex.I (principalPow Complex.I (principalPow Complex.I Complex.I)) ≠
      principalPow Complex.I (principalPow (principalPow Complex.I Complex.I) Complex.I) := by
  intro h
  have him := congrArg Complex.im h
  rw [ii_pow_i_eq_neg_I, i_pow_neg_i_eq] at him
  have hzero :
      (principalPow Complex.I
        (principalPow Complex.I (principalPow Complex.I Complex.I))).im = 0 := by
    rw [him]
    simpa using Complex.ofReal_im (Real.exp (Real.pi / 2))
  linarith [v4a_im_pos]

private theorem v4a_ne_v4c :
    principalPow Complex.I (principalPow Complex.I (principalPow Complex.I Complex.I)) ≠
      principalPow (principalPow Complex.I Complex.I) (principalPow Complex.I Complex.I) := by
  intro h
  have him := congrArg Complex.im h
  rw [ii_pow_ii_eq_theta] at him
  have hzero :
      (principalPow Complex.I
        (principalPow Complex.I (principalPow Complex.I Complex.I))).im = 0 := by
    rw [him]
    simpa using Complex.ofReal_im (Real.exp (-theta))
  linarith [v4a_im_pos]

private theorem v4b_ne_v4c :
    principalPow Complex.I (principalPow (principalPow Complex.I Complex.I) Complex.I) ≠
      principalPow (principalPow Complex.I Complex.I) (principalPow Complex.I Complex.I) := by
  intro h
  rw [ii_pow_i_eq_neg_I, i_pow_neg_i_eq, ii_pow_ii_eq_theta] at h
  have hr : Real.exp (Real.pi / 2) = Real.exp (-theta) := Complex.ofReal_inj.mp h
  have hleft : 1 < Real.exp (Real.pi / 2) := by
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hright : Real.exp (-theta) < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith [theta_pos])
  linarith

private theorem mem_valueSet_one {z : ℂ} :
    z ∈ a198683ValueSet 1 ↔ z = Complex.I := by
  simp [a198683ValueSet]

private theorem mem_valueSet_two {z : ℂ} :
    z ∈ a198683ValueSet 2 ↔ z = principalPow Complex.I Complex.I := by
  simp [a198683ValueSet]

private theorem mem_valueSet_three {z : ℂ} :
    z ∈ a198683ValueSet 3 ↔
      z = principalPow Complex.I (principalPow Complex.I Complex.I) ∨
        z = principalPow (principalPow Complex.I Complex.I) Complex.I := by
  simp [a198683ValueSet]

/-- `A198683(4) = 3`. -/
theorem a198683_four : a198683 4 = 3 := by
  simp [a198683, a198683ValueSet]
  have hset :
      {z | ∃ k : Fin 3,
        ∃ x ∈ a198683ValueSet (k.1 + 1),
        ∃ y ∈ a198683ValueSet (3 - k.1),
          z = principalPow x y} =
        ({principalPow Complex.I (principalPow Complex.I (principalPow Complex.I Complex.I)),
          principalPow Complex.I (principalPow (principalPow Complex.I Complex.I) Complex.I),
          principalPow (principalPow Complex.I Complex.I)
            (principalPow Complex.I Complex.I)} : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨k, x, hx, y, hy, rfl⟩
      fin_cases k
      · change x ∈ a198683ValueSet 1 at hx
        change y ∈ a198683ValueSet 3 at hy
        rw [mem_valueSet_one] at hx
        rw [mem_valueSet_three] at hy
        rcases hx
        rcases hy with rfl | rfl
        · simp
        · simp
      · change x ∈ a198683ValueSet 2 at hx
        change y ∈ a198683ValueSet 2 at hy
        rw [mem_valueSet_two] at hx
        rw [mem_valueSet_two] at hy
        rcases hx
        rcases hy
        simp
      · change x ∈ a198683ValueSet 3 at hx
        change y ∈ a198683ValueSet 1 at hy
        rw [mem_valueSet_three] at hx
        rw [mem_valueSet_one] at hy
        rcases hy
        rcases hx with rfl | rfl
        · simp [v4c_eq_v4d]
        · simp [v4b_eq_v4e]
    · intro hz
      rcases hz with hz | hz | hz
      · refine ⟨0, Complex.I, ?_, principalPow Complex.I (principalPow Complex.I Complex.I), ?_, ?_⟩
        · exact mem_valueSet_one.2 rfl
        · exact mem_valueSet_three.2 (Or.inl rfl)
        · simp [hz]
      · refine ⟨0, Complex.I, ?_,
          principalPow (principalPow Complex.I Complex.I) Complex.I, ?_, ?_⟩
        · exact mem_valueSet_one.2 rfl
        · exact mem_valueSet_three.2 (Or.inr rfl)
        · simp [hz]
      · refine ⟨1, principalPow Complex.I Complex.I, ?_,
          principalPow Complex.I Complex.I, ?_, ?_⟩
        · exact mem_valueSet_two.2 rfl
        · exact mem_valueSet_two.2 rfl
        · simpa [hz]
  rw [hset]
  have hnot :
      principalPow Complex.I
          (principalPow Complex.I (principalPow Complex.I Complex.I)) ∉
        ({principalPow Complex.I (principalPow (principalPow Complex.I Complex.I) Complex.I),
          principalPow (principalPow Complex.I Complex.I)
            (principalPow Complex.I Complex.I)} : Set ℂ) := by
    intro h
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    exact h.elim v4a_ne_v4b v4a_ne_v4c
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_pair v4b_ne_v4c]

private theorem p2_eq_rho :
    p2 = (rho : ℂ) := by
  dsimp [p2]
  exact i_pow_i_eq_rho

private theorem p3L_eq_exp_theta :
    p3L = Complex.exp ((theta : ℂ) * Complex.I) := by
  dsimp [p3L, p2]
  exact i_pow_ii_eq_exp_theta

private theorem p3R_eq_neg_I :
    p3R = -Complex.I := by
  dsimp [p3R, p2]
  exact ii_pow_i_eq_neg_I

private theorem p4B_eq_exp_pi_div_two :
    p4B = (Real.exp (Real.pi / 2) : ℂ) := by
  dsimp [p4B, p3R, p2]
  rw [ii_pow_i_eq_neg_I, i_pow_neg_i_eq]

private theorem p4C_eq_exp_neg_theta :
    p4C = (Real.exp (-theta) : ℂ) := by
  dsimp [p4C, p2]
  exact ii_pow_ii_eq_theta

private theorem log_p2_eq :
    Complex.log p2 = (-(Real.pi / 2) : ℂ) := by
  rw [p2_eq_rho]
  dsimp [rho]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  norm_num

private theorem log_p3R_eq :
    Complex.log p3R = (-(Real.pi / 2) : ℂ) * Complex.I := by
  rw [p3R_eq_neg_I, log_neg_I_real]
  norm_num

private theorem log_p3L_eq :
    Complex.log p3L = (theta : ℂ) * Complex.I := by
  dsimp [p3L, p2]
  exact log_i_pow_ii_eq

private theorem log_p4B_eq :
    Complex.log p4B = (Real.pi / 2 : ℂ) := by
  rw [p4B_eq_exp_pi_div_two]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  norm_num

private theorem log_p4C_eq :
    Complex.log p4C = (-theta : ℂ) := by
  rw [p4C_eq_exp_neg_theta]
  rw [← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  norm_num

private theorem log_p4A_eq :
    Complex.log p4A = Complex.log Complex.I * p3L := by
  dsimp [p4A, p3L, p2, principalPow]
  change Complex.log
      (Complex.exp (Complex.log Complex.I *
        principalPow Complex.I (principalPow Complex.I Complex.I))) =
    Complex.log Complex.I * principalPow Complex.I (principalPow Complex.I Complex.I)
  rw [Complex.log_exp]
  · rw [log_I_real, i_pow_ii_eq_exp_theta]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
      add_zero, sub_zero]
    have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
    have harg_pos : 0 < Real.pi / 2 * Real.cos theta := by positivity
    norm_num [Real.exp_zero] at *
    linarith [Real.pi_pos]
  · rw [log_I_real, i_pow_ii_eq_exp_theta]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
      add_zero, sub_zero]
    have hcos_le : Real.cos theta ≤ 1 := Real.cos_le_one theta
    have hle : Real.pi / 2 * Real.cos theta ≤ Real.pi / 2 := by
      simpa using
        mul_le_mul_of_nonneg_left hcos_le (show 0 ≤ Real.pi / 2 by positivity)
    norm_num [Real.exp_zero] at *
    linarith [hle, Real.pi_pos]

private theorem p4B_pow_I_eq_p5E :
    principalPow p4B Complex.I = p5E := by
  dsimp [p5E, principalPow]
  rw [log_p4B_eq, log_p2_eq, p3R_eq_neg_I]
  congr 1
  ring

private theorem p4C_pow_I_eq_p5G :
    principalPow p4C Complex.I = p5G := by
  dsimp [p5G, principalPow]
  rw [log_p4C_eq, log_p3R_eq, p2_eq_rho]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, theta]

private theorem p4A_pow_I_eq_p5D :
    principalPow p4A Complex.I = p5D := by
  dsimp [p5D, principalPow]
  rw [log_p4A_eq, log_p2_eq, log_I_real]
  congr 1
  calc
    (((Real.pi / 2 : ℝ) : ℂ) * Complex.I * p3L) * Complex.I =
        (((Real.pi / 2 : ℝ) : ℂ) * p3L) * (Complex.I * Complex.I) := by ring
    _ = (((Real.pi / 2 : ℝ) : ℂ) * p3L) * (-1 : ℂ) := by rw [Complex.I_mul_I]
    _ = -(((Real.pi / 2 : ℝ) : ℂ) * p3L) := by ring
    _ = (-(Real.pi / 2) : ℂ) * p3L := by simp [neg_mul]

private theorem p5E_eq_I :
    p5E = Complex.I := by
  dsimp [p5E, principalPow]
  rw [log_p2_eq, p3R_eq_neg_I]
  rw [show (-(Real.pi / 2) : ℂ) * (-Complex.I) =
      (Real.pi / 2 : ℂ) * Complex.I by ring]
  exact Complex.exp_pi_div_two_mul_I

private theorem I_eq_exp_pi_div_two_I :
    Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [show (((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2) by norm_num]
  exact Complex.exp_pi_div_two_mul_I.symm

private theorem p5G_eq_exp_neg_theta :
    p5G = Complex.exp (-(theta : ℂ) * Complex.I) := by
  dsimp [p5G, principalPow]
  rw [log_p3R_eq, p2_eq_rho]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, theta]

private theorem p5F_eq_exp_theta_mul_rho :
    p5F = Complex.exp (((theta * rho : ℝ) : ℂ) * Complex.I) := by
  dsimp [p5F, principalPow]
  rw [log_p3L_eq, p2_eq_rho]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p5C_eq_exp_pi_mul_exp_neg_theta :
    p5C = Complex.exp (((Real.pi / 2 * Real.exp (-theta) : ℝ) : ℂ) * Complex.I) := by
  dsimp [p5C, principalPow]
  rw [log_I_real, p4C_eq_exp_neg_theta]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p4A_im_pos :
    0 < p4A.im := by
  dsimp [p4A, p3L, p2]
  exact v4a_im_pos

private theorem sin_theta_pos :
    0 < Real.sin theta := by
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · exact theta_pos
  · linarith [theta_lt_pi_div_two, Real.pi_pos]

private theorem cos_theta_lt_one :
    Real.cos theta < 1 := by
  refine lt_of_le_of_ne (Real.cos_le_one theta) ?_
  intro h
  have hzero := (Real.cos_eq_one_iff_of_lt_of_lt
    (x := theta) (by linarith [theta_pos, Real.pi_pos])
    (by linarith [theta_lt_pi_div_two, Real.pi_pos])).1 h
  linarith [theta_pos]

private theorem p4A_norm_lt_one :
    ‖p4A‖ < 1 := by
  dsimp [p4A, principalPow]
  rw [Complex.norm_exp, log_I_real, p3L_eq_exp_theta]
  have hre :
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.I *
          Complex.exp ((theta : ℂ) * Complex.I)).re =
        -(Real.pi / 2) * Real.sin theta := by
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, sin_theta_pos])

private theorem p4A_re_lt_one :
    p4A.re < 1 :=
  (Complex.re_le_norm p4A).trans_lt p4A_norm_lt_one

private theorem p4A_re_pos :
    0 < p4A.re := by
  dsimp [p4A, principalPow]
  rw [Complex.exp_re, log_I_real, p3L_eq_exp_theta]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
    norm_num [Real.exp_zero] at *
    nlinarith [Real.pi_pos, hcos_pos]
  · have hlt : Real.pi / 2 * Real.cos theta < Real.pi / 2 := by
      simpa using
        mul_lt_mul_of_pos_left cos_theta_lt_one (show 0 < Real.pi / 2 by positivity)
    norm_num [Real.exp_zero] at *
    linarith [hlt, Real.pi_pos]

private theorem p5A_norm_lt_one :
    ‖p5A‖ < 1 := by
  dsimp [p5A, principalPow]
  rw [Complex.norm_exp, log_I_real]
  have hre :
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.I * p4A).re =
        -(Real.pi / 2) * p4A.im := by
    simp [Complex.mul_re]
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, p4A_im_pos])

private theorem p5D_norm_lt_one :
    ‖p5D‖ < 1 := by
  dsimp [p5D, principalPow]
  rw [Complex.norm_exp, log_p2_eq, p3L_eq_exp_theta]
  have hre :
      ((-(Real.pi / 2) : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)).re =
        -(Real.pi / 2) * Real.cos theta := by
    simp [Complex.mul_re]
  rw [hre]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hcos_pos])

private theorem p5B_norm_eq_one :
    ‖p5B‖ = 1 := by
  dsimp [p5B, principalPow]
  rw [Complex.norm_exp, log_I_real, p4B_eq_exp_pi_div_two]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

private theorem p5C_norm_eq_one :
    ‖p5C‖ = 1 := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta, Complex.norm_exp]
  simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

private theorem p5E_norm_eq_one :
    ‖p5E‖ = 1 := by
  rw [p5E_eq_I]
  simp

private theorem p5F_norm_eq_one :
    ‖p5F‖ = 1 := by
  rw [p5F_eq_exp_theta_mul_rho, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem p5G_norm_eq_one :
    ‖p5G‖ = 1 := by
  rw [p5G_eq_exp_neg_theta, Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_lt_one_ne_norm_one {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ = 1) :
    z ≠ w := by
  intro h
  rw [h, hw] at hz
  exact (lt_irrefl (1 : ℝ)) hz

private theorem exp_I_ne_of_angle_ne {a b : ℝ}
    (ha₁ : -Real.pi < a) (ha₂ : a ≤ Real.pi)
    (hb₁ : -Real.pi < b) (hb₂ : b ≤ Real.pi) (hab : a ≠ b) :
    Complex.exp ((a : ℂ) * Complex.I) ≠ Complex.exp ((b : ℂ) * Complex.I) := by
  intro h
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := (a : ℂ) * Complex.I) (y := (b : ℂ) * Complex.I)
    (by simpa [Complex.mul_re, Complex.mul_im] using ha₁)
    (by simpa [Complex.mul_re, Complex.mul_im] using ha₂)
    (by simpa [Complex.mul_re, Complex.mul_im] using hb₁)
    (by simpa [Complex.mul_re, Complex.mul_im] using hb₂)
    h
  have him := congrArg Complex.im heq
  simp [Complex.mul_im] at him
  exact hab him

private theorem p5A_im_pos :
    0 < p5A.im := by
  dsimp [p5A, principalPow]
  rw [Complex.exp_im, log_I_real]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, p4A_re_pos]
  · nlinarith [Real.pi_pos, p4A_re_lt_one]

private theorem p5D_im_neg :
    p5D.im < 0 := by
  dsimp [p5D, principalPow]
  rw [log_p2_eq, p3L_eq_exp_theta, Complex.exp_im]
  have him :
      (((-(Real.pi / 2) : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)).im) =
        -(Real.pi / 2) * Real.sin theta := by
    simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]
  rw [him]
  apply mul_neg_of_pos_of_neg
  · positivity
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · nlinarith [Real.pi_pos, sin_theta_pos]
  · have hsin_le_one : Real.sin theta ≤ 1 := Real.sin_le_one theta
    nlinarith [Real.pi_pos, hsin_le_one]

private theorem p5A_ne_p5D :
    p5A ≠ p5D := by
  intro h
  have him := congrArg Complex.im h
  linarith [p5A_im_pos, p5D_im_neg]

private theorem p5A_ne_p5B : p5A ≠ p5B :=
  norm_lt_one_ne_norm_one p5A_norm_lt_one p5B_norm_eq_one

private theorem p5A_ne_p5C : p5A ≠ p5C :=
  norm_lt_one_ne_norm_one p5A_norm_lt_one p5C_norm_eq_one

private theorem p5A_ne_p5E : p5A ≠ p5E :=
  norm_lt_one_ne_norm_one p5A_norm_lt_one p5E_norm_eq_one

private theorem p5A_ne_p5F : p5A ≠ p5F :=
  norm_lt_one_ne_norm_one p5A_norm_lt_one p5F_norm_eq_one

private theorem p5A_ne_p5G : p5A ≠ p5G :=
  norm_lt_one_ne_norm_one p5A_norm_lt_one p5G_norm_eq_one

private theorem p5D_ne_p5B : p5D ≠ p5B :=
  norm_lt_one_ne_norm_one p5D_norm_lt_one p5B_norm_eq_one

private theorem p5D_ne_p5C : p5D ≠ p5C :=
  norm_lt_one_ne_norm_one p5D_norm_lt_one p5C_norm_eq_one

private theorem p5D_ne_p5E : p5D ≠ p5E :=
  norm_lt_one_ne_norm_one p5D_norm_lt_one p5E_norm_eq_one

private theorem p5D_ne_p5F : p5D ≠ p5F :=
  norm_lt_one_ne_norm_one p5D_norm_lt_one p5F_norm_eq_one

private theorem p5D_ne_p5G : p5D ≠ p5G :=
  norm_lt_one_ne_norm_one p5D_norm_lt_one p5G_norm_eq_one

private theorem p5G_im_neg :
    p5G.im < 0 := by
  rw [p5G_eq_exp_neg_theta]
  have hsin_pos : 0 < Real.sin theta := by
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · exact theta_pos
    · linarith [theta_lt_pi_div_two, Real.pi_pos]
  have hsin_neg : -Real.sin theta < 0 := by linarith
  simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im] using hsin_neg

private theorem p5F_im_pos :
    0 < p5F.im := by
  rw [p5F_eq_exp_theta_mul_rho]
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    positivity
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have harg_pos : 0 < theta * rho := mul_pos theta_pos hrho_pos
  have harg_lt_pi : theta * rho < Real.pi := by
    have hmul_lt_theta : theta * rho < theta :=
      mul_lt_of_lt_one_right theta_pos hrho_lt_one
    linarith [hmul_lt_theta, theta_lt_pi_div_two, Real.pi_pos]
  have hsin_pos : 0 < Real.sin (theta * rho) :=
    Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩
  simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im] using hsin_pos

private theorem p5C_im_pos :
    0 < p5C.im := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta]
  have harg_pos : 0 < Real.pi / 2 * Real.exp (-theta) := by positivity
  have harg_lt_pi : Real.pi / 2 * Real.exp (-theta) < Real.pi := by
    have hexp_lt_one : Real.exp (-theta) < 1 :=
      Real.exp_lt_one_iff.mpr (by linarith [theta_pos])
    have hle : Real.pi / 2 * Real.exp (-theta) < Real.pi / 2 := by
      exact mul_lt_of_lt_one_right (show 0 < Real.pi / 2 by positivity) hexp_lt_one
    linarith [hle, Real.pi_pos]
  have hsin_pos : 0 < Real.sin (Real.pi / 2 * Real.exp (-theta)) :=
    Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩
  have hexp_re : (Complex.exp (-(theta : ℂ))).re = Real.exp (-theta) := by
    simp [Complex.exp_re]
  have hsin_pos' :
      0 < Real.sin (Real.pi / 2 * (Complex.exp (-(theta : ℂ))).re) := by
    simpa [hexp_re] using hsin_pos
  simpa [Complex.exp_im, Complex.mul_re, Complex.mul_im] using hsin_pos'

private theorem p5E_im_pos :
    0 < p5E.im := by
  rw [p5E_eq_I]
  simp

private theorem p5G_ne_p5C :
    p5G ≠ p5C := by
  intro h
  have him := congrArg Complex.im h
  linarith [p5G_im_neg, p5C_im_pos]

private theorem p5G_ne_p5E :
    p5G ≠ p5E := by
  intro h
  have him := congrArg Complex.im h
  linarith [p5G_im_neg, p5E_im_pos]

private theorem p5G_ne_p5F :
    p5G ≠ p5F := by
  intro h
  have him := congrArg Complex.im h
  linarith [p5G_im_neg, p5F_im_pos]

private theorem angleF_pos :
    0 < theta * rho := by
  exact mul_pos theta_pos (by dsimp [rho]; positivity)

private theorem angleF_lt_angleC :
    theta * rho < Real.pi / 2 * Real.exp (-theta) := by
  have hrho_lt : rho < Real.exp (-theta) := by
    dsimp [rho]
    exact Real.exp_lt_exp.mpr (by linarith [theta_lt_pi_div_two])
  have hrho_pos : 0 < rho := by dsimp [rho]; positivity
  exact mul_lt_mul theta_lt_pi_div_two hrho_lt.le hrho_pos
    (show 0 ≤ Real.pi / 2 by positivity)

private theorem angleC_pos :
    0 < Real.pi / 2 * Real.exp (-theta) := by
  positivity

private theorem angleC_lt_angleE :
    Real.pi / 2 * Real.exp (-theta) < Real.pi / 2 := by
  have hexp_lt_one : Real.exp (-theta) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [theta_pos])
  exact mul_lt_of_lt_one_right (show 0 < Real.pi / 2 by positivity) hexp_lt_one

private theorem angleE_lt_pi :
    Real.pi / 2 < Real.pi := by
  linarith [Real.pi_pos]

private theorem p5F_ne_p5C :
    p5F ≠ p5C := by
  rw [p5F_eq_exp_theta_mul_rho, p5C_eq_exp_pi_mul_exp_neg_theta]
  apply exp_I_ne_of_angle_ne
  · linarith [angleF_pos, Real.pi_pos]
  · exact (angleF_lt_angleC.trans angleC_lt_angleE).le.trans (by linarith [Real.pi_pos])
  · linarith [Real.pi_pos, angleC_pos]
  · exact (angleC_lt_angleE.trans angleE_lt_pi).le
  · exact ne_of_lt angleF_lt_angleC

private theorem p5F_ne_p5E :
    p5F ≠ p5E := by
  intro h
  have h' :
      Complex.exp (((theta * rho : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← p5F_eq_exp_theta_mul_rho, ← I_eq_exp_pi_div_two_I, ← p5E_eq_I]
    exact h
  exact (exp_I_ne_of_angle_ne
    (by linarith [angleF_pos, Real.pi_pos])
    ((angleF_lt_angleC.trans angleC_lt_angleE).le.trans (by linarith [Real.pi_pos]))
    (by linarith [Real.pi_pos])
    angleE_lt_pi.le
    (ne_of_lt (angleF_lt_angleC.trans angleC_lt_angleE))) h'

private theorem p5C_ne_p5E :
    p5C ≠ p5E := by
  intro h
  have h' :
      Complex.exp (((Real.pi / 2 * Real.exp (-theta) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← p5C_eq_exp_pi_mul_exp_neg_theta, ← I_eq_exp_pi_div_two_I, ← p5E_eq_I]
    exact h
  exact (exp_I_ne_of_angle_ne
    (by linarith [Real.pi_pos, angleC_pos])
    (angleC_lt_angleE.trans angleE_lt_pi).le
    (by linarith [Real.pi_pos])
    angleE_lt_pi.le
    (ne_of_lt angleC_lt_angleE)) h'

private theorem mem_valueSet_four {z : ℂ} :
    z ∈ a198683ValueSet 4 ↔ z = p4A ∨ z = p4B ∨ z = p4C := by
  simp only [a198683ValueSet]
  constructor
  · rintro ⟨k, x, hx, y, hy, rfl⟩
    fin_cases k
    · change x ∈ a198683ValueSet 1 at hx
      change y ∈ a198683ValueSet 3 at hy
      rw [mem_valueSet_one] at hx
      rw [mem_valueSet_three] at hy
      rcases hx
      rcases hy with rfl | rfl
      · left
        rfl
      · right
        left
        rfl
    · change x ∈ a198683ValueSet 2 at hx
      change y ∈ a198683ValueSet 2 at hy
      rw [mem_valueSet_two] at hx
      rw [mem_valueSet_two] at hy
      rcases hx
      rcases hy
      right
      right
      rfl
    · change x ∈ a198683ValueSet 3 at hx
      change y ∈ a198683ValueSet 1 at hy
      rw [mem_valueSet_three] at hx
      rw [mem_valueSet_one] at hy
      rcases hy
      rcases hx with rfl | rfl
      · right
        right
        dsimp [p4C, p3L, p2]
        exact v4c_eq_v4d.symm
      · right
        left
        dsimp [p4B, p3R, p2]
        exact v4b_eq_v4e.symm
  · intro hz
    rcases hz with hz | hz | hz
    · refine ⟨0, Complex.I, ?_, p3L, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_three.2 (Or.inl rfl)
      · simp [hz, p4A]
    · refine ⟨0, Complex.I, ?_, p3R, ?_, ?_⟩
      · exact mem_valueSet_one.2 rfl
      · exact mem_valueSet_three.2 (Or.inr rfl)
      · simp [hz, p4B]
    · refine ⟨1, p2, ?_, p2, ?_, ?_⟩
      · exact mem_valueSet_two.2 rfl
      · exact mem_valueSet_two.2 rfl
      · simp [hz, p4C]

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

/-- Semantic upper bound for the next OEIS value: `A198683(5) <= 7`. -/
theorem a198683_five_le_seven : a198683 5 ≤ 7 := by
  rw [a198683, valueSet_five_eq_candidates]
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

end

end LeanProofs
