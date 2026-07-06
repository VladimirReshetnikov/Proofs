import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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

private noncomputable def p6A : ℂ :=
  principalPow Complex.I p5A

private noncomputable def p6B : ℂ :=
  principalPow Complex.I p5B

private noncomputable def p6C : ℂ :=
  principalPow Complex.I p5C

private noncomputable def p6D : ℂ :=
  principalPow Complex.I p5D

private noncomputable def p6E : ℂ :=
  principalPow Complex.I p5E

private noncomputable def p6F : ℂ :=
  principalPow Complex.I p5F

private noncomputable def p6G : ℂ :=
  principalPow Complex.I p5G

private noncomputable def p6H : ℂ :=
  principalPow p2 p4A

private noncomputable def p6I : ℂ :=
  principalPow p2 p4B

private noncomputable def p6J : ℂ :=
  principalPow p2 p4C

private noncomputable def p6K : ℂ :=
  principalPow p3L p3L

private noncomputable def p6L : ℂ :=
  principalPow p3L p3R

private noncomputable def p6M : ℂ :=
  principalPow p3R p3L

private noncomputable def p6N : ℂ :=
  principalPow p4C p2

private noncomputable def p6O : ℂ :=
  principalPow p5B Complex.I

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

private noncomputable def thetaDelta : ℝ :=
  Real.pi / 2 * (1 - Real.cos theta)

private noncomputable def beta : ℝ :=
  Real.pi / 2 * (Real.exp (Real.pi / 2) - 4)

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
  ring_nf

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

private theorem p5B_eq_exp_beta :
    p5B = Complex.exp ((beta : ℂ) * Complex.I) := by
  dsimp [p5B, principalPow]
  rw [log_I_real, p4B_eq_exp_pi_div_two]
  have harg :
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.I * (Real.exp (Real.pi / 2) : ℂ)) =
        (((beta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im, beta]
    · simp [Complex.mul_re, Complex.mul_im, beta]
      ring
  rw [harg]
  rw [show (((beta + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
      (beta : ℂ) * Complex.I + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring_nf

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

private theorem exp_pi_div_two_gt_24_div_5 :
    (24 : ℝ) / 5 < Real.exp (Real.pi / 2) := by
  have hpi : (157 : ℝ) / 100 < Real.pi / 2 := by
    linarith [Real.pi_gt_d2]
  have hsum_le :
      (∑ i ∈ Finset.range 7, ((157 : ℝ) / 100) ^ i / (i.factorial : ℝ)) ≤
        Real.exp ((157 : ℝ) / 100) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 7
  have hsum_gt :
      (24 : ℝ) / 5 <
        ∑ i ∈ Finset.range 7, ((157 : ℝ) / 100) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hsum_gt.trans_le (hsum_le.trans ((Real.exp_le_exp).2 hpi.le))

private theorem exp_pi_div_two_lt_five :
    Real.exp (Real.pi / 2) < 5 := by
  have hpi_log : Real.pi / 2 < Real.log 5 := by
    have hpi : Real.pi / 2 < (1.6094379123 : ℝ) := by
      linarith [Real.pi_lt_d2]
    exact hpi.trans Real.log_five_gt_d9
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)).1 hpi_log

private theorem rho_gt_one_div_five :
    (1 : ℝ) / 5 < rho := by
  dsimp [rho]
  rw [Real.exp_neg]
  simpa [one_div] using
    (one_div_lt_one_div_of_lt (Real.exp_pos (Real.pi / 2)) exp_pi_div_two_lt_five)

private theorem theta_gt_one_div_four :
    (1 : ℝ) / 4 < theta := by
  dsimp [theta]
  have hpi : (157 : ℝ) / 100 < Real.pi / 2 := by
    linarith [Real.pi_gt_d2]
  nlinarith [hpi, rho_gt_one_div_five]

private theorem theta_gt_three_div_ten :
    (3 : ℝ) / 10 < theta := by
  dsimp [theta]
  have hpi : (157 : ℝ) / 100 < Real.pi / 2 := by
    linarith [Real.pi_gt_d2]
  nlinarith [hpi, rho_gt_one_div_five]

private theorem theta_lt_one_div_three :
    theta < (1 : ℝ) / 3 := by
  have hpi : Real.pi / 2 < (63 : ℝ) / 40 := by
    linarith [Real.pi_lt_d2]
  have htheta_mul :
      theta * Real.exp (Real.pi / 2) = Real.pi / 2 := by
    dsimp [theta, rho]
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos (Real.pi / 2)).ne']
  have hexp_pos : 0 < Real.exp (Real.pi / 2) := Real.exp_pos _
  nlinarith [hpi, exp_pi_div_two_gt_24_div_5, htheta_mul, theta_pos, hexp_pos]

private theorem sin_theta_gt_seven_div_thirty :
    (7 : ℝ) / 30 < Real.sin theta := by
  have hquarter : (7 : ℝ) / 30 < Real.sin ((1 : ℝ) / 4) := by
    have h := Real.sin_gt_sub_cube
      (x := (1 : ℝ) / 4) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := (1 : ℝ) / 4) (y := theta)
    (by linarith [Real.pi_pos]) theta_lt_pi_div_two.le theta_gt_one_div_four
  exact hquarter.trans hmono

private theorem sin_theta_gt_twenty_nine_div_hundred :
    (29 : ℝ) / 100 < Real.sin theta := by
  have hthree_tenths : (29 : ℝ) / 100 < Real.sin ((3 : ℝ) / 10) := by
    have h := Real.sin_gt_sub_cube
      (x := (3 : ℝ) / 10) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := (3 : ℝ) / 10) (y := theta)
    (by linarith [Real.pi_pos]) theta_lt_pi_div_two.le theta_gt_three_div_ten
  exact hthree_tenths.trans hmono

private theorem p4A_exp_factor_lt_three_div_four :
    Real.exp (-(Real.pi / 2 * Real.sin theta)) < (3 : ℝ) / 4 := by
  have hu_gt : (1 : ℝ) / 3 < Real.pi / 2 * Real.sin theta := by
    nlinarith [Real.pi_gt_d2, sin_theta_gt_seven_div_thirty]
  rw [Real.exp_neg]
  have hexp_gt : (4 : ℝ) / 3 < Real.exp (Real.pi / 2 * Real.sin theta) := by
    have h := Real.add_one_lt_exp (by nlinarith [hu_gt] :
      Real.pi / 2 * Real.sin theta ≠ 0)
    nlinarith [h, hu_gt]
  have hrec := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < (4 : ℝ) / 3) hexp_gt
  norm_num [one_div] at hrec
  exact hrec

private theorem p4A_exp_factor_lt_two_div_three :
    Real.exp (-(Real.pi / 2 * Real.sin theta)) < (2 : ℝ) / 3 := by
  have hu_gt : (9 : ℝ) / 20 < Real.pi / 2 * Real.sin theta := by
    nlinarith [Real.pi_gt_d2, sin_theta_gt_twenty_nine_div_hundred]
  rw [Real.exp_neg]
  have hsum_le := Real.sum_le_exp_of_nonneg (x := Real.pi / 2 * Real.sin theta)
    (by nlinarith [hu_gt]) 3
  have hsum_gt :
      (3 : ℝ) / 2 <
        ∑ m ∈ Finset.range 3,
          (Real.pi / 2 * Real.sin theta) ^ m / (m.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
    nlinarith [hu_gt]
  have hexp_gt : (3 : ℝ) / 2 < Real.exp (Real.pi / 2 * Real.sin theta) :=
    hsum_gt.trans_le hsum_le
  have hrec := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < (3 : ℝ) / 2) hexp_gt
  norm_num [one_div] at hrec
  exact hrec

private theorem exp_neg_eight_div_fifteen_gt_seven_div_twelve :
    (7 : ℝ) / 12 < Real.exp (-(8 / 15 : ℝ)) := by
  rw [Real.exp_neg]
  have hupper := Real.exp_bound' (x := (8 : ℝ) / 15)
    (by norm_num) (by norm_num) (n := 4) (by norm_num)
  have hpoly :
      (∑ m ∈ Finset.range 4, ((8 : ℝ) / 15) ^ m / (m.factorial : ℝ)) +
          ((8 : ℝ) / 15) ^ 4 * ((4 : ℝ) + 1) / ((Nat.factorial 4 : ℝ) * (4 : ℝ)) <
        (12 : ℝ) / 7 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp_lt : Real.exp ((8 : ℝ) / 15) < (12 : ℝ) / 7 :=
    hupper.trans_lt hpoly
  have hrec := one_div_lt_one_div_of_lt (Real.exp_pos ((8 : ℝ) / 15)) hexp_lt
  norm_num [one_div] at hrec
  exact hrec

private theorem p4A_exp_factor_gt_seven_div_twelve :
    (7 : ℝ) / 12 < Real.exp (-(Real.pi / 2 * Real.sin theta)) := by
  have hu_lt : Real.pi / 2 * Real.sin theta < (8 : ℝ) / 15 := by
    have hsin_le_theta : Real.sin theta ≤ theta := Real.sin_le theta_pos.le
    have hpi : Real.pi < (16 : ℝ) / 5 := by
      linarith [Real.pi_lt_d2]
    nlinarith [Real.pi_pos, hsin_le_theta, theta_lt_one_div_three, hpi]
  have hmono : Real.exp (-(8 / 15 : ℝ)) <
      Real.exp (-(Real.pi / 2 * Real.sin theta)) :=
    (Real.exp_lt_exp).2 (by linarith [hu_lt])
  exact exp_neg_eight_div_fifteen_gt_seven_div_twelve.trans hmono

private theorem thetaDelta_nonneg :
    0 ≤ thetaDelta := by
  dsimp [thetaDelta]
  nlinarith [Real.pi_pos, Real.cos_le_one theta]

private theorem thetaDelta_pos :
    0 < thetaDelta := by
  dsimp [thetaDelta]
  nlinarith [Real.pi_pos, cos_theta_lt_one]

private theorem thetaDelta_lt_four_div_fortyfive :
    thetaDelta < (4 : ℝ) / 45 := by
  dsimp [thetaDelta]
  have hcos_lb := Real.one_sub_sq_div_two_le_cos (x := theta)
  have hdelta_le : Real.pi / 2 * (1 - Real.cos theta) ≤
      Real.pi / 2 * (theta ^ 2 / 2) := by
    nlinarith [Real.pi_pos, hcos_lb]
  have htheta_sq_lt : theta ^ 2 < ((1 : ℝ) / 3) ^ 2 := by
    nlinarith [theta_pos, theta_lt_one_div_three]
  have hpi : Real.pi < (16 : ℝ) / 5 := by
    linarith [Real.pi_lt_d2]
  nlinarith [hdelta_le, htheta_sq_lt, hpi, Real.pi_pos]

private theorem cos_thetaDelta_gt_six_div_seven :
    (6 : ℝ) / 7 < Real.cos thetaDelta := by
  have h := Real.one_sub_sq_div_two_lt_cos (x := thetaDelta)
    (by nlinarith [thetaDelta_pos] : thetaDelta ≠ 0)
  have hsq : thetaDelta ^ 2 < ((4 : ℝ) / 45) ^ 2 := by
    nlinarith [thetaDelta_nonneg, thetaDelta_lt_four_div_fortyfive]
  nlinarith [h, hsq]

private theorem p4A_re_lt_one_div_fifteen :
    p4A.re < (1 : ℝ) / 15 := by
  dsimp [p4A, principalPow]
  rw [Complex.exp_re, log_I_real, p3L_eq_exp_theta]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  norm_num [Real.exp_zero]
  rw [show Real.pi / 2 * Real.cos theta = Real.pi / 2 - thetaDelta by
    dsimp [thetaDelta]
    ring]
  rw [Real.cos_pi_div_two_sub]
  have hsin_le_delta : Real.sin thetaDelta ≤ thetaDelta :=
    Real.sin_le thetaDelta_nonneg
  have hmul_le₁ :
      Real.exp (-(Real.pi / 2 * Real.sin theta)) * Real.sin thetaDelta ≤
        Real.exp (-(Real.pi / 2 * Real.sin theta)) * thetaDelta :=
    mul_le_mul_of_nonneg_left hsin_le_delta (Real.exp_pos _).le
  have hmul_lt₂ :
      Real.exp (-(Real.pi / 2 * Real.sin theta)) * thetaDelta <
        (3 : ℝ) / 4 * ((4 : ℝ) / 45) := by
    calc
      Real.exp (-(Real.pi / 2 * Real.sin theta)) * thetaDelta
          ≤ Real.exp (-(Real.pi / 2 * Real.sin theta)) * ((4 : ℝ) / 45) := by
            exact mul_le_mul_of_nonneg_left thetaDelta_lt_four_div_fortyfive.le
              (Real.exp_pos _).le
      _ < (3 : ℝ) / 4 * ((4 : ℝ) / 45) := by
            exact mul_lt_mul_of_pos_right p4A_exp_factor_lt_three_div_four
              (by norm_num)
  nlinarith [hmul_le₁, hmul_lt₂]

private theorem p4A_im_gt_one_div_two :
    (1 : ℝ) / 2 < p4A.im := by
  dsimp [p4A, principalPow]
  rw [Complex.exp_im, log_I_real, p3L_eq_exp_theta]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  norm_num [Real.exp_zero]
  rw [show Real.pi / 2 * Real.cos theta = Real.pi / 2 - thetaDelta by
    dsimp [thetaDelta]
    ring]
  rw [Real.sin_pi_div_two_sub]
  have hprod :
      (7 : ℝ) / 12 * ((6 : ℝ) / 7) <
        Real.exp (-(Real.pi / 2 * Real.sin theta)) * Real.cos thetaDelta :=
    mul_lt_mul p4A_exp_factor_gt_seven_div_twelve cos_thetaDelta_gt_six_div_seven.le
      (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem p4A_im_lt_three_div_four :
    p4A.im < (3 : ℝ) / 4 := by
  dsimp [p4A, principalPow]
  rw [Complex.exp_im, log_I_real, p3L_eq_exp_theta]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  norm_num [Real.exp_zero]
  have hsin_le_one : Real.sin (Real.pi / 2 * Real.cos theta) ≤ 1 :=
    Real.sin_le_one _
  have hmul_le :
      Real.exp (-(Real.pi / 2 * Real.sin theta)) *
          Real.sin (Real.pi / 2 * Real.cos theta) ≤
        Real.exp (-(Real.pi / 2 * Real.sin theta)) * 1 :=
    mul_le_mul_of_nonneg_left hsin_le_one (Real.exp_pos _).le
  nlinarith [hmul_le, p4A_exp_factor_lt_three_div_four]

private theorem p4A_im_lt_two_div_three :
    p4A.im < (2 : ℝ) / 3 := by
  dsimp [p4A, principalPow]
  rw [Complex.exp_im, log_I_real, p3L_eq_exp_theta]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.exp_re, Complex.exp_im, mul_zero, zero_mul,
    add_zero, sub_zero]
  norm_num [Real.exp_zero]
  have hsin_le_one : Real.sin (Real.pi / 2 * Real.cos theta) ≤ 1 :=
    Real.sin_le_one _
  have hmul_le :
      Real.exp (-(Real.pi / 2 * Real.sin theta)) *
          Real.sin (Real.pi / 2 * Real.cos theta) ≤
        Real.exp (-(Real.pi / 2 * Real.sin theta)) * 1 :=
    mul_le_mul_of_nonneg_left hsin_le_one (Real.exp_pos _).le
  nlinarith [hmul_le, p4A_exp_factor_lt_two_div_three]

private theorem exp_neg_pi_div_three_gt_three_div_ten :
    (3 : ℝ) / 10 < Real.exp (-(Real.pi / 3)) := by
  rw [Real.exp_neg]
  have hx_pos : 0 < Real.pi / 3 := by positivity
  have hx_lt_two : Real.pi / 3 < 2 := by
    linarith [Real.pi_lt_d2]
  have hbound := Real.exp_lt_two_add_div_two_sub hx_pos hx_lt_two
  have hfrac : (2 + Real.pi / 3) / (2 - Real.pi / 3) < (10 : ℝ) / 3 := by
    have hden : 0 < 2 - Real.pi / 3 := by
      linarith [Real.pi_lt_d2]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_lt_d2]
  have hexp_lt : Real.exp (Real.pi / 3) < (10 : ℝ) / 3 :=
    hbound.trans hfrac
  have hrec := one_div_lt_one_div_of_lt (Real.exp_pos (Real.pi / 3)) hexp_lt
  norm_num [one_div] at hrec
  exact hrec

private theorem exp_neg_pi_div_four_lt_one_div_two :
    Real.exp (-(Real.pi / 4)) < (1 : ℝ) / 2 := by
  rw [Real.exp_neg]
  have hsum_le := Real.sum_le_exp_of_nonneg (x := Real.pi / 4) (by positivity) 4
  have hsum_gt :
      (2 : ℝ) < ∑ m ∈ Finset.range 4, (Real.pi / 4) ^ m / (m.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
    nlinarith [Real.pi_gt_d2]
  have hexp_gt : (2 : ℝ) < Real.exp (Real.pi / 4) :=
    hsum_gt.trans_le hsum_le
  have hrec := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (2 : ℝ)) hexp_gt
  norm_num [one_div] at hrec
  exact hrec

private theorem exp_neg_theta_lt_four_div_five :
    Real.exp (-theta) < (4 : ℝ) / 5 := by
  have hmono : Real.exp (-theta) < Real.exp (-(1 : ℝ) / 4) :=
    (Real.exp_lt_exp).2 (by linarith [theta_gt_one_div_four])
  have hquarter : (5 : ℝ) / 4 < Real.exp ((1 : ℝ) / 4) := by
    have h := Real.add_one_lt_exp (by norm_num : ((1 : ℝ) / 4) ≠ 0)
    linarith
  have hrec :
      Real.exp (-(1 : ℝ) / 4) < (4 : ℝ) / 5 := by
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring]
    rw [Real.exp_neg]
    have h :=
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (5 : ℝ) / 4) hquarter
    norm_num [one_div] at h
    exact h
  exact hmono.trans hrec

private theorem beta_pos :
    0 < beta := by
  dsimp [beta]
  nlinarith [Real.pi_pos, exp_pi_div_two_gt_24_div_5]

private theorem beta_lt_angleE :
    beta < Real.pi / 2 := by
  dsimp [beta]
  have hdiff : Real.exp (Real.pi / 2) - 4 < 1 := by
    linarith [exp_pi_div_two_lt_five]
  simpa using
    mul_lt_mul_of_pos_left hdiff (show 0 < Real.pi / 2 by positivity)

private theorem angleC_lt_beta :
    Real.pi / 2 * Real.exp (-theta) < beta := by
  dsimp [beta]
  have hdiff : Real.exp (-theta) < Real.exp (Real.pi / 2) - 4 := by
    linarith [exp_neg_theta_lt_four_div_five, exp_pi_div_two_gt_24_div_5]
  simpa using
    mul_lt_mul_of_pos_left hdiff (show 0 < Real.pi / 2 by positivity)

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

private theorem p5B_ne_p5C :
    p5B ≠ p5C := by
  rw [p5B_eq_exp_beta, p5C_eq_exp_pi_mul_exp_neg_theta]
  apply exp_I_ne_of_angle_ne
  · linarith [beta_pos, Real.pi_pos]
  · exact (beta_lt_angleE.trans angleE_lt_pi).le
  · linarith [angleC_pos, Real.pi_pos]
  · exact (angleC_lt_angleE.trans angleE_lt_pi).le
  · exact ne_of_gt angleC_lt_beta

private theorem p5B_ne_p5E :
    p5B ≠ p5E := by
  intro h
  have h' :
      Complex.exp ((beta : ℂ) * Complex.I) =
        Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [← p5B_eq_exp_beta, ← I_eq_exp_pi_div_two_I, ← p5E_eq_I]
    exact h
  exact (exp_I_ne_of_angle_ne
    (by linarith [beta_pos, Real.pi_pos])
    (beta_lt_angleE.trans angleE_lt_pi).le
    (by linarith [Real.pi_pos])
    angleE_lt_pi.le
    (ne_of_lt beta_lt_angleE)) h'

private theorem p5B_ne_p5F :
    p5B ≠ p5F := by
  rw [p5B_eq_exp_beta, p5F_eq_exp_theta_mul_rho]
  apply exp_I_ne_of_angle_ne
  · linarith [beta_pos, Real.pi_pos]
  · exact (beta_lt_angleE.trans angleE_lt_pi).le
  · linarith [angleF_pos, Real.pi_pos]
  · exact ((angleF_lt_angleC.trans angleC_lt_beta).trans
      (beta_lt_angleE.trans angleE_lt_pi)).le
  · exact ne_of_gt (angleF_lt_angleC.trans angleC_lt_beta)

private theorem p5B_ne_p5G :
    p5B ≠ p5G := by
  rw [p5B_eq_exp_beta, p5G_eq_exp_neg_theta]
  rw [show -(theta : ℂ) * Complex.I = ((-theta : ℝ) : ℂ) * Complex.I by
    norm_num]
  apply exp_I_ne_of_angle_ne
  · linarith [beta_pos, Real.pi_pos]
  · exact (beta_lt_angleE.trans angleE_lt_pi).le
  · linarith [theta_lt_pi_div_two, Real.pi_pos]
  · linarith [theta_pos, Real.pi_pos]
  · exact ne_of_gt (by linarith [beta_pos, theta_pos])

private theorem I_pow_inj_of_norm_le_one {x y : ℂ}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    principalPow Complex.I x = principalPow Complex.I y → x = y := by
  intro h
  dsimp [principalPow] at h
  rw [log_I_real] at h
  have hxabs : |x.re| ≤ 1 := (Complex.abs_re_le_norm x).trans hx
  have hyabs : |y.re| ≤ 1 := (Complex.abs_re_le_norm y).trans hy
  have hxge : -1 ≤ x.re := (abs_le.mp hxabs).1
  have hxle : x.re ≤ 1 := (abs_le.mp hxabs).2
  have hyge : -1 ≤ y.re := (abs_le.mp hyabs).1
  have hyle : y.re ≤ 1 := (abs_le.mp hyabs).2
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (x := ((Real.pi / 2 : ℝ) : ℂ) * Complex.I * x)
    (y := ((Real.pi / 2 : ℝ) : ℂ) * Complex.I * y)
    (by simp [Complex.mul_re, Complex.mul_im]; nlinarith [Real.pi_pos, hxge])
    (by simp [Complex.mul_re, Complex.mul_im]; nlinarith [Real.pi_pos, hxle])
    (by simp [Complex.mul_re, Complex.mul_im]; nlinarith [Real.pi_pos, hyge])
    (by simp [Complex.mul_re, Complex.mul_im]; nlinarith [Real.pi_pos, hyle])
    h
  have hc : (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero
  exact mul_left_cancel₀ hc heq

private theorem I_pow_ne_of_norm_le_one {x y : ℂ}
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : x ≠ y) :
    principalPow Complex.I x ≠ principalPow Complex.I y := by
  intro h
  exact hxy (I_pow_inj_of_norm_le_one hx hy h)

private theorem p5A_norm_le_one : ‖p5A‖ ≤ 1 := p5A_norm_lt_one.le

private theorem p5B_norm_le_one : ‖p5B‖ ≤ 1 := by
  rw [p5B_norm_eq_one]

private theorem p5C_norm_le_one : ‖p5C‖ ≤ 1 := by
  rw [p5C_norm_eq_one]

private theorem p5D_norm_le_one : ‖p5D‖ ≤ 1 := p5D_norm_lt_one.le

private theorem p5E_norm_le_one : ‖p5E‖ ≤ 1 := by
  rw [p5E_norm_eq_one]

private theorem p5F_norm_le_one : ‖p5F‖ ≤ 1 := by
  rw [p5F_norm_eq_one]

private theorem p5G_norm_le_one : ‖p5G‖ ≤ 1 := by
  rw [p5G_norm_eq_one]

private theorem I_pow_re_pos_of_neg_one_lt_re_of_re_lt_one {z : ℂ}
    (hz₁ : -1 < z.re) (hz₂ : z.re < 1) :
    0 < (principalPow Complex.I z).re := by
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos, hz₁, hz₂]

private theorem I_pow_im_pos_of_re_pos_of_norm_le_one {z : ℂ}
    (hzre : 0 < z.re) (hznorm : ‖z‖ ≤ 1) :
    0 < (principalPow Complex.I z).im := by
  dsimp [principalPow]
  rw [log_I_real, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  apply mul_pos
  · positivity
  apply Real.sin_pos_of_mem_Ioo
  constructor
  · nlinarith [Real.pi_pos, hzre]
  · have hzle : z.re ≤ 1 := (Complex.re_le_norm z).trans hznorm
    nlinarith [Real.pi_pos, hzle]

private theorem exp_I_re_pos_of_angle_mem_half {a : ℝ}
    (ha₁ : -(Real.pi / 2) < a) (ha₂ : a < Real.pi / 2) :
    0 < (Complex.exp ((a : ℂ) * Complex.I)).re := by
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  exact Real.cos_pos_of_mem_Ioo ⟨ha₁, ha₂⟩

private theorem p5A_re_pos :
    0 < p5A.re := by
  simpa [p5A] using
    I_pow_re_pos_of_neg_one_lt_re_of_re_lt_one
      (z := p4A) (by linarith [p4A_re_pos]) p4A_re_lt_one

private theorem p5A_re_gt_one_div_four :
    (1 : ℝ) / 4 < p5A.re := by
  dsimp [p5A, principalPow]
  rw [Complex.exp_re, log_I_real]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num
  have hu_lt : Real.pi / 2 * p4A.im < Real.pi / 3 := by
    nlinarith [Real.pi_pos, p4A_im_lt_two_div_three]
  have hexp_gt : (3 : ℝ) / 10 < Real.exp (-(Real.pi / 2 * p4A.im)) := by
    have hmono : Real.exp (-(Real.pi / 3)) <
        Real.exp (-(Real.pi / 2 * p4A.im)) :=
      (Real.exp_lt_exp).2 (by linarith [hu_lt])
    exact exp_neg_pi_div_three_gt_three_div_ten.trans hmono
  have harg_nonneg : 0 ≤ Real.pi / 2 * p4A.re := by
    nlinarith [Real.pi_pos, p4A_re_pos]
  have harg_lt : Real.pi / 2 * p4A.re < (4 : ℝ) / 35 := by
    have harg_lt_pi_div_thirty : Real.pi / 2 * p4A.re < Real.pi / 30 := by
      nlinarith [Real.pi_pos, p4A_re_lt_one_div_fifteen]
    nlinarith [harg_lt_pi_div_thirty, Real.pi_lt_d2]
  have harg_sq_lt : (Real.pi / 2 * p4A.re) ^ 2 < ((4 : ℝ) / 35) ^ 2 := by
    nlinarith [harg_nonneg, harg_lt]
  have hcos_gt : (9 : ℝ) / 10 < Real.cos (Real.pi / 2 * p4A.re) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / 2 * p4A.re)
    nlinarith [h, harg_sq_lt]
  have hprod :
      (3 : ℝ) / 10 * ((9 : ℝ) / 10) <
        Real.exp (-(Real.pi / 2 * p4A.im)) * Real.cos (Real.pi / 2 * p4A.re) :=
    mul_lt_mul hexp_gt hcos_gt.le (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem p5A_im_lt_seven_div_125 :
    p5A.im < (7 : ℝ) / 125 := by
  dsimp [p5A, principalPow]
  rw [Complex.exp_im, log_I_real]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num
  have hu_gt : Real.pi / 4 < Real.pi / 2 * p4A.im := by
    nlinarith [Real.pi_pos, p4A_im_gt_one_div_two]
  have hexp_lt : Real.exp (-(Real.pi / 2 * p4A.im)) < (1 : ℝ) / 2 := by
    have hmono : Real.exp (-(Real.pi / 2 * p4A.im)) < Real.exp (-(Real.pi / 4)) :=
      (Real.exp_lt_exp).2 (by linarith [hu_gt])
    exact hmono.trans exp_neg_pi_div_four_lt_one_div_two
  have harg_nonneg : 0 ≤ Real.pi / 2 * p4A.re := by
    nlinarith [Real.pi_pos, p4A_re_pos]
  have harg_lt : Real.pi / 2 * p4A.re < Real.pi / 30 := by
    nlinarith [Real.pi_pos, p4A_re_lt_one_div_fifteen]
  have hsin_le : Real.sin (Real.pi / 2 * p4A.re) ≤ Real.pi / 2 * p4A.re :=
    Real.sin_le harg_nonneg
  have hmul_le :
      Real.exp (-(Real.pi / 2 * p4A.im)) * Real.sin (Real.pi / 2 * p4A.re) ≤
        Real.exp (-(Real.pi / 2 * p4A.im)) * (Real.pi / 2 * p4A.re) :=
    mul_le_mul_of_nonneg_left hsin_le (Real.exp_pos _).le
  have hmul_lt :
      Real.exp (-(Real.pi / 2 * p4A.im)) * (Real.pi / 2 * p4A.re) <
        (1 : ℝ) / 2 * (Real.pi / 30) := by
    calc
      Real.exp (-(Real.pi / 2 * p4A.im)) * (Real.pi / 2 * p4A.re)
          ≤ Real.exp (-(Real.pi / 2 * p4A.im)) * (Real.pi / 30) := by
            exact mul_le_mul_of_nonneg_left harg_lt.le (Real.exp_pos _).le
      _ < (1 : ℝ) / 2 * (Real.pi / 30) := by
            exact mul_lt_mul_of_pos_right hexp_lt (by positivity)
  nlinarith [hmul_le, hmul_lt, Real.pi_lt_d2]

private theorem p5B_re_pos :
    0 < p5B.re := by
  rw [p5B_eq_exp_beta]
  exact exp_I_re_pos_of_angle_mem_half
    (by linarith [beta_pos, Real.pi_pos]) beta_lt_angleE

private theorem p5C_re_pos :
    0 < p5C.re := by
  rw [p5C_eq_exp_pi_mul_exp_neg_theta]
  exact exp_I_re_pos_of_angle_mem_half
    (by linarith [angleC_pos, Real.pi_pos]) angleC_lt_angleE

private theorem p5D_re_pos :
    0 < p5D.re := by
  dsimp [p5D, principalPow]
  rw [log_p2_eq, p3L_eq_exp_theta, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  apply mul_pos
  · positivity
  apply Real.cos_pos_of_mem_Ioo
  have hsin_lt_one : Real.sin theta < 1 := by
    have hsin_lt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := theta) (y := Real.pi / 2)
      (by linarith [theta_pos, Real.pi_pos])
      (by linarith [Real.pi_pos])
      theta_lt_pi_div_two
    simpa using hsin_lt
  constructor
  · nlinarith [Real.pi_pos, sin_theta_pos]
  · nlinarith [Real.pi_pos, hsin_lt_one]

private theorem p5F_re_pos :
    0 < p5F.re := by
  rw [p5F_eq_exp_theta_mul_rho]
  exact exp_I_re_pos_of_angle_mem_half
    (by linarith [angleF_pos, Real.pi_pos])
    (angleF_lt_angleC.trans angleC_lt_angleE)

private theorem p5F_re_gt_half :
    (1 : ℝ) / 2 < p5F.re := by
  rw [p5F_eq_exp_theta_mul_rho]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hangle_lt_theta : theta * rho < theta :=
    mul_lt_of_lt_one_right theta_pos hrho_lt_one
  have hangle_lt_pi_div_three : theta * rho < Real.pi / 3 := by
    linarith [hangle_lt_theta, theta_lt_one_div_three, Real.pi_gt_d2]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
    (x := theta * rho) (y := Real.pi / 3)
    (by linarith [angleF_pos]) (by linarith [Real.pi_pos]) hangle_lt_pi_div_three
  simpa [Real.cos_pi_div_three] using hcos

private theorem p5G_re_pos :
    0 < p5G.re := by
  rw [p5G_eq_exp_neg_theta]
  rw [show -(theta : ℂ) * Complex.I = ((-theta : ℝ) : ℂ) * Complex.I by
    norm_num]
  exact exp_I_re_pos_of_angle_mem_half
    (by linarith [theta_lt_pi_div_two])
    (by linarith [theta_pos, Real.pi_pos])

private theorem p6A_im_pos :
    0 < p6A.im := by
  simpa [p6A] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5A_re_pos p5A_norm_le_one

private theorem p6B_im_pos :
    0 < p6B.im := by
  simpa [p6B] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5B_re_pos p5B_norm_le_one

private theorem p6C_im_pos :
    0 < p6C.im := by
  simpa [p6C] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5C_re_pos p5C_norm_le_one

private theorem p6D_im_pos :
    0 < p6D.im := by
  simpa [p6D] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5D_re_pos p5D_norm_le_one

private theorem p6F_im_pos :
    0 < p6F.im := by
  simpa [p6F] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5F_re_pos p5F_norm_le_one

private theorem p6G_im_pos :
    0 < p6G.im := by
  simpa [p6G] using
    I_pow_im_pos_of_re_pos_of_norm_le_one p5G_re_pos p5G_norm_le_one

private theorem p6A_ne_p6B : p6A ≠ p6B := by
  simpa [p6A, p6B] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5B_norm_le_one p5A_ne_p5B

private theorem p6A_ne_p6C : p6A ≠ p6C := by
  simpa [p6A, p6C] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5C_norm_le_one p5A_ne_p5C

private theorem p6A_ne_p6D : p6A ≠ p6D := by
  simpa [p6A, p6D] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5D_norm_le_one p5A_ne_p5D

private theorem p6A_ne_p6E : p6A ≠ p6E := by
  simpa [p6A, p6E] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5E_norm_le_one p5A_ne_p5E

private theorem p6A_ne_p6F : p6A ≠ p6F := by
  simpa [p6A, p6F] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5F_norm_le_one p5A_ne_p5F

private theorem p6A_ne_p6G : p6A ≠ p6G := by
  simpa [p6A, p6G] using
    I_pow_ne_of_norm_le_one p5A_norm_le_one p5G_norm_le_one p5A_ne_p5G

private theorem p6B_ne_p6C : p6B ≠ p6C := by
  simpa [p6B, p6C] using
    I_pow_ne_of_norm_le_one p5B_norm_le_one p5C_norm_le_one p5B_ne_p5C

private theorem p6B_ne_p6D : p6B ≠ p6D := by
  simpa [p6B, p6D] using
    I_pow_ne_of_norm_le_one p5B_norm_le_one p5D_norm_le_one p5D_ne_p5B.symm

private theorem p6B_ne_p6E : p6B ≠ p6E := by
  simpa [p6B, p6E] using
    I_pow_ne_of_norm_le_one p5B_norm_le_one p5E_norm_le_one p5B_ne_p5E

private theorem p6B_ne_p6F : p6B ≠ p6F := by
  simpa [p6B, p6F] using
    I_pow_ne_of_norm_le_one p5B_norm_le_one p5F_norm_le_one p5B_ne_p5F

private theorem p6B_ne_p6G : p6B ≠ p6G := by
  simpa [p6B, p6G] using
    I_pow_ne_of_norm_le_one p5B_norm_le_one p5G_norm_le_one p5B_ne_p5G

private theorem p6C_ne_p6D : p6C ≠ p6D := by
  simpa [p6C, p6D] using
    I_pow_ne_of_norm_le_one p5C_norm_le_one p5D_norm_le_one p5D_ne_p5C.symm

private theorem p6C_ne_p6E : p6C ≠ p6E := by
  simpa [p6C, p6E] using
    I_pow_ne_of_norm_le_one p5C_norm_le_one p5E_norm_le_one p5C_ne_p5E

private theorem p6C_ne_p6F : p6C ≠ p6F := by
  simpa [p6C, p6F] using
    I_pow_ne_of_norm_le_one p5C_norm_le_one p5F_norm_le_one p5F_ne_p5C.symm

private theorem p6C_ne_p6G : p6C ≠ p6G := by
  simpa [p6C, p6G] using
    I_pow_ne_of_norm_le_one p5C_norm_le_one p5G_norm_le_one p5G_ne_p5C.symm

private theorem p6D_ne_p6E : p6D ≠ p6E := by
  simpa [p6D, p6E] using
    I_pow_ne_of_norm_le_one p5D_norm_le_one p5E_norm_le_one p5D_ne_p5E

private theorem p6D_ne_p6F : p6D ≠ p6F := by
  simpa [p6D, p6F] using
    I_pow_ne_of_norm_le_one p5D_norm_le_one p5F_norm_le_one p5D_ne_p5F

private theorem p6D_ne_p6G : p6D ≠ p6G := by
  simpa [p6D, p6G] using
    I_pow_ne_of_norm_le_one p5D_norm_le_one p5G_norm_le_one p5D_ne_p5G

private theorem p6E_ne_p6F : p6E ≠ p6F := by
  simpa [p6E, p6F] using
    I_pow_ne_of_norm_le_one p5E_norm_le_one p5F_norm_le_one p5F_ne_p5E.symm

private theorem p6E_ne_p6G : p6E ≠ p6G := by
  simpa [p6E, p6G] using
    I_pow_ne_of_norm_le_one p5E_norm_le_one p5G_norm_le_one p5G_ne_p5E.symm

private theorem p6F_ne_p6G : p6F ≠ p6G := by
  simpa [p6F, p6G] using
    I_pow_ne_of_norm_le_one p5F_norm_le_one p5G_norm_le_one p5G_ne_p5F.symm

private theorem log_p5A_eq :
    Complex.log p5A = Complex.log Complex.I * p4A := by
  dsimp [p5A, principalPow]
  rw [Complex.log_exp]
  · rw [log_I_real]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
    nlinarith [Real.pi_pos, p4A_re_pos]
  · rw [log_I_real]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
    nlinarith [Real.pi_pos, p4A_re_lt_one]

private theorem log_p5C_eq :
    Complex.log p5C = ((Real.pi / 2 * Real.exp (-theta) : ℝ) : ℂ) * Complex.I := by
  dsimp [p5C, principalPow]
  rw [log_I_real, p4C_eq_exp_neg_theta]
  have harg :
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.I * (Real.exp (-theta) : ℂ)) =
        ((Real.pi / 2 * Real.exp (-theta) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [harg]
  rw [Complex.log_exp]
  · simp [Complex.mul_re, Complex.mul_im, Complex.exp_re]
    linarith [Real.pi_pos, angleC_pos]
  · simp [Complex.mul_re, Complex.mul_im, Complex.exp_re]
    exact (angleC_lt_angleE.trans angleE_lt_pi).le

private theorem log_p5D_eq :
    Complex.log p5D = Complex.log p2 * p3L := by
  dsimp [p5D, principalPow]
  rw [Complex.log_exp]
  · rw [log_p2_eq, p3L_eq_exp_theta]
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    have hsin_le_one : Real.sin theta ≤ 1 := Real.sin_le_one theta
    nlinarith [Real.pi_pos, hsin_le_one]
  · rw [log_p2_eq, p3L_eq_exp_theta]
    simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    nlinarith [Real.pi_pos, sin_theta_pos]

private theorem log_p5E_eq :
    Complex.log p5E = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  rw [p5E_eq_I, log_I_real]

private theorem log_p5F_eq :
    Complex.log p5F = ((theta * rho : ℝ) : ℂ) * Complex.I := by
  rw [p5F_eq_exp_theta_mul_rho]
  rw [Complex.log_exp]
  · simp [Complex.mul_im]
    linarith [Real.pi_pos, angleF_pos]
  · simp [Complex.mul_im]
    exact ((angleF_lt_angleC.trans angleC_lt_angleE).trans angleE_lt_pi).le

private theorem log_p5G_eq :
    Complex.log p5G = (-(theta : ℂ) * Complex.I) := by
  rw [p5G_eq_exp_neg_theta]
  rw [Complex.log_exp]
  · simp [Complex.mul_im]
    linarith [theta_lt_pi_div_two, Real.pi_pos]
  · simp [Complex.mul_im]
    linarith [theta_pos, Real.pi_pos]

private theorem p6E_eq_p2 :
    p6E = p2 := by
  dsimp [p6E]
  rw [p5E_eq_I]
  rfl

private theorem p3R_pow_p3R_eq_p6E :
    principalPow p3R p3R = p6E := by
  rw [p6E_eq_p2]
  dsimp [principalPow, p2]
  rw [log_p3R_eq, p3R_eq_neg_I, log_I_real]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p5E_pow_I_eq_p6E :
    principalPow p5E Complex.I = p6E := by
  dsimp [p6E]
  rw [p5E_eq_I]

private theorem p5A_pow_I_eq_p6H :
    principalPow p5A Complex.I = p6H := by
  dsimp [p6H, principalPow]
  rw [log_p5A_eq, log_p2_eq, log_I_real]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p5C_pow_I_eq_p6J :
    principalPow p5C Complex.I = p6J := by
  dsimp [p6J, principalPow]
  rw [log_p5C_eq, log_p2_eq, p4C_eq_exp_neg_theta]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p5D_pow_I_eq_p6M :
    principalPow p5D Complex.I = p6M := by
  dsimp [p6M, principalPow]
  rw [log_p5D_eq, log_p2_eq, log_p3R_eq]
  congr 1
  ring_nf

private theorem p5F_pow_I_eq_p6N :
    principalPow p5F Complex.I = p6N := by
  dsimp [p6N, principalPow]
  rw [log_p5F_eq, log_p4C_eq, p2_eq_rho]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

private theorem p5G_pow_I_eq_p6L :
    principalPow p5G Complex.I = p6L := by
  dsimp [p6L, principalPow]
  rw [log_p5G_eq, log_p3L_eq, p3R_eq_neg_I]
  congr 1
  ring_nf

private theorem p4A_pow_p2_eq_p6K :
    principalPow p4A p2 = p6K := by
  dsimp [p6K, principalPow]
  rw [log_p4A_eq, log_p3L_eq, log_I_real, p2_eq_rho]
  congr 1
  dsimp [theta]
  rw [show (((Real.pi / 2 * rho : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * (rho : ℂ)) by
    norm_num [Complex.ofReal_mul]]
  ring_nf

private theorem p4B_pow_p2_eq_p6L :
    principalPow p4B p2 = p6L := by
  dsimp [p6L, principalPow]
  rw [log_p4B_eq, p2_eq_rho, log_p3L_eq, p3R_eq_neg_I]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, theta]

private theorem p4C_pow_p2_eq_p6N :
    principalPow p4C p2 = p6N := by
  rfl

private theorem p6E_pow_I_eq_p2_pow_p5E :
    principalPow p6E Complex.I = principalPow p2 p5E := by
  rw [p6E_eq_p2, p5E_eq_I]

private theorem p4B_pow_p3R_eq_p2_pow_p5E :
    principalPow p4B p3R = principalPow p2 p5E := by
  dsimp [principalPow]
  rw [log_p4B_eq, p3R_eq_neg_I, log_p2_eq, p5E_eq_I]
  congr 1
  ring_nf

private theorem I_pow_p6E_eq_p3L :
    principalPow Complex.I p6E = p3L := by
  rw [p6E_eq_p2]
  rfl

private theorem p5E_pow_p2_eq_p3L :
    principalPow p5E p2 = p3L := by
  rw [p5E_eq_I]
  rfl

private theorem p4C_pow_p3R_eq_p3L :
    principalPow p4C p3R = p3L := by
  dsimp [principalPow]
  rw [log_p4C_eq, p3R_eq_neg_I, p3L_eq_exp_theta]
  congr 1
  ring_nf

private theorem p6E_eq_exp_neg_pi_div_two :
    p6E = (Real.exp (-(Real.pi / 2)) : ℂ) := by
  rw [p6E_eq_p2, p2_eq_rho]
  rfl

private theorem p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two :
    p6I = (Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2))) : ℂ) := by
  dsimp [p6I, principalPow]
  rw [log_p2_eq, p4B_eq_exp_pi_div_two]
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

private theorem p6J_eq_exp_neg_angleC :
    p6J = (Real.exp (-(Real.pi / 2 * Real.exp (-theta))) : ℂ) := by
  dsimp [p6J, principalPow]
  rw [log_p2_eq, p4C_eq_exp_neg_theta]
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

private theorem p6L_eq_exp_theta :
    p6L = (Real.exp theta : ℂ) := by
  dsimp [p6L, principalPow]
  rw [log_p3L_eq, p3R_eq_neg_I]
  rw [show (theta : ℂ) * Complex.I * (-Complex.I) = (theta : ℂ) by
    calc
      (theta : ℂ) * Complex.I * (-Complex.I) =
          (theta : ℂ) * (Complex.I * (-Complex.I)) := by ring
      _ = (theta : ℂ) * 1 := by rw [mul_neg, Complex.I_mul_I]; ring
      _ = (theta : ℂ) := by ring]
  exact (Complex.ofReal_exp theta).symm

private theorem p6L_pow_I_eq_p3L :
    principalPow p6L Complex.I = p3L := by
  dsimp [principalPow]
  rw [p6L_eq_exp_theta, p3L_eq_exp_theta]
  rw [← Complex.ofReal_log (Real.exp_pos theta).le, Real.log_exp]

private theorem p6N_eq_exp_neg_angleF :
    p6N = (Real.exp (-(theta * rho)) : ℂ) := by
  dsimp [p6N, principalPow]
  rw [log_p4C_eq, p2_eq_rho]
  apply Complex.ext <;> simp [Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im]

private theorem p3L_pow_p4A_eq_p5A_pow_p2 :
    principalPow p3L p4A = principalPow p5A p2 := by
  dsimp [principalPow]
  rw [log_p3L_eq, log_p5A_eq, log_I_real, p2_eq_rho]
  congr 1
  dsimp [theta]
  rw [show (((Real.pi / 2 * rho : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * (rho : ℂ)) by
    norm_num [Complex.ofReal_mul]]
  ring_nf

private theorem p3L_pow_p4C_eq_p5C_pow_p2 :
    principalPow p3L p4C = principalPow p5C p2 := by
  dsimp [principalPow]
  rw [log_p3L_eq, log_p5C_eq, p4C_eq_exp_neg_theta, p2_eq_rho]
  congr 1
  dsimp [theta]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring_nf

private theorem p4C_pow_p3L_eq_p5D_pow_p2 :
    principalPow p4C p3L = principalPow p5D p2 := by
  dsimp [principalPow]
  rw [log_p4C_eq, log_p5D_eq, log_p2_eq, p2_eq_rho]
  congr 1
  dsimp [theta]
  rw [show (((Real.pi / 2 * rho : ℝ) : ℂ) =
      ((Real.pi / 2 : ℝ) : ℂ) * (rho : ℂ)) by
    norm_num [Complex.ofReal_mul]]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring_nf

private theorem p5G_pow_p2_eq_p6N_pow_I :
    principalPow p5G p2 = principalPow p6N Complex.I := by
  dsimp [principalPow]
  rw [log_p5G_eq, p2_eq_rho, p6N_eq_exp_neg_angleF]
  rw [← Complex.ofReal_log (Real.exp_pos (-(theta * rho))).le, Real.log_exp]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_mul]

private theorem p3R_pow_p4C_eq_p6J_pow_I :
    principalPow p3R p4C = principalPow p6J Complex.I := by
  dsimp [principalPow]
  rw [log_p3R_eq, p4C_eq_exp_neg_theta, p6J_eq_exp_neg_angleC]
  rw [← Complex.ofReal_log (Real.exp_pos (-(Real.pi / 2 * Real.exp (-theta)))).le,
    Real.log_exp]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_mul]

private theorem p3R_pow_p4B_eq_p6I_pow_I :
    principalPow p3R p4B = principalPow p6I Complex.I := by
  dsimp [principalPow]
  rw [log_p3R_eq, p4B_eq_exp_pi_div_two, p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]
  rw [← Complex.ofReal_log
      (Real.exp_pos (-(Real.pi / 2 * Real.exp (Real.pi / 2)))).le,
    Real.log_exp]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_mul]

private theorem log_p5B_eq :
    Complex.log p5B = (beta : ℂ) * Complex.I := by
  rw [p5B_eq_exp_beta]
  rw [Complex.log_exp]
  · simp [Complex.mul_im]
    linarith [Real.pi_pos, beta_pos]
  · simp [Complex.mul_im]
    exact (beta_lt_angleE.trans angleE_lt_pi).le

private theorem p6O_eq_exp_neg_beta :
    p6O = (Real.exp (-beta) : ℂ) := by
  dsimp [p6O, principalPow]
  rw [log_p5B_eq]
  rw [show (beta : ℂ) * Complex.I * Complex.I = (-beta : ℂ) by
    calc
      (beta : ℂ) * Complex.I * Complex.I = (beta : ℂ) * (Complex.I * Complex.I) := by ring
      _ = (beta : ℂ) * (-1) := by rw [Complex.I_mul_I]
      _ = (-beta : ℂ) := by ring]
  rw [show -(beta : ℂ) = ((-beta : ℝ) : ℂ) by norm_num]
  exact (Complex.ofReal_exp (-beta)).symm

private theorem p6O_pow_I_eq_p3R_pow_p4B :
    principalPow p6O Complex.I = principalPow p3R p4B := by
  dsimp [principalPow]
  rw [p6O_eq_exp_neg_beta, log_p3R_eq, p4B_eq_exp_pi_div_two]
  rw [← Complex.ofReal_log (Real.exp_pos (-beta)).le, Real.log_exp]
  rw [show (((-beta : ℝ) : ℂ) * Complex.I) =
      (((-(Real.pi / 2) : ℂ) * Complex.I) * (Real.exp (Real.pi / 2) : ℂ)) +
        (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, beta]
    ring_nf]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring_nf

private theorem p6I_re_lt_p6E_re :
    p6I.re < p6E.re := by
  have hI : p6I.re = Real.exp (-(Real.pi / 2 * Real.exp (Real.pi / 2))) := by
    rw [p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]
    exact Complex.ofReal_re _
  have hE : p6E.re = Real.exp (-(Real.pi / 2)) := by
    rw [p6E_eq_exp_neg_pi_div_two]
    exact Complex.ofReal_re _
  rw [hI, hE]
  apply (Real.exp_lt_exp).2
  have hgt : 1 < Real.exp (Real.pi / 2) :=
    Real.one_lt_exp_iff.mpr (by positivity)
  nlinarith [Real.pi_pos, hgt]

private theorem p6E_re_lt_p6O_re :
    p6E.re < p6O.re := by
  have hE : p6E.re = Real.exp (-(Real.pi / 2)) := by
    rw [p6E_eq_exp_neg_pi_div_two]
    exact Complex.ofReal_re _
  have hO : p6O.re = Real.exp (-beta) := by
    rw [p6O_eq_exp_neg_beta]
    exact Complex.ofReal_re _
  rw [hE, hO]
  exact (Real.exp_lt_exp).2 (by linarith [beta_lt_angleE])

private theorem p6O_re_lt_p6J_re :
    p6O.re < p6J.re := by
  have hO : p6O.re = Real.exp (-beta) := by
    rw [p6O_eq_exp_neg_beta]
    exact Complex.ofReal_re _
  have hJ : p6J.re = Real.exp (-(Real.pi / 2 * Real.exp (-theta))) := by
    rw [p6J_eq_exp_neg_angleC]
    exact Complex.ofReal_re _
  rw [hO, hJ]
  exact (Real.exp_lt_exp).2 (by linarith [angleC_lt_beta])

private theorem p6J_re_lt_p6N_re :
    p6J.re < p6N.re := by
  have hJ : p6J.re = Real.exp (-(Real.pi / 2 * Real.exp (-theta))) := by
    rw [p6J_eq_exp_neg_angleC]
    exact Complex.ofReal_re _
  have hN : p6N.re = Real.exp (-(theta * rho)) := by
    rw [p6N_eq_exp_neg_angleF]
    exact Complex.ofReal_re _
  rw [hJ, hN]
  exact (Real.exp_lt_exp).2 (by linarith [angleF_lt_angleC])

private theorem p6N_re_lt_p6L_re :
    p6N.re < p6L.re := by
  have hN : p6N.re = Real.exp (-(theta * rho)) := by
    rw [p6N_eq_exp_neg_angleF]
    exact Complex.ofReal_re _
  have hL : p6L.re = Real.exp theta := by
    rw [p6L_eq_exp_theta]
    exact Complex.ofReal_re _
  rw [hN, hL]
  exact (Real.exp_lt_exp).2 (by linarith [angleF_pos, theta_pos])

private theorem p4A_im_lt_one :
    p4A.im < 1 := by
  have habs : |p4A.im| < 1 := (Complex.abs_im_le_norm p4A).trans_lt p4A_norm_lt_one
  exact lt_of_le_of_lt (le_abs_self p4A.im) habs

private theorem p6H_im_neg :
    p6H.im < 0 := by
  dsimp [p6H, principalPow]
  rw [log_p2_eq, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im]
  have harg_pos : 0 < Real.pi / 2 * p4A.im := by
    nlinarith [Real.pi_pos, p4A_im_pos]
  have harg_lt_pi : Real.pi / 2 * p4A.im < Real.pi := by
    nlinarith [Real.pi_pos, p4A_im_lt_one]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩)

private theorem p6M_im_neg :
    p6M.im < 0 := by
  dsimp [p6M, principalPow]
  rw [log_p3R_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_pos : 0 < Real.pi / 2 * Real.cos theta := by
    nlinarith [Real.pi_pos, hcos_pos]
  have harg_lt_pi : Real.pi / 2 * Real.cos theta < Real.pi := by
    nlinarith [Real.pi_pos, hcos_le_one]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩)

private theorem p6K_im_pos :
    0 < p6K.im := by
  dsimp [p6K, principalPow]
  rw [log_p3L_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_pos : 0 < theta * Real.cos theta := mul_pos theta_pos hcos_pos
  have harg_lt_pi : theta * Real.cos theta < Real.pi := by
    nlinarith [theta_lt_pi_div_two, Real.pi_pos, hcos_le_one, hcos_pos]
  exact mul_pos (by positivity) (Real.sin_pos_of_mem_Ioo ⟨harg_pos, harg_lt_pi⟩)

private theorem p6K_im_lt_one_div_three :
    p6K.im < (1 : ℝ) / 3 := by
  dsimp [p6K, principalPow]
  rw [log_p3L_eq, p3L_eq_exp_theta, Complex.exp_im]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  change Real.exp (-(theta * Real.sin theta)) * Real.sin (theta * Real.cos theta) <
    (3 : ℝ)⁻¹
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_nonneg : 0 ≤ theta * Real.cos theta := by
    nlinarith [theta_pos, hcos_pos]
  have hsin_le : Real.sin (theta * Real.cos theta) ≤ theta * Real.cos theta :=
    Real.sin_le harg_nonneg
  have harg_lt : theta * Real.cos theta < (3 : ℝ)⁻¹ := by
    have h : theta * Real.cos theta < (1 : ℝ) / 3 := by
      nlinarith [theta_pos, theta_lt_one_div_three, hcos_pos, hcos_le_one]
    simpa [one_div] using h
  have hexp_le_one : Real.exp (-(theta * Real.sin theta)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [theta_pos, sin_theta_pos])
  calc
    Real.exp (-(theta * Real.sin theta)) * Real.sin (theta * Real.cos theta)
        ≤ Real.exp (-(theta * Real.sin theta)) * (theta * Real.cos theta) := by
          exact mul_le_mul_of_nonneg_left hsin_le (Real.exp_pos _).le
    _ ≤ theta * Real.cos theta := by
          simpa using mul_le_mul_of_nonneg_right hexp_le_one harg_nonneg
    _ < (3 : ℝ)⁻¹ := harg_lt

private theorem p6A_im_gt_one_div_three :
    (1 : ℝ) / 3 < p6A.im := by
  dsimp [p6A, principalPow]
  rw [Complex.exp_im, log_I_real]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  norm_num
  have hu_pos : 0 < Real.pi / 2 * p5A.im := by
    nlinarith [Real.pi_pos, p5A_im_pos]
  have hu_lt : Real.pi / 2 * p5A.im < (1 : ℝ) / 10 := by
    have hpi_half : Real.pi / 2 < (63 : ℝ) / 40 := by
      linarith [Real.pi_lt_d2]
    nlinarith [hpi_half, p5A_im_lt_seven_div_125, p5A_im_pos]
  have hexp_gt : (9 : ℝ) / 10 < Real.exp (-(Real.pi / 2 * p5A.im)) := by
    have h := Real.one_sub_lt_exp_neg (by nlinarith [hu_pos] :
      Real.pi / 2 * p5A.im ≠ 0)
    nlinarith [h, hu_lt]
  have hsin_pi_eighth_gt : (10 : ℝ) / 27 < Real.sin (Real.pi / 8) := by
    have h := Real.sin_gt_sub_cube
      (x := Real.pi / 8) (by positivity) (by linarith [Real.pi_lt_d2])
    have harg_nonneg : 0 ≤ Real.pi / 8 := by positivity
    have harg_gt : (157 : ℝ) / 400 < Real.pi / 8 := by
      linarith [Real.pi_gt_d2]
    have harg_lt : Real.pi / 8 < (63 : ℝ) / 160 := by
      linarith [Real.pi_lt_d2]
    have hcube_lt : (Real.pi / 8) ^ 3 < ((63 : ℝ) / 160) ^ 3 :=
      pow_lt_pow_left₀ harg_lt harg_nonneg (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith [h, harg_gt, hcube_lt]
  have hp5A_re_le_one : p5A.re ≤ 1 :=
    (Complex.re_le_norm p5A).trans p5A_norm_le_one
  have harg_gt : Real.pi / 8 < Real.pi / 2 * p5A.re := by
    nlinarith [Real.pi_pos, p5A_re_gt_one_div_four]
  have harg_le : Real.pi / 2 * p5A.re ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, hp5A_re_le_one]
  have hsin_gt : (10 : ℝ) / 27 < Real.sin (Real.pi / 2 * p5A.re) := by
    have hmono := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := Real.pi / 8) (y := Real.pi / 2 * p5A.re)
      (by linarith [Real.pi_pos]) harg_le harg_gt
    exact hsin_pi_eighth_gt.trans hmono
  have hprod :
      (9 : ℝ) / 10 * ((10 : ℝ) / 27) <
        Real.exp (-(Real.pi / 2 * p5A.im)) * Real.sin (Real.pi / 2 * p5A.re) :=
    mul_lt_mul hexp_gt hsin_gt.le (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem p6K_re_gt_four_div_five :
    (4 : ℝ) / 5 < p6K.re := by
  dsimp [p6K, principalPow]
  rw [log_p3L_eq, p3L_eq_exp_theta, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hsin_pos : 0 < Real.sin theta := sin_theta_pos
  have hsin_lt_theta : Real.sin theta < theta := Real.sin_lt theta_pos
  have hu_pos : 0 < theta * Real.sin theta := mul_pos theta_pos hsin_pos
  have hu_lt : theta * Real.sin theta < (1 : ℝ) / 9 := by
    nlinarith [theta_pos, theta_lt_one_div_three, hsin_pos, hsin_lt_theta]
  have hexp_lb : (8 : ℝ) / 9 < Real.exp (-(theta * Real.sin theta)) := by
    have h := Real.one_sub_lt_exp_neg hu_pos.ne'
    nlinarith [h, hu_lt]
  have hcos_pos : 0 < Real.cos theta := Real.cos_pos_of_mem_Ioo theta_mem_half
  have hcos_le_one : Real.cos theta ≤ 1 := Real.cos_le_one theta
  have harg_pos : 0 ≤ theta * Real.cos theta := by nlinarith [theta_pos, hcos_pos]
  have harg_lt : theta * Real.cos theta < (1 : ℝ) / 3 := by
    nlinarith [theta_pos, theta_lt_one_div_three, hcos_pos, hcos_le_one]
  have harg_sq_lt : (theta * Real.cos theta) ^ 2 < (1 : ℝ) / 9 := by
    nlinarith [harg_pos, harg_lt]
  have hcos_lb : (17 : ℝ) / 18 < Real.cos (theta * Real.cos theta) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := theta * Real.cos theta)
    nlinarith [h, harg_sq_lt]
  have hprod :
      (8 : ℝ) / 9 * ((17 : ℝ) / 18) <
        Real.exp (-(theta * Real.sin theta)) * Real.cos (theta * Real.cos theta) :=
    mul_lt_mul hexp_lb hcos_lb.le (by norm_num) (Real.exp_pos _).le
  nlinarith [hprod]

private theorem exp_neg_pi_div_four_lt_four_div_five :
    Real.exp (-(Real.pi / 4)) < (4 : ℝ) / 5 := by
  rw [Real.exp_neg]
  have hquarter : (1 : ℝ) / 4 < Real.pi / 4 := by
    linarith [Real.pi_gt_d2]
  have h_exp_quarter : (5 : ℝ) / 4 < Real.exp ((1 : ℝ) / 4) := by
    have h := Real.add_one_lt_exp (by norm_num : ((1 : ℝ) / 4) ≠ 0)
    linarith
  have h_exp_pi : (5 : ℝ) / 4 < Real.exp (Real.pi / 4) :=
    h_exp_quarter.trans ((Real.exp_lt_exp).2 hquarter)
  have hrec := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < (5 : ℝ) / 4) h_exp_pi
  norm_num [one_div] at hrec
  exact hrec

private theorem cos_pi_div_four_lt_four_div_five :
    Real.cos (Real.pi / 4) < (4 : ℝ) / 5 := by
  rw [Real.cos_pi_div_four]
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith

private theorem p6B_norm_lt_four_div_five :
    ‖p6B‖ < (4 : ℝ) / 5 := by
  dsimp [p6B, principalPow]
  rw [Complex.norm_exp, log_I_real, p5B_eq_exp_beta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hbeta_gt_pi_div_six : Real.pi / 6 < beta := by
    dsimp [beta]
    nlinarith [Real.pi_pos, exp_pi_div_two_gt_24_div_5]
  have hsin_gt_half : (1 : ℝ) / 2 < Real.sin beta := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := Real.pi / 6) (y := beta)
      (by linarith [Real.pi_pos])
      beta_lt_angleE.le
      hbeta_gt_pi_div_six
    simpa [Real.sin_pi_div_six] using h
  have harg_gt : Real.pi / 4 < Real.pi / 2 * Real.sin beta := by
    nlinarith [Real.pi_pos, hsin_gt_half]
  exact ((Real.exp_lt_exp).2 (by linarith)).trans exp_neg_pi_div_four_lt_four_div_five

private theorem p6C_norm_lt_four_div_five :
    ‖p6C‖ < (4 : ℝ) / 5 := by
  dsimp [p6C, principalPow]
  rw [Complex.norm_exp, log_I_real, p5C_eq_exp_pi_mul_exp_neg_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have h_exp_neg_theta_gt_two_div_three :
      (2 : ℝ) / 3 < Real.exp (-theta) := by
    have h := Real.one_sub_lt_exp_neg theta_pos.ne'
    nlinarith [h, theta_lt_one_div_three]
  have hangle_gt_pi_div_six : Real.pi / 6 < Real.pi / 2 * Real.exp (-theta) := by
    nlinarith [Real.pi_pos, h_exp_neg_theta_gt_two_div_three]
  have hsin_gt_half : (1 : ℝ) / 2 < Real.sin (Real.pi / 2 * Real.exp (-theta)) := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (x := Real.pi / 6) (y := Real.pi / 2 * Real.exp (-theta))
      (by linarith [Real.pi_pos])
      angleC_lt_angleE.le
      hangle_gt_pi_div_six
    simpa [Real.sin_pi_div_six] using h
  have harg_gt : Real.pi / 4 < Real.pi / 2 * Real.sin (Real.pi / 2 * Real.exp (-theta)) := by
    nlinarith [Real.pi_pos, hsin_gt_half]
  exact ((Real.exp_lt_exp).2 (by linarith)).trans exp_neg_pi_div_four_lt_four_div_five

private theorem p6B_re_lt_four_div_five :
    p6B.re < (4 : ℝ) / 5 :=
  (Complex.re_le_norm p6B).trans_lt p6B_norm_lt_four_div_five

private theorem p6C_re_lt_four_div_five :
    p6C.re < (4 : ℝ) / 5 :=
  (Complex.re_le_norm p6C).trans_lt p6C_norm_lt_four_div_five

private theorem p6F_re_lt_four_div_five :
    p6F.re < (4 : ℝ) / 5 := by
  dsimp [p6F, principalPow]
  rw [Complex.exp_re, log_I_real]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, sub_zero]
  rw [show 0 - Real.pi / 2 * 1 * p5F.im = -(Real.pi / 2 * p5F.im) by ring,
    show 0 + Real.pi / 2 * 1 * p5F.re = Real.pi / 2 * p5F.re by ring]
  have hp5F_re_le_one : p5F.re ≤ 1 :=
    (Complex.re_le_norm p5F).trans p5F_norm_le_one
  have harg_gt : Real.pi / 4 < Real.pi / 2 * p5F.re := by
    nlinarith [Real.pi_pos, p5F_re_gt_half]
  have harg_le : Real.pi / 2 * p5F.re ≤ Real.pi / 2 := by
    nlinarith [Real.pi_pos, hp5F_re_le_one]
  have hcos_lt_cos :
      Real.cos (Real.pi / 2 * p5F.re) < Real.cos (Real.pi / 4) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two
      (x := Real.pi / 4) (y := Real.pi / 2 * p5F.re)
      (by positivity) harg_le harg_gt
  have hcos_lt : Real.cos (Real.pi / 2 * p5F.re) < (4 : ℝ) / 5 :=
    hcos_lt_cos.trans cos_pi_div_four_lt_four_div_five
  have hcos_nonneg : 0 ≤ Real.cos (Real.pi / 2 * p5F.re) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [Real.pi_pos, p5F_re_gt_half]
    · exact harg_le
  have hexp_le : Real.exp (-(Real.pi / 2 * p5F.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, p5F_im_pos])
  have hmul_le :
      Real.exp (-(Real.pi / 2 * p5F.im)) * Real.cos (Real.pi / 2 * p5F.re) ≤
        1 * Real.cos (Real.pi / 2 * p5F.re) :=
    mul_le_mul_of_nonneg_right hexp_le hcos_nonneg
  exact lt_of_le_of_lt hmul_le (by simpa using hcos_lt)

private theorem p6E_im_zero :
    p6E.im = 0 := by
  rw [p6E_eq_exp_neg_pi_div_two]
  exact Complex.ofReal_im _

private theorem p6I_im_zero :
    p6I.im = 0 := by
  rw [p6I_eq_exp_neg_pi_div_two_mul_exp_pi_div_two]
  exact Complex.ofReal_im _

private theorem p6J_im_zero :
    p6J.im = 0 := by
  rw [p6J_eq_exp_neg_angleC]
  exact Complex.ofReal_im _

private theorem p6L_im_zero :
    p6L.im = 0 := by
  rw [p6L_eq_exp_theta]
  exact Complex.ofReal_im _

private theorem p6N_im_zero :
    p6N.im = 0 := by
  rw [p6N_eq_exp_neg_angleF]
  exact Complex.ofReal_im _

private theorem p6O_im_zero :
    p6O.im = 0 := by
  rw [p6O_eq_exp_neg_beta]
  exact Complex.ofReal_im _

private theorem p6H_norm_lt_one :
    ‖p6H‖ < 1 := by
  dsimp [p6H, principalPow]
  rw [Complex.norm_exp, log_p2_eq]
  simp [Complex.mul_re]
  have hpos : 0 < Real.pi / 2 * p4A.re := by
    nlinarith [Real.pi_pos, p4A_re_pos]
  exact hpos

private theorem p6M_norm_gt_one :
    1 < ‖p6M‖ := by
  dsimp [p6M, principalPow]
  rw [Complex.norm_exp, log_p3R_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hsin_pos : 0 < Real.sin theta := sin_theta_pos
  have hpos : 0 < Real.pi / 2 * Real.sin theta := by
    nlinarith [Real.pi_pos, hsin_pos]
  exact hpos

private theorem p6K_norm_lt_one :
    ‖p6K‖ < 1 := by
  dsimp [p6K, principalPow]
  rw [Complex.norm_exp, log_p3L_eq, p3L_eq_exp_theta]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
  have hpos : 0 < theta * Real.sin theta := by
    nlinarith [theta_pos, sin_theta_pos]
  exact hpos

private theorem p6D_norm_gt_one :
    1 < ‖p6D‖ := by
  dsimp [p6D, principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  have hpos : Real.pi / 2 * p5D.im < 0 := by
    nlinarith [Real.pi_pos, p5D_im_neg]
  exact hpos

private theorem p6G_norm_gt_one :
    1 < ‖p6G‖ := by
  dsimp [p6G, principalPow]
  rw [Complex.norm_exp, log_I_real]
  simp [Complex.mul_re, Complex.mul_im]
  have hpos : Real.pi / 2 * p5G.im < 0 := by
    nlinarith [Real.pi_pos, p5G_im_neg]
  exact hpos

private theorem p6K_ne_p6D :
    p6K ≠ p6D := by
  intro h
  have hn := congrArg norm h
  have hlt := p6K_norm_lt_one
  rw [hn] at hlt
  linarith [hlt, p6D_norm_gt_one]

private theorem p6K_ne_p6G :
    p6K ≠ p6G := by
  intro h
  have hn := congrArg norm h
  have hlt := p6K_norm_lt_one
  rw [hn] at hlt
  linarith [hlt, p6G_norm_gt_one]

private theorem p6H_ne_p6M :
    p6H ≠ p6M := by
  intro h
  have hn := congrArg norm h
  have hlt := p6H_norm_lt_one
  rw [hn] at hlt
  linarith [hlt, p6M_norm_gt_one]

private theorem ne_of_im_pos_of_im_zero {z w : ℂ}
    (hz : 0 < z.im) (hw : w.im = 0) : z ≠ w := by
  intro h
  have him := congrArg Complex.im h
  linarith

private theorem ne_of_im_neg_of_im_zero {z w : ℂ}
    (hz : z.im < 0) (hw : w.im = 0) : z ≠ w := by
  intro h
  have him := congrArg Complex.im h
  linarith

private theorem ne_of_im_pos_of_im_neg {z w : ℂ}
    (hz : 0 < z.im) (hw : w.im < 0) : z ≠ w := by
  intro h
  have him := congrArg Complex.im h
  linarith

private theorem ne_of_re_lt {z w : ℂ} (h : z.re < w.re) : z ≠ w := by
  intro hz
  have hre := congrArg Complex.re hz
  linarith

private theorem ne_of_im_lt {z w : ℂ} (h : z.im < w.im) : z ≠ w := by
  intro hz
  have him := congrArg Complex.im hz
  linarith

private theorem p6K_ne_p6A :
    p6K ≠ p6A :=
  ne_of_im_lt (p6K_im_lt_one_div_three.trans p6A_im_gt_one_div_three)

private theorem p6K_ne_p6B :
    p6K ≠ p6B :=
  (ne_of_re_lt (p6B_re_lt_four_div_five.trans p6K_re_gt_four_div_five)).symm

private theorem p6K_ne_p6C :
    p6K ≠ p6C :=
  (ne_of_re_lt (p6C_re_lt_four_div_five.trans p6K_re_gt_four_div_five)).symm

private theorem p6K_ne_p6F :
    p6K ≠ p6F :=
  (ne_of_re_lt (p6F_re_lt_four_div_five.trans p6K_re_gt_four_div_five)).symm

private theorem p6I_ne_p6E : p6I ≠ p6E :=
  ne_of_re_lt p6I_re_lt_p6E_re

private theorem p6I_ne_p6O : p6I ≠ p6O :=
  ne_of_re_lt (p6I_re_lt_p6E_re.trans p6E_re_lt_p6O_re)

private theorem p6I_ne_p6J : p6I ≠ p6J :=
  ne_of_re_lt ((p6I_re_lt_p6E_re.trans p6E_re_lt_p6O_re).trans p6O_re_lt_p6J_re)

private theorem p6I_ne_p6N : p6I ≠ p6N :=
  ne_of_re_lt (((p6I_re_lt_p6E_re.trans p6E_re_lt_p6O_re).trans
    p6O_re_lt_p6J_re).trans p6J_re_lt_p6N_re)

private theorem p6I_ne_p6L : p6I ≠ p6L :=
  ne_of_re_lt ((((p6I_re_lt_p6E_re.trans p6E_re_lt_p6O_re).trans
    p6O_re_lt_p6J_re).trans p6J_re_lt_p6N_re).trans p6N_re_lt_p6L_re)

private theorem p6E_ne_p6O : p6E ≠ p6O :=
  ne_of_re_lt p6E_re_lt_p6O_re

private theorem p6E_ne_p6J : p6E ≠ p6J :=
  ne_of_re_lt (p6E_re_lt_p6O_re.trans p6O_re_lt_p6J_re)

private theorem p6E_ne_p6N : p6E ≠ p6N :=
  ne_of_re_lt ((p6E_re_lt_p6O_re.trans p6O_re_lt_p6J_re).trans p6J_re_lt_p6N_re)

private theorem p6E_ne_p6L : p6E ≠ p6L :=
  ne_of_re_lt (((p6E_re_lt_p6O_re.trans p6O_re_lt_p6J_re).trans
    p6J_re_lt_p6N_re).trans p6N_re_lt_p6L_re)

private theorem p6O_ne_p6J : p6O ≠ p6J :=
  ne_of_re_lt p6O_re_lt_p6J_re

private theorem p6O_ne_p6N : p6O ≠ p6N :=
  ne_of_re_lt (p6O_re_lt_p6J_re.trans p6J_re_lt_p6N_re)

private theorem p6O_ne_p6L : p6O ≠ p6L :=
  ne_of_re_lt ((p6O_re_lt_p6J_re.trans p6J_re_lt_p6N_re).trans p6N_re_lt_p6L_re)

private theorem p6J_ne_p6N : p6J ≠ p6N :=
  ne_of_re_lt p6J_re_lt_p6N_re

private theorem p6J_ne_p6L : p6J ≠ p6L :=
  ne_of_re_lt (p6J_re_lt_p6N_re.trans p6N_re_lt_p6L_re)

private theorem p6N_ne_p6L : p6N ≠ p6L :=
  ne_of_re_lt p6N_re_lt_p6L_re

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

private theorem mem_valueSet_five {z : ℂ} :
    z ∈ a198683ValueSet 5 ↔
      z = p5A ∨ z = p5B ∨ z = p5C ∨ z = p5D ∨ z = p5E ∨ z = p5F ∨ z = p5G := by
  rw [valueSet_five_eq_candidates]
  simp

private theorem valueSet_six_eq_candidates :
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

private theorem mem_valueSet_six {z : ℂ} :
    z ∈ a198683ValueSet 6 ↔
      z = p6A ∨ z = p6B ∨ z = p6C ∨ z = p6D ∨ z = p6E ∨ z = p6F ∨ z = p6G ∨
        z = p6H ∨ z = p6I ∨ z = p6J ∨ z = p6K ∨ z = p6L ∨ z = p6M ∨
        z = p6N ∨ z = p6O := by
  rw [valueSet_six_eq_candidates]
  simp

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

/-- `A198683(5) = 7`. -/
theorem a198683_five : a198683 5 = 7 := by
  rw [a198683, valueSet_five_eq_candidates]
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
  rw [a198683, valueSet_six_eq_candidates]
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
  rw [a198683, valueSet_six_eq_candidates]
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

/--
Semantic upper bound for the next OEIS value.  The theorem expands the top
level split using the exact representative sets already proved for `n <= 6`.
-/
theorem a198683_seven_le_fifty_six : a198683 7 ≤ 56 := by
  classical
  rw [a198683]
  let reps : List ℂ :=
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
      principalPow p4B p3R, principalPow p4C p3L, principalPow p4C p3R,
      principalPow p5A p2, principalPow p5B p2, principalPow p5C p2,
      principalPow p5D p2, principalPow p5E p2, principalPow p5F p2,
      principalPow p5G p2,
      principalPow p6A Complex.I, principalPow p6B Complex.I, principalPow p6C Complex.I,
      principalPow p6D Complex.I, principalPow p6E Complex.I, principalPow p6F Complex.I,
      principalPow p6G Complex.I, principalPow p6H Complex.I, principalPow p6I Complex.I,
      principalPow p6J Complex.I, principalPow p6K Complex.I, principalPow p6L Complex.I,
      principalPow p6M Complex.I, principalPow p6N Complex.I, principalPow p6O Complex.I]
  have reps_length : reps.length = 56 := by norm_num [reps]
  let rep : Fin reps.length → ℂ := fun i => reps.get i
  have inRange (i : Nat) (h : i < reps.length) : reps.get ⟨i, h⟩ ∈ Set.range rep := by
    exact ⟨⟨i, h⟩, rfl⟩
  have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
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
        · exact inRange 31 (by rw [reps_length]; norm_num)
      · rcases hy with rfl | rfl
        · exact inRange 32 (by rw [reps_length]; norm_num)
        · exact inRange 33 (by rw [reps_length]; norm_num)
    · change x ∈ a198683ValueSet 5 at hx
      change y ∈ a198683ValueSet 2 at hy
      rw [mem_valueSet_five] at hx
      rw [mem_valueSet_two] at hy
      rcases hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact inRange 34 (by rw [reps_length]; norm_num)
      · exact inRange 35 (by rw [reps_length]; norm_num)
      · exact inRange 36 (by rw [reps_length]; norm_num)
      · exact inRange 37 (by rw [reps_length]; norm_num)
      · exact inRange 38 (by rw [reps_length]; norm_num)
      · exact inRange 39 (by rw [reps_length]; norm_num)
      · exact inRange 40 (by rw [reps_length]; norm_num)
    · change x ∈ a198683ValueSet 6 at hx
      change y ∈ a198683ValueSet 1 at hy
      rw [mem_valueSet_six] at hx
      rw [mem_valueSet_one] at hy
      rcases hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      · exact inRange 41 (by rw [reps_length]; norm_num)
      · exact inRange 42 (by rw [reps_length]; norm_num)
      · exact inRange 43 (by rw [reps_length]; norm_num)
      · exact inRange 44 (by rw [reps_length]; norm_num)
      · exact inRange 45 (by rw [reps_length]; norm_num)
      · exact inRange 46 (by rw [reps_length]; norm_num)
      · exact inRange 47 (by rw [reps_length]; norm_num)
      · exact inRange 48 (by rw [reps_length]; norm_num)
      · exact inRange 49 (by rw [reps_length]; norm_num)
      · exact inRange 50 (by rw [reps_length]; norm_num)
      · exact inRange 51 (by rw [reps_length]; norm_num)
      · exact inRange 52 (by rw [reps_length]; norm_num)
      · exact inRange 53 (by rw [reps_length]; norm_num)
      · exact inRange 54 (by rw [reps_length]; norm_num)
      · exact inRange 55 (by rw [reps_length]; norm_num)
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
    _ ≤ (Finset.univ : Finset (Fin reps.length)).card := Finset.card_image_le
    _ = reps.length := by simp
    _ = 56 := by norm_num [reps]

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

/--
Sharper semantic upper bound for `A198683(7)`.  This removes five duplicates
from the naive top-level cover by normalizing the easiest exact collisions.
-/
theorem a198683_seven_le_fifty_one : a198683 7 ≤ 51 := by
  classical
  rw [a198683]
  let rep : Fin a198683SevenCollapsedReps.length → ℂ :=
    fun i => a198683SevenCollapsedReps.get i
  have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
    simpa [rep] using a198683_seven_subset_collapsedReps
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
    _ ≤ (Finset.univ : Finset (Fin a198683SevenCollapsedReps.length)).card :=
      Finset.card_image_le
    _ = a198683SevenCollapsedReps.length := by simp
    _ = 51 := by norm_num [a198683SevenCollapsedReps]

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

/--
Sharper semantic upper bound for `A198683(7)`.  This further identifies the
straight-line logarithmic collisions that do not require new branch estimates.
-/
theorem a198683_seven_le_forty_five : a198683 7 ≤ 45 := by
  classical
  rw [a198683]
  let rep : Fin a198683SevenMoreCollapsedReps.length → ℂ :=
    fun i => a198683SevenMoreCollapsedReps.get i
  have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
    simpa [rep] using a198683_seven_subset_moreCollapsedReps
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
    _ ≤ (Finset.univ : Finset (Fin a198683SevenMoreCollapsedReps.length)).card :=
      Finset.card_image_le
    _ = a198683SevenMoreCollapsedReps.length := by simp
    _ = 45 := by norm_num [a198683SevenMoreCollapsedReps]

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

theorem a198683_seven_le_forty_four : a198683 7 ≤ 44 := by
  classical
  rw [a198683]
  let rep : Fin a198683SevenPeriodicCollapsedReps.length → ℂ :=
    fun i => a198683SevenPeriodicCollapsedReps.get i
  have hsubset : a198683ValueSet 7 ⊆ Set.range rep := by
    simpa [rep] using a198683_seven_subset_periodicCollapsedReps
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
    _ ≤ (Finset.univ : Finset (Fin a198683SevenPeriodicCollapsedReps.length)).card :=
      Finset.card_image_le
    _ = a198683SevenPeriodicCollapsedReps.length := by simp
    _ = 44 := by norm_num [a198683SevenPeriodicCollapsedReps]

end

end LeanProofs
