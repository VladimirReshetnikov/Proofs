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

end

end LeanProofs
