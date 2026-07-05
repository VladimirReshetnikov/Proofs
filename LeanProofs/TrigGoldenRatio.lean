import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# A golden-ratio trigonometric identity

This module proves the elementary identity
`sin 9° + sin 21° + sin 39° = φ / √2`.
-/

namespace LeanProofs

noncomputable section

open Real
open scoped goldenRatio

/-- The two off-center sine terms collapse by the sum-to-product formula. -/
private lemma sin_twenty_one_add_sin_thirty_nine :
    Real.sin (7 * Real.pi / 60) + Real.sin (13 * Real.pi / 60) =
      Real.cos (Real.pi / 20) := by
  calc
    Real.sin (7 * Real.pi / 60) + Real.sin (13 * Real.pi / 60)
        = 2 * Real.sin (((7 * Real.pi / 60) + (13 * Real.pi / 60)) / 2) *
            Real.cos (((7 * Real.pi / 60) - (13 * Real.pi / 60)) / 2) := by
          rw [Real.sin_add_sin]
    _ = 2 * Real.sin (Real.pi / 6) * Real.cos (-(Real.pi / 20)) := by
          congr 2 <;> ring_nf
    _ = Real.cos (Real.pi / 20) := by
          rw [Real.sin_pi_div_six, Real.cos_neg]
          ring

/-- `sin 9° + cos 9° = √2 cos 36°`. -/
private lemma sin_nine_add_cos_nine :
    Real.sin (Real.pi / 20) + Real.cos (Real.pi / 20) =
      √2 * Real.cos (Real.pi / 5) := by
  calc
    Real.sin (Real.pi / 20) + Real.cos (Real.pi / 20)
        = √2 * Real.sin (Real.pi / 20 + Real.pi / 4) := by
          rw [Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four]
          ring_nf
          rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          ring
    _ = √2 * Real.sin (3 * Real.pi / 10) := by
          congr 1
          ring_nf
    _ = √2 * Real.cos (Real.pi / 5) := by
          rw [← Real.sin_pi_div_two_sub (Real.pi / 5)]
          congr 1
          ring_nf

/-- `√2 cos 36° = φ / √2`, using mathlib's exact value for `cos (π / 5)`. -/
private lemma sqrt_two_mul_cos_thirty_six :
    √2 * Real.cos (Real.pi / 5) = φ / √2 := by
  rw [Real.cos_pi_div_five, Real.goldenRatio]
  field_simp [ne_of_gt (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 2))]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/--
The identity from the image, stated in radians:
`sin 9° + sin 21° + sin 39° = φ / √2`.
-/
theorem sin_deg9_add_sin_deg21_add_sin_deg39 :
    Real.sin (9 * Real.pi / 180) +
        Real.sin (21 * Real.pi / 180) +
        Real.sin (39 * Real.pi / 180) = φ / √2 := by
  rw [show 9 * Real.pi / 180 = Real.pi / 20 by ring_nf,
    show 21 * Real.pi / 180 = 7 * Real.pi / 60 by ring_nf,
    show 39 * Real.pi / 180 = 13 * Real.pi / 60 by ring_nf]
  calc
    Real.sin (Real.pi / 20) +
          Real.sin (7 * Real.pi / 60) +
          Real.sin (13 * Real.pi / 60)
        = Real.sin (Real.pi / 20) + Real.cos (Real.pi / 20) := by
          rw [add_assoc, sin_twenty_one_add_sin_thirty_nine]
    _ = √2 * Real.cos (Real.pi / 5) := sin_nine_add_cos_nine
    _ = φ / √2 := sqrt_two_mul_cos_thirty_six

end

end LeanProofs
