import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# A tiny-exponent power-tower floor

This module proves the numerical identity

```text
floor(10^(10^(10^(10^(10^(-10^10)))))) - 10^(10^10) = 2811012357389.
```

The proof isolates the computation that matters: if
`t = 10^(-10^10)` and `L = log 10`, then the excess over `10^(10^10)` is
controlled by the first derivative `10^11 L^4`, while every higher-order term
is killed by the tiny factor `t`.
-/

namespace LeanProofs

noncomputable section

open Real

private abbrev N : Nat := 10 ^ 10

private abbrev M : Int := 2811012357389

private noncomputable def L : ℝ := log 10

private noncomputable def t : ℝ := (10 : ℝ) ^ (-(N : ℝ))

private noncomputable def u : ℝ := (10 : ℝ) ^ t

private noncomputable def v : ℝ := (10 : ℝ) ^ u

private noncomputable def c : ℝ := (10 : ℝ) ^ v

/-- The full tower on the left-hand side of the challenge identity. -/
noncomputable def tinyExponentTower : ℝ := (10 : ℝ) ^ c

private theorem log_two_near_20 :
    |log 2 - (69314718055994530942 / 100000000000000000000 : ℝ)| ≤ 1 / 10 ^ 20 := by
  suffices |log 2 - (69314718055994530942 / 100000000000000000000 : ℝ)| ≤
      (1 / 2 : ℝ) ^ 85 / (1 - 1 / 2) +
        (1 / 10 ^ 20 - (1 / 2 : ℝ) ^ 85 / (1 - 1 / 2)) by
    norm_num1 at *
    assumption
  have t_abs : |(2⁻¹ : ℝ)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le
    (show |(2⁻¹ : ℝ)| < 1 by rw [t_abs]; norm_num) 85
  rw [t_abs] at z
  norm_num1 at z
  rw [one_div (2 : ℝ), log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  calc
    |log 2 - (69314718055994530942 / 100000000000000000000 : ℝ)| ≤
        |log 2 -
          (6767419353446990359387534777193432446042710369441370775542121 /
            9763322340833968061889948860843352247574157378090622884249600 : ℝ)| +
          |(6767419353446990359387534777193432446042710369441370775542121 /
            9763322340833968061889948860843352247574157378090622884249600 : ℝ) -
            (69314718055994530942 / 100000000000000000000 : ℝ)| := by
      exact _root_.abs_sub_le _ _ _
    _ ≤ (1 / 38685626227668133590597632 : ℝ) +
          (1 / 10 ^ 20 - 1 / 38685626227668133590597632 : ℝ) := by
      apply add_le_add z
      norm_num
    _ = (1 / 2 : ℝ) ^ 85 / (1 - 1 / 2) +
        (1 / 10 ^ 20 - (1 / 2 : ℝ) ^ 85 / (1 - 1 / 2)) := by
      norm_num

private theorem log_five_four_near_20 :
    |log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ)| ≤
      1 / 10 ^ 20 := by
  suffices |log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ)| ≤
      (1 / 5 : ℝ) ^ 37 / (1 - 1 / 5) +
        (1 / 10 ^ 20 - (1 / 5 : ℝ) ^ 37 / (1 - 1 / 5)) by
    norm_num1 at *
    assumption
  have t_abs : |(5⁻¹ : ℝ)| = 5⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le
    (show |(5⁻¹ : ℝ)| < 1 by rw [t_abs]; norm_num) 36
  rw [t_abs] at z
  norm_num1 at z
  rw [show (4 / 5 : ℝ) = (5 / 4 : ℝ)⁻¹ by norm_num, log_inv,
    ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  calc
    |log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ)| ≤
        |log (5 / 4) -
          (18756092534788904164500610557762072271 /
            84053930415306240320205688476562500000 : ℝ)| +
          |(18756092534788904164500610557762072271 /
            84053930415306240320205688476562500000 : ℝ) -
            (22314355131420975577 / 100000000000000000000 : ℝ)| := by
      exact _root_.abs_sub_le _ _ _
    _ ≤ (1 / 58207660913467407226562500 : ℝ) +
          (1 / 10 ^ 20 - 1 / 58207660913467407226562500 : ℝ) := by
      apply add_le_add z
      norm_num
    _ = (1 / 5 : ℝ) ^ 37 / (1 - 1 / 5) +
        (1 / 10 ^ 20 - (1 / 5 : ℝ) ^ 37 / (1 - 1 / 5)) := by
      norm_num

private theorem log_ten_eq : log (10 : ℝ) = 3 * log 2 + log (5 / 4 : ℝ) := by
  rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num]
  rw [log_mul]
  · rw [log_pow]
    norm_num
  · positivity
  · norm_num

private theorem log_ten_near_20 :
    |L - (230258509299404568403 / 100000000000000000000 : ℝ)| ≤
      4 / 10 ^ 20 := by
  have h2 := log_two_near_20
  have h54 := log_five_four_near_20
  dsimp [L]
  rw [log_ten_eq]
  calc
    |3 * log 2 + log (5 / 4) -
        (230258509299404568403 / 100000000000000000000 : ℝ)| =
        |3 * (log 2 - (69314718055994530942 / 100000000000000000000 : ℝ)) +
          (log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ))| := by
      ring_nf
    _ ≤ |3 * (log 2 - (69314718055994530942 / 100000000000000000000 : ℝ))| +
          |log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ)| := by
      exact abs_add_le _ _
    _ = 3 * |log 2 - (69314718055994530942 / 100000000000000000000 : ℝ)| +
          |log (5 / 4) - (22314355131420975577 / 100000000000000000000 : ℝ)| := by
      rw [abs_mul]
      norm_num
    _ ≤ 3 * (1 / 10 ^ 20 : ℝ) + 1 / 10 ^ 20 := by
      exact add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num)) h54
    _ = 4 / 10 ^ 20 := by
      norm_num

private theorem log_ten_bounds :
    (230258509299404568399 / 100000000000000000000 : ℝ) ≤ L ∧
      L ≤ (230258509299404568407 / 100000000000000000000 : ℝ) := by
  have h := (abs_sub_le_iff.mp log_ten_near_20)
  constructor <;> linarith

private theorem main_derivative_bounds :
    (M : ℝ) + 2 / 5 < 10 ^ 11 * L ^ 4 ∧
      10 ^ 11 * L ^ 4 < (M : ℝ) + 1 / 2 := by
  rcases log_ten_bounds with ⟨hlo, hhi⟩
  have hlo_pos : 0 ≤ (230258509299404568399 / 100000000000000000000 : ℝ) := by norm_num
  have hpow_lo :
      (230258509299404568399 / 100000000000000000000 : ℝ) ^ 4 ≤ L ^ 4 :=
    pow_le_pow_left₀ hlo_pos hlo 4
  have hpow_hi :
      L ^ 4 ≤ (230258509299404568407 / 100000000000000000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (by linarith : 0 ≤ L) hhi 4
  constructor
  · exact lt_of_lt_of_le (by norm_num) (mul_le_mul_of_nonneg_left hpow_lo (by norm_num))
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow_hi (by norm_num)) (by norm_num)

private theorem exp_remainder_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ exp x - 1 - x ∧ exp x - 1 - x ≤ x ^ 2 := by
  constructor
  · nlinarith [Real.add_one_le_exp x]
  · have hnonneg : 0 ≤ exp x - 1 - x := by nlinarith [Real.add_one_le_exp x]
    have habs := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rwa [abs_of_nonneg hnonneg] at habs

private theorem t_eq_inv : t = ((10 : ℝ) ^ N)⁻¹ := by
  dsimp [t]
  rw [Real.rpow_neg (by norm_num : 0 ≤ (10 : ℝ)) (N : ℝ)]
  rw [Real.rpow_natCast]

private theorem t_pos : 0 < t := by
  dsimp [t]
  positivity

private theorem t_le_pow100_inv : t ≤ (1 / 10 ^ 100 : ℝ) := by
  rw [t_eq_inv]
  have hN : 100 ≤ N := by norm_num [N]
  have hpow : (10 : ℝ) ^ 100 ≤ (10 : ℝ) ^ N := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 10) hN
  have hpos : 0 < (10 : ℝ) ^ 100 := by positivity
  have := inv_anti₀ hpos hpow
  simpa [one_div] using this

private theorem t_le_pow20_inv : t ≤ (1 / 10 ^ 20 : ℝ) := by
  exact t_le_pow100_inv.trans (by norm_num)

private theorem log_increment_bounds :
    (M : ℝ) * t ≤ L * (c - (N : ℝ)) ∧
      L * (c - (N : ℝ)) + (L * (c - (N : ℝ))) ^ 2 < ((M : ℝ) + 1) * t := by
  let r1 : ℝ := exp (L * t) - 1 - L * t
  let r2 : ℝ := exp (L * (u - 1)) - 1 - L * (u - 1)
  let r3 : ℝ := exp (L * (v - 10)) - 1 - L * (v - 10)
  let x : ℝ := L * (c - (N : ℝ))
  have ht0 : 0 ≤ t := t_pos.le
  rcases log_ten_bounds with ⟨hLlo, hLhi⟩
  have hL0 : 0 ≤ L := by
    nlinarith
  have hL3 : L ≤ 3 := by
    nlinarith
  have hL2 : L ^ 2 ≤ 9 := by
    have := pow_le_pow_left₀ hL0 hL3 2
    norm_num at this
    exact this
  have hL3pow : L ^ 3 ≤ 27 := by
    have := pow_le_pow_left₀ hL0 hL3 3
    norm_num at this
    exact this
  have hL4_nonneg : 0 ≤ L ^ 4 := pow_nonneg hL0 4
  have ht_le1 : t ≤ 1 := t_le_pow20_inv.trans (by norm_num)
  have ht2_le_t : t ^ 2 ≤ t := by
    nlinarith [mul_le_mul_of_nonneg_left ht_le1 ht0]
  have hx1_nonneg : 0 ≤ L * t := mul_nonneg hL0 ht0
  have hx1_le_one : L * t ≤ 1 := by
    have hLt : L * t ≤ 3 * t := mul_le_mul_of_nonneg_right hL3 ht0
    nlinarith [hLt, t_le_pow20_inv]
  have hr1_bounds := exp_remainder_bounds hx1_nonneg hx1_le_one
  have hr1_nonneg : 0 ≤ r1 := by
    simpa [r1] using hr1_bounds.1
  have hr1_le_sq : r1 ≤ (L * t) ^ 2 := by
    simpa [r1] using hr1_bounds.2
  have hr1_le : r1 ≤ 9 * t ^ 2 := by
    calc
      r1 ≤ (L * t) ^ 2 := hr1_le_sq
      _ = L ^ 2 * t ^ 2 := by ring
      _ ≤ 9 * t ^ 2 := mul_le_mul_of_nonneg_right hL2 (sq_nonneg t)
  have hu_eq : u = 1 + L * t + r1 := by
    dsimp [u, L, r1]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (10 : ℝ))]
    ring
  have hu_sub_eq : u - 1 = L * t + r1 := by
    rw [hu_eq]
    ring
  have hr1_le_t : r1 ≤ t := by
    have : 9 * t ^ 2 ≤ t := by nlinarith [t_le_pow20_inv, ht0]
    exact hr1_le.trans this
  have hu_sub_nonneg : 0 ≤ u - 1 := by
    rw [hu_sub_eq]
    nlinarith [hx1_nonneg, hr1_nonneg]
  have hu_sub_le : u - 1 ≤ 4 * t := by
    rw [hu_sub_eq]
    have hLt : L * t ≤ 3 * t := mul_le_mul_of_nonneg_right hL3 ht0
    nlinarith [hLt, hr1_le_t]
  have hx2_nonneg : 0 ≤ L * (u - 1) := mul_nonneg hL0 hu_sub_nonneg
  have hx2_le : L * (u - 1) ≤ 12 * t := by
    have := mul_le_mul hL3 hu_sub_le hu_sub_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hx2_le_one : L * (u - 1) ≤ 1 := by
    nlinarith [hx2_le, t_le_pow20_inv]
  have hr2_bounds := exp_remainder_bounds hx2_nonneg hx2_le_one
  have hr2_nonneg : 0 ≤ r2 := by
    simpa [r2] using hr2_bounds.1
  have hr2_le_sq : r2 ≤ (L * (u - 1)) ^ 2 := by
    simpa [r2] using hr2_bounds.2
  have hr2_le : r2 ≤ 144 * t ^ 2 := by
    have hx2sq :=
      mul_le_mul hx2_le hx2_le hx2_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) ht0)
    calc
      r2 ≤ (L * (u - 1)) ^ 2 := hr2_le_sq
      _ ≤ (12 * t) ^ 2 := by simpa [pow_two] using hx2sq
      _ = 144 * t ^ 2 := by ring
  have hv_eq : v = 10 * (1 + L * (u - 1) + r2) := by
    dsimp [v, L, r2]
    rw [show u = 1 + (u - 1) by ring]
    rw [Real.rpow_add (by norm_num : 0 < (10 : ℝ)) 1 (u - 1)]
    rw [Real.rpow_one]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (10 : ℝ)) (u - 1)]
    ring_nf
  have hv_sub_eq : v - 10 = 10 * (L * (u - 1) + r2) := by
    rw [hv_eq]
    ring
  have hr2_le_8t : r2 ≤ 8 * t := by
    have : 144 * t ^ 2 ≤ 8 * t := by nlinarith [t_le_pow20_inv, ht0]
    exact hr2_le.trans this
  have hv_sub_nonneg : 0 ≤ v - 10 := by
    rw [hv_sub_eq]
    nlinarith [hx2_nonneg, hr2_nonneg]
  have hv_sub_le : v - 10 ≤ 200 * t := by
    rw [hv_sub_eq]
    nlinarith [hx2_le, hr2_le_8t]
  have hx3_nonneg : 0 ≤ L * (v - 10) := mul_nonneg hL0 hv_sub_nonneg
  have hx3_le : L * (v - 10) ≤ 600 * t := by
    have := mul_le_mul hL3 hv_sub_le hv_sub_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hx3_le_one : L * (v - 10) ≤ 1 := by
    nlinarith [hx3_le, t_le_pow20_inv]
  have hr3_bounds := exp_remainder_bounds hx3_nonneg hx3_le_one
  have hr3_nonneg : 0 ≤ r3 := by
    simpa [r3] using hr3_bounds.1
  have hr3_le_sq : r3 ≤ (L * (v - 10)) ^ 2 := by
    simpa [r3] using hr3_bounds.2
  have hr3_le : r3 ≤ 360000 * t ^ 2 := by
    have hx3sq :=
      mul_le_mul hx3_le hx3_le hx3_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 600) ht0)
    calc
      r3 ≤ (L * (v - 10)) ^ 2 := hr3_le_sq
      _ ≤ (600 * t) ^ 2 := by simpa [pow_two] using hx3sq
      _ = 360000 * t ^ 2 := by ring
  have hc_eq : c = (N : ℝ) * (1 + L * (v - 10) + r3) := by
    dsimp [c, L, r3]
    rw [show v = 10 + (v - 10) by ring]
    rw [Real.rpow_add (by norm_num : 0 < (10 : ℝ)) 10 (v - 10)]
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (10 : ℝ)) (v - 10)]
    norm_num [N]
  have hx_eq :
      x = (10 ^ 11 : ℝ) * L ^ 4 * t + (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
        (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 := by
    dsimp [x]
    rw [hc_eq, hv_eq, hu_eq]
    norm_num [N]
    ring_nf
  have hx_nonneg : 0 ≤ x := by
    rw [hx_eq]
    positivity
  have hmain_nonneg : 0 ≤ (10 ^ 11 : ℝ) * L ^ 4 * t := by positivity
  have hterm1_nonneg : 0 ≤ (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 := by positivity
  have hterm2_nonneg : 0 ≤ (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 := by positivity
  have hterm3_nonneg : 0 ≤ (N : ℝ) * L * r3 := by positivity
  have hterm1_le : (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 ≤ 10 ^ 16 * t ^ 2 := by
    have hmul : L ^ 3 * r1 ≤ 27 * (9 * t ^ 2) :=
      mul_le_mul hL3pow hr1_le hr1_nonneg (by norm_num : (0 : ℝ) ≤ 27)
    calc
      (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 = ((10 : ℝ) * (N : ℝ)) * (L ^ 3 * r1) := by ring
      _ ≤ ((10 : ℝ) * (N : ℝ)) * (27 * (9 * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (24300000000000 : ℝ) * t ^ 2 := by
          norm_num [N]
          ring
      _ ≤ 10 ^ 16 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num : (24300000000000 : ℝ) ≤ 10 ^ 16)
            (sq_nonneg t)
  have hterm2_le : (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 ≤ 10 ^ 16 * t ^ 2 := by
    have hmul : L ^ 2 * r2 ≤ 9 * (144 * t ^ 2) :=
      mul_le_mul hL2 hr2_le hr2_nonneg (by norm_num : (0 : ℝ) ≤ 9)
    calc
      (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 = ((10 : ℝ) * (N : ℝ)) * (L ^ 2 * r2) := by ring
      _ ≤ ((10 : ℝ) * (N : ℝ)) * (9 * (144 * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (129600000000000 : ℝ) * t ^ 2 := by
          norm_num [N]
          ring
      _ ≤ 10 ^ 16 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num : (129600000000000 : ℝ) ≤ 10 ^ 16)
            (sq_nonneg t)
  have hterm3_le : (N : ℝ) * L * r3 ≤ 2 * 10 ^ 16 * t ^ 2 := by
    have hmul : L * r3 ≤ 3 * (360000 * t ^ 2) :=
      mul_le_mul hL3 hr3_le hr3_nonneg (by norm_num : (0 : ℝ) ≤ 3)
    calc
      (N : ℝ) * L * r3 = (N : ℝ) * (L * r3) := by ring
      _ ≤ (N : ℝ) * (3 * (360000 * t ^ 2)) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = (10800000000000000 : ℝ) * t ^ 2 := by
          norm_num [N]
          ring
      _ ≤ 2 * 10 ^ 16 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (by norm_num : (10800000000000000 : ℝ) ≤ 2 * 10 ^ 16)
            (sq_nonneg t)
  have herror_le :
      (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
        (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 ≤
          (1 / 1000 : ℝ) * t := by
    have ht2small : 4 * 10 ^ 16 * t ^ 2 ≤ (1 / 1000 : ℝ) * t := by
      have ht2 : t ^ 2 ≤ (1 / 10 ^ 20 : ℝ) * t := by
        calc
          t ^ 2 = t * t := by ring
          _ ≤ (1 / 10 ^ 20 : ℝ) * t := mul_le_mul_of_nonneg_right t_le_pow20_inv ht0
      calc
        4 * 10 ^ 16 * t ^ 2 ≤ 4 * 10 ^ 16 * ((1 / 10 ^ 20 : ℝ) * t) :=
          mul_le_mul_of_nonneg_left ht2 (by norm_num)
        _ = ((4 * 10 ^ 16 : ℝ) * (1 / 10 ^ 20)) * t := by ring
        _ ≤ (1 / 1000 : ℝ) * t :=
          mul_le_mul_of_nonneg_right (by norm_num : (4 * 10 ^ 16 : ℝ) * (1 / 10 ^ 20) ≤ 1 / 1000) ht0
    calc
      (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
          (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 ≤
          10 ^ 16 * t ^ 2 + 10 ^ 16 * t ^ 2 + 2 * 10 ^ 16 * t ^ 2 :=
        add_le_add (add_le_add hterm1_le hterm2_le) hterm3_le
      _ = 4 * 10 ^ 16 * t ^ 2 := by ring
      _ ≤ (1 / 1000 : ℝ) * t := ht2small
  have hmain_lower : (M : ℝ) * t ≤ (10 ^ 11 : ℝ) * L ^ 4 * t := by
    have hder := main_derivative_bounds.1.le
    have hM : (M : ℝ) ≤ (M : ℝ) + 2 / 5 := by norm_num [M]
    exact mul_le_mul_of_nonneg_right (hM.trans hder) ht0
  have hmain_upper :
      (10 ^ 11 : ℝ) * L ^ 4 * t ≤ ((M : ℝ) + 1 / 2) * t := by
    exact mul_le_mul_of_nonneg_right main_derivative_bounds.2.le ht0
  have hx_lower : (M : ℝ) * t ≤ x := by
    rw [hx_eq]
    have herror_nonneg :
        0 ≤ (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
          (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 :=
      add_nonneg (add_nonneg hterm1_nonneg hterm2_nonneg) hterm3_nonneg
    calc
      (M : ℝ) * t ≤ (10 ^ 11 : ℝ) * L ^ 4 * t := hmain_lower
      _ ≤ (10 ^ 11 : ℝ) * L ^ 4 * t +
          ((10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
            (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3) :=
        le_add_of_nonneg_right herror_nonneg
      _ = (10 ^ 11 : ℝ) * L ^ 4 * t + (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
          (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 := by ring
  have hx_upper : x ≤ ((M : ℝ) + 501 / 1000) * t := by
    rw [hx_eq]
    calc
      (10 ^ 11 : ℝ) * L ^ 4 * t + (10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
          (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3 =
          (10 ^ 11 : ℝ) * L ^ 4 * t +
            ((10 : ℝ) * (N : ℝ) * L ^ 3 * r1 +
              (10 : ℝ) * (N : ℝ) * L ^ 2 * r2 + (N : ℝ) * L * r3) := by ring
      _ ≤ ((M : ℝ) + 1 / 2) * t + (1 / 1000 : ℝ) * t :=
        add_le_add hmain_upper herror_le
      _ = ((M : ℝ) + 501 / 1000) * t := by ring
  have hx_le_big : x ≤ (3000000000000 : ℝ) * t := by
    calc
      x ≤ ((M : ℝ) + 501 / 1000) * t := hx_upper
      _ ≤ (3000000000000 : ℝ) * t :=
        mul_le_mul_of_nonneg_right
          (by norm_num [M] : (M : ℝ) + 501 / 1000 ≤ (3000000000000 : ℝ)) ht0
  have hx_sq_le : x ^ 2 ≤ (1 / 1000 : ℝ) * t := by
    have hxt_nonneg : 0 ≤ (3000000000000 : ℝ) * t := by positivity
    have hsq := mul_le_mul hx_le_big hx_le_big hx_nonneg hxt_nonneg
    have ht2tiny : (3000000000000 : ℝ) ^ 2 * t ^ 2 ≤ (1 / 1000 : ℝ) * t := by
      have ht2 : t ^ 2 ≤ (1 / 10 ^ 100 : ℝ) * t := by
        calc
          t ^ 2 = t * t := by ring
          _ ≤ (1 / 10 ^ 100 : ℝ) * t := mul_le_mul_of_nonneg_right t_le_pow100_inv ht0
      calc
        (3000000000000 : ℝ) ^ 2 * t ^ 2 ≤
            (3000000000000 : ℝ) ^ 2 * ((1 / 10 ^ 100 : ℝ) * t) :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = (((3000000000000 : ℝ) ^ 2) * (1 / 10 ^ 100)) * t := by ring
        _ ≤ (1 / 1000 : ℝ) * t :=
          mul_le_mul_of_nonneg_right
            (by norm_num : ((3000000000000 : ℝ) ^ 2) * (1 / 10 ^ 100) ≤ 1 / 1000) ht0
    calc
      x ^ 2 = x * x := by ring
      _ ≤ (3000000000000 * t) * (3000000000000 * t) := by
        simpa [pow_two] using hsq
      _ = (3000000000000 : ℝ) ^ 2 * t ^ 2 := by ring
      _ ≤ (1 / 1000 : ℝ) * t := ht2tiny
  constructor
  · simpa [x] using hx_lower
  · have : x + x ^ 2 < ((M : ℝ) + 1) * t := by
      calc
        x + x ^ 2 ≤ ((M : ℝ) + 501 / 1000) * t + (1 / 1000 : ℝ) * t :=
          add_le_add hx_upper hx_sq_le
        _ = ((M : ℝ) + 502 / 1000) * t := by ring
        _ < ((M : ℝ) + 1) * t :=
          mul_lt_mul_of_pos_right (by norm_num [M] : (M : ℝ) + 502 / 1000 < (M : ℝ) + 1) t_pos
    simpa [x] using this

private theorem powN_mul_t : (10 : ℝ) ^ N * t = 1 := by
  rw [t_eq_inv]
  exact mul_inv_cancel₀ (pow_ne_zero N (by norm_num : (10 : ℝ) ≠ 0))

private theorem tinyExponentTower_eq_base_mul_exp :
    tinyExponentTower = (10 : ℝ) ^ N * exp (L * (c - (N : ℝ))) := by
  dsimp [tinyExponentTower, L]
  rw [show c = (N : ℝ) + (c - (N : ℝ)) by ring]
  rw [Real.rpow_add (by norm_num : 0 < (10 : ℝ)) (N : ℝ) (c - (N : ℝ))]
  rw [Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by norm_num : 0 < (10 : ℝ)) (c - (N : ℝ))]
  ring_nf

private theorem floor_tinyExponentTower :
    ⌊tinyExponentTower⌋ = (10 : Int) ^ N + M := by
  let A : ℝ := (10 : ℝ) ^ N
  let x : ℝ := L * (c - (N : ℝ))
  have htower : tinyExponentTower = A * exp x := by
    dsimp [A, x]
    exact tinyExponentTower_eq_base_mul_exp
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hAt : A * t = 1 := by
    dsimp [A]
    exact powN_mul_t
  have hcastA : (((10 : Int) ^ N : Int) : ℝ) = A := by
    dsimp [A]
    rw [Int.cast_pow]
    norm_num
  have hAMt : A * ((M : ℝ) * t) = (M : ℝ) := by
    calc
      A * ((M : ℝ) * t) = (M : ℝ) * (A * t) := by ring
      _ = (M : ℝ) := by rw [hAt, mul_one]
  have hAM1t : A * (((M : ℝ) + 1) * t) = (M : ℝ) + 1 := by
    calc
      A * (((M : ℝ) + 1) * t) = ((M : ℝ) + 1) * (A * t) := by ring
      _ = (M : ℝ) + 1 := by rw [hAt, mul_one]
  have hx_lower : (M : ℝ) * t ≤ x := by
    simpa [x] using log_increment_bounds.1
  have hx_plus_sq_upper : x + x ^ 2 < ((M : ℝ) + 1) * t := by
    simpa [x] using log_increment_bounds.2
  have hx_nonneg : 0 ≤ x := by
    have hMt_nonneg : 0 ≤ (M : ℝ) * t := mul_nonneg (by norm_num [M]) t_pos.le
    exact hMt_nonneg.trans hx_lower
  have hx_upper : x ≤ ((M : ℝ) + 1) * t := by
    calc
      x ≤ x + x ^ 2 := le_add_of_nonneg_right (sq_nonneg x)
      _ ≤ ((M : ℝ) + 1) * t := le_of_lt hx_plus_sq_upper
  have hx_le_one : x ≤ 1 := by
    calc
      x ≤ ((M : ℝ) + 1) * t := hx_upper
      _ ≤ ((M : ℝ) + 1) * (1 / 10 ^ 20 : ℝ) :=
        mul_le_mul_of_nonneg_left t_le_pow20_inv (by norm_num [M])
      _ ≤ 1 := by norm_num [M]
  have hexp_rem_le : exp x - 1 - x ≤ x ^ 2 :=
    (exp_remainder_bounds hx_nonneg hx_le_one).2
  have hexp_lower : 1 + (M : ℝ) * t ≤ exp x := by
    calc
      1 + (M : ℝ) * t = (M : ℝ) * t + 1 := by ring
      _ ≤ x + 1 := add_le_add_left hx_lower 1
      _ ≤ exp x := Real.add_one_le_exp x
  have hexp_upper : exp x < 1 + ((M : ℝ) + 1) * t := by
    have hbound : exp x ≤ 1 + x + x ^ 2 := by linarith
    calc
      exp x ≤ 1 + x + x ^ 2 := hbound
      _ = 1 + (x + x ^ 2) := by ring
      _ < 1 + ((M : ℝ) + 1) * t := by
        simpa [add_comm, add_left_comm, add_assoc] using add_lt_add_right hx_plus_sq_upper 1
  have hlower : (((10 : Int) ^ N + M : Int) : ℝ) ≤ tinyExponentTower := by
    rw [htower]
    calc
      (((10 : Int) ^ N + M : Int) : ℝ) = A + (M : ℝ) := by
        rw [Int.cast_add, hcastA]
      _ = A * (1 + (M : ℝ) * t) := by
        rw [mul_add, mul_one, hAMt]
      _ ≤ A * exp x := mul_le_mul_of_nonneg_left hexp_lower hA_pos.le
  have hupper : tinyExponentTower < (((10 : Int) ^ N + M : Int) : ℝ) + 1 := by
    rw [htower]
    calc
      A * exp x < A * (1 + ((M : ℝ) + 1) * t) :=
        mul_lt_mul_of_pos_left hexp_upper hA_pos
      _ = A + ((M : ℝ) + 1) := by
        rw [mul_add, mul_one, hAM1t]
      _ = (((10 : Int) ^ N + M : Int) : ℝ) + 1 := by
        rw [Int.cast_add, hcastA]
        ring
  exact Int.floor_eq_iff.2 ⟨hlower, hupper⟩

/--
The floor identity

```text
floor(10^(10^(10^(10^(10^(-10^10)))))) - 10^(10^10) = 2811012357389.
```
-/
theorem floor_tinyExponentTower_sub :
    ⌊tinyExponentTower⌋ - (10 : Int) ^ (10 ^ 10 : Nat) = (2811012357389 : Int) := by
  change ⌊tinyExponentTower⌋ - (10 : Int) ^ N = M
  rw [floor_tinyExponentTower]
  ring

/-- The same identity with the full tower expanded in the theorem statement. -/
theorem floor_expanded_tinyExponentTower_sub :
    Int.floor
      ((10 : ℝ) ^
        ((10 : ℝ) ^
          ((10 : ℝ) ^
            ((10 : ℝ) ^
              ((10 : ℝ) ^ (-((10 ^ 10 : Nat) : ℝ))))))) -
      (10 : Int) ^ (10 ^ 10 : Nat) = (2811012357389 : Int) := by
  change ⌊tinyExponentTower⌋ - (10 : Int) ^ (10 ^ 10 : Nat) = (2811012357389 : Int)
  exact floor_tinyExponentTower_sub

end

end LeanProofs
