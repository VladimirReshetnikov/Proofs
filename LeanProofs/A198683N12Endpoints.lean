import LeanProofs.A198683N12Certificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Endpoint estimates for the `A198683(12)` near-`1` split

This module discharges, one by one, the scalar endpoint estimates collected in
`LeanProofs.A198683N12Certificate.NearOneEndpointBounds`.  Each field is a
rational bound on `Real.sin`, `Real.cos`, or `Real.exp` at an explicit
argument (a pure rational, a `π/2`-scaled rational, or a product of such
factors), and each is proved by the same three-layer strategy:

1. **Argument boxing.** Arguments containing `π` are boxed with the certified
   rational `π/2` interval `A198683N12Symbolic.pi_div_two_bounds_for_theta_rho`
   (itself derived from mathlib's 20-decimal `π` certificate), after quadrant
   reduction with the exact shift identities (`sin (x + π) = -sin x`,
   `cos (π/2 - x) = sin x`, ...) so that every remaining trigonometric
   evaluation happens at an argument in `[0, 1]`.
2. **Monotone transport.** `Real.sin` is strictly monotone on
   `[-π/2, π/2]` and `Real.cos` strictly antitone on `[0, π]`, so each boxed
   argument is replaced by a rational endpoint.
3. **Taylor partial sums.** At the rational endpoints, `sin`/`cos` are boxed
   by alternating-series partial sums (via `Real.hasSum_sin`/`Real.hasSum_cos`
   and mathlib's `Antitone.alternating_series_le_tendsto` /
   `Antitone.tendsto_le_alternating_series`), and `exp` by
   `Real.sum_le_exp_of_nonneg` (below) and `Real.exp_bound'` plus the
   20-decimal `exp 1` certificate (above), with all resulting rational
   inequalities discharged by `norm_num`.

## Outcome: all fields proved; the near-`1` split is unconditional

Every field of `NearOneEndpointBounds` is proved below as a standalone
theorem named `endpoint_<field>`; the bundle is assembled in
`nearOneEndpointBounds`, and `nearOneSplit` discharges
`A198683N12Certificate.NearOneSplit` through the symbolic interval ladder.

## Historical note: the original `hexp0`/`hcos1` constants were false

The first version of the certificate carried two endpoint-selection errors
(both found by exact rational interval arithmetic while proving this module,
and both refuted *in Lean* below):

* the original `hexp0` claimed `3724 < exp (π/2 * 5.2346)`, but
  `exp (π/2 * 5.2346) = 3723.7647... < 3724`; see `uncorrected_hexp0_is_false`.
* the original `hcos1` claimed `cos (π/2 * 1.1317) < -411/2000 = -0.2055`,
  but `cos (π/2 * 1.1317) = -0.2054014... > -0.2055`; see
  `uncorrected_hcos1_is_false`.

In both cases the constant had been evaluated at the *true* (mid-box)
level-2 value (`≈ 5.23468`, `≈ 1.13179`) instead of at the box endpoint
actually named in the statement (`5.2346`, `1.1317`).  The repair widens the
level-3 window of the `A198683N12Symbolic` ladder from `(-766, -765)` to
`(-766, -764)` — still inside the negative half-period of `sin (π/2 · x)`
since `-766 ≡ 2` and `-764 ≡ 0 (mod 4)` — which admits the corrected
endpoint bounds `3723 < exp (π/2 · 5.2346)` and
`cos (π/2 · 1.1317) < -1027/5000`.
-/

namespace LeanProofs

namespace A198683N12Endpoints

open Finset

set_option maxHeartbeats 4000000

/-! ## The `π/2` box -/

private theorem pi_half_gt :
    (1570796326794 : ℝ) / 1000000000000 < Real.pi / 2 :=
  A198683N12Symbolic.pi_div_two_bounds_for_theta_rho.1

private theorem pi_half_lt :
    Real.pi / 2 < (1570796326795 : ℝ) / 1000000000000 :=
  A198683N12Symbolic.pi_div_two_bounds_for_theta_rho.2

/-! ## The 20-decimal `exp 1` certificate, upper side -/

private theorem exp_one_upper_cert :
    Real.exp 1 ≤ (363916618873 : ℝ) / 133877442384 + 1 / 10 ^ 20 := by
  have h := (abs_sub_le_iff.1 Real.exp_one_near_20).1
  linarith

private theorem exp_one_le_d10 :
    Real.exp 1 ≤ (27182818285 : ℝ) / 10000000000 :=
  exp_one_upper_cert.trans (by norm_num)

/-! ## Alternating Taylor partial sums for `sin` and `cos` on `[0, 1]` -/

private theorem sin_terms_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : x ^ (2 * (n + 1) + 1) ≤ x ^ (2 * n + 1) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : (Nat.factorial (2 * n + 1) : ℝ) ≤ (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hd1 : (0 : ℝ) < (Nat.factorial (2 * n + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hd2 : (0 : ℝ) < (Nat.factorial (2 * (n + 1) + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [div_le_div_iff₀ hd2 hd1]
  exact mul_le_mul hp hf hd1.le (pow_nonneg h0 _)

private theorem cos_terms_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : x ^ (2 * (n + 1)) ≤ x ^ (2 * n) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hf : (Nat.factorial (2 * n) : ℝ) ≤ (Nat.factorial (2 * (n + 1)) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hd1 : (0 : ℝ) < (Nat.factorial (2 * n) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hd2 : (0 : ℝ) < (Nat.factorial (2 * (n + 1)) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [div_le_div_iff₀ hd2 hd1]
  exact mul_le_mul hp hf hd1.le (pow_nonneg h0 _)

private theorem sin_tendsto (x : ℝ) :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      Filter.atTop (nhds (Real.sin x)) := by
  have h := (Real.hasSum_sin x).tendsto_sum_nat
  simpa only [mul_div_assoc] using h

private theorem cos_tendsto (x : ℝ) :
    Filter.Tendsto
      (fun n => ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      Filter.atTop (nhds (Real.cos x)) := by
  have h := (Real.hasSum_cos x).tendsto_sum_nat
  simpa only [mul_div_assoc] using h

/-- Even partial sums of the `sin` Taylor series are lower bounds on `[0, 1]`. -/
private theorem sin_partial_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k),
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)) ≤
      Real.sin x :=
  Antitone.alternating_series_le_tendsto (sin_tendsto x) (sin_terms_antitone h0 h1) k

/-- Odd partial sums of the `sin` Taylor series are upper bounds on `[0, 1]`. -/
private theorem le_sin_partial {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    Real.sin x ≤
      ∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)) :=
  Antitone.tendsto_le_alternating_series (sin_tendsto x) (sin_terms_antitone h0 h1) k

/-- Even partial sums of the `cos` Taylor series are lower bounds on `[0, 1]`. -/
private theorem cos_partial_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (2 * k),
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)) ≤
      Real.cos x :=
  Antitone.alternating_series_le_tendsto (cos_tendsto x) (cos_terms_antitone h0 h1) k

/-- Odd partial sums of the `cos` Taylor series are upper bounds on `[0, 1]`. -/
private theorem le_cos_partial {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    Real.cos x ≤
      ∑ i ∈ Finset.range (2 * k + 1),
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)) :=
  Antitone.tendsto_le_alternating_series (cos_tendsto x) (cos_terms_antitone h0 h1) k

/-- Reduce a strict lower bound on `sin A` to a `norm_num`-checkable partial sum. -/
private theorem lt_sin_taylor {A q : ℝ} (h0 : 0 ≤ A) (h1 : A ≤ 1) (k : ℕ)
    (h : q < ∑ i ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ i * (A ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ))) :
    q < Real.sin A :=
  h.trans_le (sin_partial_le h0 h1 k)

/-- Reduce a strict upper bound on `sin A` to a `norm_num`-checkable partial sum. -/
private theorem sin_taylor_lt {A q : ℝ} (h0 : 0 ≤ A) (h1 : A ≤ 1) (k : ℕ)
    (h : (∑ i ∈ Finset.range (2 * k + 1),
      (-1 : ℝ) ^ i * (A ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ))) < q) :
    Real.sin A < q :=
  (le_sin_partial h0 h1 k).trans_lt h

/-- Reduce a strict lower bound on `cos A` to a `norm_num`-checkable partial sum. -/
private theorem lt_cos_taylor {A q : ℝ} (h0 : 0 ≤ A) (h1 : A ≤ 1) (k : ℕ)
    (h : q < ∑ i ∈ Finset.range (2 * k),
      (-1 : ℝ) ^ i * (A ^ (2 * i) / (Nat.factorial (2 * i) : ℝ))) :
    q < Real.cos A :=
  h.trans_le (cos_partial_le h0 h1 k)

/-- Reduce a strict upper bound on `cos A` to a `norm_num`-checkable partial sum. -/
private theorem cos_taylor_lt {A q : ℝ} (h0 : 0 ≤ A) (h1 : A ≤ 1) (k : ℕ)
    (h : (∑ i ∈ Finset.range (2 * k + 1),
      (-1 : ℝ) ^ i * (A ^ (2 * i) / (Nat.factorial (2 * i) : ℝ))) < q) :
    Real.cos A < q :=
  (le_cos_partial h0 h1 k).trans_lt h

/-! ## Taylor bounds for `exp` at rational arguments -/

/-- Reduce a strict lower bound on `exp A` (any `A ≥ 0`) to a partial sum. -/
private theorem exp_lower_rat {A r : ℝ} (h0 : 0 ≤ A) (n : ℕ)
    (h : r < ∑ m ∈ Finset.range n, A ^ m / (Nat.factorial m : ℝ)) :
    r < Real.exp A :=
  h.trans_le (Real.sum_le_exp_of_nonneg h0 n)

/-- The `n = 14` Taylor upper bound for `exp` on `[0, 1]`. -/
private theorem exp_upper_taylor {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y ≤ (∑ m ∈ Finset.range 14, y ^ m / (Nat.factorial m : ℝ)) +
      y ^ 14 * ((14 : ℝ) + 1) / ((Nat.factorial 14 : ℝ) * (14 : ℝ)) := by
  simpa using Real.exp_bound' h0 h1 (n := 14) (by norm_num)

/-- Reduce a strict upper bound on `exp A` for `A ∈ [0, 1]` to a partial sum. -/
private theorem exp_upper_rat {y r : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1)
    (h : (∑ m ∈ Finset.range 14, y ^ m / (Nat.factorial m : ℝ)) +
      y ^ 14 * ((14 : ℝ) + 1) / ((Nat.factorial 14 : ℝ) * (14 : ℝ)) < r) :
    Real.exp y < r :=
  (exp_upper_taylor h0 h1).trans_lt h

/-! ## Monotone transport across the `π/2` box

Each lemma replaces a `π/2`-scaled argument by a nearby rational endpoint,
using strict monotonicity of `sin` on `[-π/2, π/2]`, strict antitonicity of
`cos` on `[0, π]`, or strict monotonicity of `exp`. -/

private theorem lt_sin_pi_half_mul {c A q : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hA0 : 0 ≤ A) (hA : A ≤ (1570796326794 : ℝ) / 1000000000000 * c)
    (hq : q < Real.sin A) : q < Real.sin (Real.pi / 2 * c) := by
  have hkey := mul_lt_mul_of_pos_right pi_half_gt hc
  have hpos : (0 : ℝ) < Real.pi / 2 := lt_trans (by norm_num) pi_half_gt
  have h1 : A < Real.pi / 2 * c := by linarith
  have h2 : Real.pi / 2 * c ≤ Real.pi / 2 := by
    have := mul_le_of_le_one_right hpos.le hc1
    linarith
  have h3 : -(Real.pi / 2) ≤ A := by linarith
  exact hq.trans (Real.sin_lt_sin_of_lt_of_le_pi_div_two h3 h2 h1)

private theorem sin_pi_half_mul_lt {c A q : ℝ} (hc : 0 < c) (hA1 : A ≤ 1)
    (hA : (1570796326795 : ℝ) / 1000000000000 * c ≤ A)
    (hq : Real.sin A < q) : Real.sin (Real.pi / 2 * c) < q := by
  have hkey := mul_lt_mul_of_pos_right pi_half_lt hc
  have hpos : (0 : ℝ) < Real.pi / 2 := lt_trans (by norm_num) pi_half_gt
  have h1 : Real.pi / 2 * c < A := by linarith
  have h2 : A ≤ Real.pi / 2 := by linarith [pi_half_gt]
  have h3 : -(Real.pi / 2) ≤ Real.pi / 2 * c := by
    have := mul_nonneg hpos.le hc.le
    linarith
  exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two h3 h2 h1).trans hq

private theorem lt_cos_pi_half_mul {c A q : ℝ} (hc : 0 < c) (hA1 : A ≤ 1)
    (hA : (1570796326795 : ℝ) / 1000000000000 * c ≤ A)
    (hq : q < Real.cos A) : q < Real.cos (Real.pi / 2 * c) := by
  have hkey := mul_lt_mul_of_pos_right pi_half_lt hc
  have hpos : (0 : ℝ) < Real.pi / 2 := lt_trans (by norm_num) pi_half_gt
  have h1 : Real.pi / 2 * c < A := by linarith
  have h0 : 0 ≤ Real.pi / 2 * c := mul_nonneg hpos.le hc.le
  have h2 : A ≤ Real.pi := by linarith [pi_half_gt]
  exact hq.trans (Real.cos_lt_cos_of_nonneg_of_le_pi h0 h2 h1)

private theorem cos_pi_half_mul_lt {c A q : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hA0 : 0 ≤ A) (hA : A ≤ (1570796326794 : ℝ) / 1000000000000 * c)
    (hq : Real.cos A < q) : Real.cos (Real.pi / 2 * c) < q := by
  have hkey := mul_lt_mul_of_pos_right pi_half_gt hc
  have hpos : (0 : ℝ) < Real.pi / 2 := lt_trans (by norm_num) pi_half_gt
  have h1 : A < Real.pi / 2 * c := by linarith
  have h2 : Real.pi / 2 * c ≤ Real.pi := by
    have := mul_le_of_le_one_right hpos.le hc1
    linarith
  exact (Real.cos_lt_cos_of_nonneg_of_le_pi hA0 h2 h1).trans hq

private theorem lt_exp_pi_half_mul {c A q : ℝ} (hc : 0 < c)
    (hA : A ≤ (1570796326794 : ℝ) / 1000000000000 * c)
    (hq : q < Real.exp A) : q < Real.exp (Real.pi / 2 * c) := by
  have hkey := mul_lt_mul_of_pos_right pi_half_gt hc
  exact hq.trans (Real.exp_lt_exp.mpr (by linarith))

private theorem exp_pi_half_mul_lt {c A q : ℝ} (hc : 0 < c)
    (hA : (1570796326795 : ℝ) / 1000000000000 * c ≤ A)
    (hq : Real.exp A < q) : Real.exp (Real.pi / 2 * c) < q := by
  have hkey := mul_lt_mul_of_pos_right pi_half_lt hc
  exact (Real.exp_lt_exp.mpr (by linarith)).trans hq

private theorem lt_exp_neg_pi_half_mul {c A q : ℝ} (hc : 0 < c)
    (hA : (1570796326795 : ℝ) / 1000000000000 * c ≤ A)
    (hq : q < Real.exp (-A)) : q < Real.exp (-(Real.pi / 2) * c) := by
  have hkey := mul_lt_mul_of_pos_right pi_half_lt hc
  exact hq.trans (Real.exp_lt_exp.mpr (by linarith))

private theorem exp_neg_pi_half_mul_lt {c A q : ℝ} (hc : 0 < c)
    (hA : A ≤ (1570796326794 : ℝ) / 1000000000000 * c)
    (hq : Real.exp (-A) < q) : Real.exp (-(Real.pi / 2) * c) < q := by
  have hkey := mul_lt_mul_of_pos_right pi_half_gt hc
  exact (Real.exp_lt_exp.mpr (by linarith)).trans hq

/-! ## Exact quadrant/complement reductions -/

/-- `cos (π/2 · b) = sin (π/2 · c)` when `b + c = 1`. -/
private theorem cos_eq_sin_compl {b c : ℝ} (h : b + c = 1) :
    Real.cos (Real.pi / 2 * b) = Real.sin (Real.pi / 2 * c) := by
  rw [← Real.sin_pi_div_two_sub]
  congr 1
  linear_combination (-(Real.pi / 2)) * h

/-- `sin (π/2 · b) = cos (π/2 · c)` when `b + c = 1`. -/
private theorem sin_eq_cos_compl {b c : ℝ} (h : b + c = 1) :
    Real.sin (Real.pi / 2 * b) = Real.cos (Real.pi / 2 * c) := by
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  linear_combination (-(Real.pi / 2)) * h

/-- `cos (π/2 · b) = -cos (π/2 · c)` when `b = c + 2`. -/
private theorem cos_shift_two {b c : ℝ} (h : b = c + 2) :
    Real.cos (Real.pi / 2 * b) = -Real.cos (Real.pi / 2 * c) := by
  rw [show Real.pi / 2 * b = Real.pi / 2 * c + Real.pi by
        linear_combination (Real.pi / 2) * h,
    Real.cos_add_pi]

/-- `sin (π/2 · b) = -sin (π/2 · c)` when `b = c + 2`. -/
private theorem sin_shift_two {b c : ℝ} (h : b = c + 2) :
    Real.sin (Real.pi / 2 * b) = -Real.sin (Real.pi / 2 * c) := by
  rw [show Real.pi / 2 * b = Real.pi / 2 * c + Real.pi by
        linear_combination (Real.pi / 2) * h,
    Real.sin_add_pi]

/-- `cos (π/2 · b) = -sin (π/2 · c)` when `b = c + 1`. -/
private theorem cos_shift_one {b c : ℝ} (h : b = c + 1) :
    Real.cos (Real.pi / 2 * b) = -Real.sin (Real.pi / 2 * c) := by
  rw [show Real.pi / 2 * b = Real.pi / 2 * c + Real.pi / 2 by
        linear_combination (Real.pi / 2) * h,
    Real.cos_add_pi_div_two]

/-!
## The `t`-group: `sin`/`cos` at the certified `θ`-box endpoints

Pure rational arguments in `[0, 1]`; direct Taylor partial sums suffice.
-/

/-- Field `htsin0` of `NearOneEndpointBounds`. -/
theorem endpoint_htsin0 :
    (320764449975 : ℝ) / 1000000000000 <
      Real.sin ((326536474946 : ℝ) / 1000000000000) :=
  lt_sin_taylor (by norm_num) (by norm_num) 3
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- Field `htsin1` of `NearOneEndpointBounds`. -/
theorem endpoint_htsin1 :
    Real.sin ((326536474949 : ℝ) / 1000000000000) <
      (320764449985 : ℝ) / 1000000000000 :=
  sin_taylor_lt (by norm_num) (by norm_num) 3
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- Field `htcos0` of `NearOneEndpointBounds`. -/
theorem endpoint_htcos0 :
    (947158998071 : ℝ) / 1000000000000 <
      Real.cos ((326536474949 : ℝ) / 1000000000000) :=
  lt_cos_taylor (by norm_num) (by norm_num) 3
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- Field `htcos1` of `NearOneEndpointBounds`. -/
theorem endpoint_htcos1 :
    Real.cos ((326536474946 : ℝ) / 1000000000000) <
      (947158998073 : ℝ) / 1000000000000 :=
  cos_taylor_lt (by norm_num) (by norm_num) 3
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-!
## The `v`-group: factors of `v = i^(i^(i^i))`
-/

/-- Field `hvexp0` of `NearOneEndpointBounds`. -/
theorem endpoint_hvexp0 :
    (60419661058 : ℝ) / 100000000000 <
      Real.exp (-(Real.pi / 2) * ((320764449985 : ℝ) / 1000000000000)) := by
  refine lt_exp_neg_pi_half_mul (A := (1007711239605713 : ℝ) / 2000000000000000)
    (by norm_num) (by norm_num) ?_
  have hU : Real.exp ((1007711239605713 : ℝ) / 2000000000000000) <
      (100000000000 : ℝ) / 60419661058 :=
    exp_upper_rat (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rw [Real.exp_neg, ← one_div, lt_div_iff₀ (Real.exp_pos _)]
  linarith

/-- Field `hvexp1` of `NearOneEndpointBounds`. -/
theorem endpoint_hvexp1 :
    Real.exp (-(Real.pi / 2) * ((320764449975 : ℝ) / 1000000000000)) <
      (60419661060 : ℝ) / 100000000000 := by
  refine exp_neg_pi_half_mul_lt (A := (5038556197868277 : ℝ) / 10000000000000000)
    (by norm_num) (by norm_num) ?_
  have hL : (100000000000 : ℝ) / 60419661060 <
      Real.exp ((5038556197868277 : ℝ) / 10000000000000000) :=
    exp_lower_rat (by norm_num) 14
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rw [Real.exp_neg, ← one_div, div_lt_iff₀ (Real.exp_pos _)]
  linarith

/-- Field `hvcos0` of `NearOneEndpointBounds`. -/
theorem endpoint_hvcos0 :
    (8290717827 : ℝ) / 100000000000 <
      Real.cos (Real.pi / 2 * ((947158998073 : ℝ) / 1000000000000)) := by
  rw [cos_eq_sin_compl (c := (52841001927 : ℝ) / 1000000000000) (by norm_num)]
  exact lt_sin_pi_half_mul (A := (415012258655231 : ℝ) / 5000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (lt_sin_taylor (by norm_num) (by norm_num) 2
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-- Field `hvcos1` of `NearOneEndpointBounds`. -/
theorem endpoint_hvcos1 :
    Real.cos (Real.pi / 2 * ((947158998071 : ℝ) / 1000000000000)) <
      (8290717829 : ℝ) / 100000000000 := by
  rw [cos_eq_sin_compl (c := (52841001929 : ℝ) / 1000000000000) (by norm_num)]
  exact sin_pi_half_mul_lt (A := (103753064667801 : ℝ) / 1250000000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (sin_taylor_lt (by norm_num) (by norm_num) 2
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-- Field `hvsin0` of `NearOneEndpointBounds`. -/
theorem endpoint_hvsin0 :
    (99655727371 : ℝ) / 100000000000 <
      Real.sin (Real.pi / 2 * ((947158998071 : ℝ) / 1000000000000)) := by
  rw [sin_eq_cos_compl (c := (52841001929 : ℝ) / 1000000000000) (by norm_num)]
  exact lt_cos_pi_half_mul (A := (103753064667801 : ℝ) / 1250000000000000)
    (by norm_num) (by norm_num) (by norm_num)
    (lt_cos_taylor (by norm_num) (by norm_num) 2
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-- Field `hvsin1` of `NearOneEndpointBounds`. -/
theorem endpoint_hvsin1 :
    Real.sin (Real.pi / 2 * ((947158998073 : ℝ) / 1000000000000)) <
      (99655727372 : ℝ) / 100000000000 := by
  rw [sin_eq_cos_compl (c := (52841001927 : ℝ) / 1000000000000) (by norm_num)]
  exact cos_pi_half_mul_lt (A := (415012258655231 : ℝ) / 5000000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (cos_taylor_lt (by norm_num) (by norm_num) 2
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-!
## The `hs`-group: the seed products `exp(π/2·a) · (cos, sin)(π/2·b)`

All factors positive; each factor is boxed separately and the boxes are
multiplied.
-/

/-- Field `hsrelo` of `NearOneEndpointBounds`. -/
theorem endpoint_hsrelo :
    (25669119 : ℝ) / 10000000 <
      Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) *
        Real.cos (Real.pi / 2 * ((50092237 : ℝ) / 1000000000)) := by
  have hEpos := Real.exp_pos (Real.pi / 2 * ((602116527 : ℝ) / 1000000000))
  have hE : (6437196767389 : ℝ) / 2500000000000 <
      Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) :=
    lt_exp_pi_half_mul (A := (9458024289135603 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 14
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hC : (996905955681 : ℝ) / 1000000000000 <
      Real.cos (Real.pi / 2 * ((50092237 : ℝ) / 1000000000)) :=
    lt_cos_pi_half_mul (A := (393423509402723 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (lt_cos_taylor (by norm_num) (by norm_num) 3
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-- Field `hsrehi` of `NearOneEndpointBounds`. -/
theorem endpoint_hsrehi :
    Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) *
      Real.cos (Real.pi / 2 * ((50092236 : ℝ) / 1000000000)) <
    (320864 : ℝ) / 125000 := by
  have hEpos := Real.exp_pos (Real.pi / 2 * ((602116528 : ℝ) / 1000000000))
  have hE : Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) <
      (1029951484403 : ℝ) / 400000000000 :=
    exp_pi_half_mul_lt (A := (2364506076212397 : ℝ) / 2500000000000000)
      (by norm_num) (by norm_num)
      (exp_upper_rat (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hC : Real.cos (Real.pi / 2 * ((50092236 : ℝ) / 1000000000)) <
      (4984529779023 : ℝ) / 5000000000000 :=
    cos_pi_half_mul_lt (A := (786847003096981 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cos_taylor_lt (by norm_num) (by norm_num) 3
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-- Field `hsimlo` of `NearOneEndpointBounds`. -/
theorem endpoint_hsimlo :
    (404789 : ℝ) / 2000000 <
      Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) *
        Real.sin (Real.pi / 2 * ((50092236 : ℝ) / 1000000000)) := by
  have hEpos := Real.exp_pos (Real.pi / 2 * ((602116527 : ℝ) / 1000000000))
  have hE : (6437196767389 : ℝ) / 2500000000000 <
      Real.exp (Real.pi / 2 * ((602116527 : ℝ) / 1000000000)) :=
    lt_exp_pi_half_mul (A := (9458024289135603 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 14
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hS : (49127207653 : ℝ) / 625000000000 <
      Real.sin (Real.pi / 2 * ((50092236 : ℝ) / 1000000000)) :=
    lt_sin_pi_half_mul (A := (786847003096981 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (lt_sin_taylor (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-- Field `hsimhi` of `NearOneEndpointBounds`. -/
theorem endpoint_hsimhi :
    Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) *
      Real.sin (Real.pi / 2 * ((50092237 : ℝ) / 1000000000)) <
    (1011973 : ℝ) / 5000000 := by
  have hEpos := Real.exp_pos (Real.pi / 2 * ((602116528 : ℝ) / 1000000000))
  have hE : Real.exp (Real.pi / 2 * ((602116528 : ℝ) / 1000000000)) <
      (1029951484403 : ℝ) / 400000000000 :=
    exp_pi_half_mul_lt (A := (2364506076212397 : ℝ) / 2500000000000000)
      (by norm_num) (by norm_num)
      (exp_upper_rat (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hS : Real.sin (Real.pi / 2 * ((50092237 : ℝ) / 1000000000)) <
      (786035338109 : ℝ) / 10000000000000 :=
    sin_pi_half_mul_lt (A := (393423509402723 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (sin_taylor_lt (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-!
## The `h1`-group: level-1 products

The `cos`/`sin` arguments sit past `π` (multiplier `≈ 2.567`), so they are
first shifted by `π` (`b = c + 2`), which flips the sign; the reduced
arguments `≈ 0.8905` lie in `[0, 1]`.
-/

/-- Field `h1relo` of `NearOneEndpointBounds`. -/
theorem endpoint_h1relo :
    (-(864443 : ℝ) / 1000000) <
      Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) *
        Real.cos (Real.pi / 2 * ((25669119 : ℝ) / 10000000)) := by
  rw [cos_shift_two (c := (5669119 : ℝ) / 10000000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((1011973 : ℝ) / 5000000))
  have hE : Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) <
      (13742672695999 : ℝ) / 10000000000000 :=
    exp_pi_half_mul_lt (A := (1589603471215717 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num)
      (exp_upper_rat (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hC : Real.cos (Real.pi / 2 * ((5669119 : ℝ) / 10000000)) <
      (6290209787117 : ℝ) / 10000000000000 :=
    cos_pi_half_mul_lt (A := (4452515650679037 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cos_taylor_lt (by norm_num) (by norm_num) 4
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-- Field `h1rehi` of `NearOneEndpointBounds`. -/
theorem endpoint_h1rehi :
    Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) *
      Real.cos (Real.pi / 2 * ((320864 : ℝ) / 125000)) <
    (-(432221 : ℝ) / 500000) := by
  rw [cos_shift_two (c := (70864 : ℝ) / 125000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((404789 : ℝ) / 2000000))
  have hE : (13742670537301 : ℝ) / 10000000000000 <
      Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) :=
    lt_exp_pi_half_mul (A := (1589602685816541 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 14
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hC : (6290208565993 : ℝ) / 10000000000000 <
      Real.cos (Real.pi / 2 * ((70864 : ℝ) / 125000)) :=
    lt_cos_pi_half_mul (A := (8905032872160071 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (lt_cos_taylor (by norm_num) (by norm_num) 4
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-- Field `h1imlo` of `NearOneEndpointBounds`. -/
theorem endpoint_h1imlo :
    (-(53417 : ℝ) / 50000) <
      Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) *
        Real.sin (Real.pi / 2 * ((320864 : ℝ) / 125000)) := by
  rw [sin_shift_two (c := (70864 : ℝ) / 125000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((1011973 : ℝ) / 5000000))
  have hE : Real.exp (Real.pi / 2 * ((1011973 : ℝ) / 5000000)) <
      (13742672695999 : ℝ) / 10000000000000 :=
    exp_pi_half_mul_lt (A := (1589603471215717 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num)
      (exp_upper_rat (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hS : Real.sin (Real.pi / 2 * ((70864 : ℝ) / 125000)) <
      (242933882539 : ℝ) / 312500000000 :=
    sin_pi_half_mul_lt (A := (8905032872160071 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (sin_taylor_lt (by norm_num) (by norm_num) 3
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-- Field `h1imhi` of `NearOneEndpointBounds`. -/
theorem endpoint_h1imhi :
    Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) *
      Real.sin (Real.pi / 2 * ((25669119 : ℝ) / 10000000)) <
    (-(1068339 : ℝ) / 1000000) := by
  rw [sin_shift_two (c := (5669119 : ℝ) / 10000000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((404789 : ℝ) / 2000000))
  have hE : (13742670537301 : ℝ) / 10000000000000 <
      Real.exp (Real.pi / 2 * ((404789 : ℝ) / 2000000)) :=
    lt_exp_pi_half_mul (A := (1589602685816541 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 14
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hS : (310955330113 : ℝ) / 400000000000 <
      Real.sin (Real.pi / 2 * ((5669119 : ℝ) / 10000000)) :=
    lt_sin_pi_half_mul (A := (4452515650679037 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (lt_sin_taylor (by norm_num) (by norm_num) 3
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-!
## The `h2`-group: level-2 products

Negative trigonometric arguments are reflected (`cos` even, `sin` odd) and
then complemented (`b + c = 1`).  The `exp` arguments exceed `1`
(`≈ 1.678`), so the lower bound uses a longer direct Taylor sum
(`n = 20`) and the upper bound splits off one factor of `exp 1`.
-/

/-- Field `h2relo` of `NearOneEndpointBounds`. -/
theorem endpoint_h2relo :
    (11317 : ℝ) / 10000 <
      Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) *
        Real.cos (Real.pi / 2 * (-(864443 : ℝ) / 1000000)) := by
  rw [show Real.pi / 2 * (-(864443 : ℝ) / 1000000) =
        -(Real.pi / 2 * ((864443 : ℝ) / 1000000)) by ring,
    Real.cos_neg,
    cos_eq_sin_compl (c := (135557 : ℝ) / 1000000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((1068339 : ℝ) / 1000000))
  have hE : (53556012560473 : ℝ) / 10000000000000 <
      Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) :=
    lt_exp_pi_half_mul (A := (16781429769707751 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 20
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hS : (422654028277 : ℝ) / 2000000000000 <
      Real.sin (Real.pi / 2 * ((135557 : ℝ) / 1000000)) :=
    lt_sin_pi_half_mul (A := (1064662188356071 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (lt_sin_taylor (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-- The upper `exp` bound shared by `h2rehi` and `h2imlo`: the argument
`π/2 · 1.06834 ≈ 1.6781` exceeds `1`, so one factor of `exp 1` is split off
and bounded by the 20-decimal certificate. -/
private theorem h2_exp_upper :
    Real.exp (Real.pi / 2 * ((53417 : ℝ) / 50000)) <
      (10711219337237 : ℝ) / 2000000000000 := by
  refine exp_pi_half_mul_lt (A := (2097680684710213 : ℝ) / 1250000000000000)
    (by norm_num) (by norm_num) ?_
  have hsplit : Real.exp ((2097680684710213 : ℝ) / 1250000000000000) =
      Real.exp 1 * Real.exp ((847680684710213 : ℝ) / 1250000000000000) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  calc Real.exp 1 * Real.exp ((847680684710213 : ℝ) / 1250000000000000)
      ≤ ((363916618873 : ℝ) / 133877442384 + 1 / 10 ^ 20) *
        ((∑ m ∈ Finset.range 14,
            ((847680684710213 : ℝ) / 1250000000000000) ^ m / (Nat.factorial m : ℝ)) +
          ((847680684710213 : ℝ) / 1250000000000000) ^ 14 * ((14 : ℝ) + 1) /
            ((Nat.factorial 14 : ℝ) * (14 : ℝ))) :=
        mul_le_mul exp_one_upper_cert
          (exp_upper_taylor (by norm_num) (by norm_num))
          (Real.exp_pos _).le (by positivity)
    _ < (10711219337237 : ℝ) / 2000000000000 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Field `h2rehi` of `NearOneEndpointBounds`. -/
theorem endpoint_h2rehi :
    Real.exp (Real.pi / 2 * ((53417 : ℝ) / 50000)) *
      Real.cos (Real.pi / 2 * (-(432221 : ℝ) / 500000)) <
    (5659 : ℝ) / 5000 := by
  rw [show Real.pi / 2 * (-(432221 : ℝ) / 500000) =
        -(Real.pi / 2 * ((432221 : ℝ) / 500000)) by ring,
    Real.cos_neg,
    cos_eq_sin_compl (c := (67779 : ℝ) / 500000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((53417 : ℝ) / 50000))
  have hE := h2_exp_upper
  have hS : Real.sin (Real.pi / 2 * ((67779 : ℝ) / 500000)) <
      (422657098923 : ℝ) / 2000000000000 :=
    sin_pi_half_mul_lt (A := (2129340084676767 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (sin_taylor_lt (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hS, mul_pos hEpos (sub_pos.mpr hS)]

/-- Field `h2imlo` of `NearOneEndpointBounds`. -/
theorem endpoint_h2imlo :
    (-(52347 : ℝ) / 10000) <
      Real.exp (Real.pi / 2 * ((53417 : ℝ) / 50000)) *
        Real.sin (Real.pi / 2 * (-(864443 : ℝ) / 1000000)) := by
  rw [show Real.pi / 2 * (-(864443 : ℝ) / 1000000) =
        -(Real.pi / 2 * ((864443 : ℝ) / 1000000)) by ring,
    Real.sin_neg,
    sin_eq_cos_compl (c := (135557 : ℝ) / 1000000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((53417 : ℝ) / 50000))
  have hE := h2_exp_upper
  have hC : Real.cos (Real.pi / 2 * ((135557 : ℝ) / 1000000)) <
      (977415414803 : ℝ) / 1000000000000 :=
    cos_pi_half_mul_lt (A := (1064662188356071 : ℝ) / 5000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (cos_taylor_lt (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-- Field `h2imhi` of `NearOneEndpointBounds`. -/
theorem endpoint_h2imhi :
    Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) *
      Real.sin (Real.pi / 2 * (-(432221 : ℝ) / 500000)) <
    (-(52346 : ℝ) / 10000) := by
  rw [show Real.pi / 2 * (-(432221 : ℝ) / 500000) =
        -(Real.pi / 2 * ((432221 : ℝ) / 500000)) by ring,
    Real.sin_neg,
    sin_eq_cos_compl (c := (67779 : ℝ) / 500000) (by norm_num)]
  have hEpos := Real.exp_pos (Real.pi / 2 * ((1068339 : ℝ) / 1000000))
  have hE : (53556012560473 : ℝ) / 10000000000000 <
      Real.exp (Real.pi / 2 * ((1068339 : ℝ) / 1000000)) :=
    lt_exp_pi_half_mul (A := (16781429769707751 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num)
      (exp_lower_rat (by norm_num) 20
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hC : (9774150827451 : ℝ) / 10000000000000 <
      Real.cos (Real.pi / 2 * ((67779 : ℝ) / 500000)) :=
    lt_cos_pi_half_mul (A := (2129340084676767 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (lt_cos_taylor (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  nlinarith [hE, hC, mul_pos hEpos (sub_pos.mpr hC)]

/-!
## The final level-3 factors: `hexp0`/`hexp1` and `hcos0`/`hcos1`

The `hexp` arguments are `≈ 8.22`, handled by splitting off `(exp 1)^8` for
the upper bound and by a direct 30-term Taylor sum for the (loose) lower
bound.  The tight `hcos1` bound `-1027/5000` sits `1.4·10⁻⁶` above the true
value `-0.2054014...`.
-/

/-- Field `hexp0` of `NearOneEndpointBounds` (corrected constant `3723`;
the original constant `3724` is refuted in `uncorrected_hexp0_is_false`). -/
theorem endpoint_hexp0 :
    (3723 : ℝ) < Real.exp (Real.pi / 2 * ((52346 : ℝ) / 10000)) :=
  lt_exp_pi_half_mul (A := (82224904522358723 : ℝ) / 10000000000000000)
    (by norm_num) (by norm_num)
    (exp_lower_rat (by norm_num) 30
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-- Field `hexp1` of `NearOneEndpointBounds`. -/
theorem endpoint_hexp1 :
    Real.exp (Real.pi / 2 * ((52347 : ℝ) / 10000)) < 3725 := by
  refine exp_pi_half_mul_lt (A := (41113237659368933 : ℝ) / 5000000000000000)
    (by norm_num) (by norm_num) ?_
  have hsplit : Real.exp ((41113237659368933 : ℝ) / 5000000000000000) =
      Real.exp 1 ^ 8 * Real.exp ((1113237659368933 : ℝ) / 5000000000000000) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 8 * Real.exp ((1113237659368933 : ℝ) / 5000000000000000)
      ≤ ((27182818285 : ℝ) / 10000000000) ^ 8 *
        ((∑ m ∈ Finset.range 14,
            ((1113237659368933 : ℝ) / 5000000000000000) ^ m / (Nat.factorial m : ℝ)) +
          ((1113237659368933 : ℝ) / 5000000000000000) ^ 14 * ((14 : ℝ) + 1) /
            ((Nat.factorial 14 : ℝ) * (14 : ℝ))) :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_d10 8)
          (exp_upper_taylor (by norm_num) (by norm_num))
          (Real.exp_pos _).le (by positivity)
    _ < 3725 := by norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Field `hcos0` of `NearOneEndpointBounds`. -/
theorem endpoint_hcos0 :
    (-(257 : ℝ) / 1250) < Real.cos (Real.pi / 2 * ((5659 : ℝ) / 5000)) := by
  rw [cos_shift_one (c := (659 : ℝ) / 5000) (by norm_num)]
  have hS : Real.sin (Real.pi / 2 * ((659 : ℝ) / 5000)) < (257 : ℝ) / 1250 :=
    sin_pi_half_mul_lt (A := (2070309558715811 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (sin_taylor_lt (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  linarith

/-- Field `hcos1` of `NearOneEndpointBounds` (corrected constant
`-1027/5000 = -0.2054`; the original constant `-411/2000 = -0.2055` is
refuted in `uncorrected_hcos1_is_false`). -/
theorem endpoint_hcos1 :
    Real.cos (Real.pi / 2 * ((11317 : ℝ) / 10000)) <
      (-(1027 : ℝ) / 5000) := by
  rw [cos_shift_one (c := (1317 : ℝ) / 10000) (by norm_num)]
  have hS : (1027 : ℝ) / 5000 <
      Real.sin (Real.pi / 2 * ((1317 : ℝ) / 10000)) :=
    lt_sin_pi_half_mul (A := (2068738762387697 : ℝ) / 10000000000000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (lt_sin_taylor (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  linarith

/-!
## Historical record: the two originally stated fields were false

Before the repair recorded in the module docstring, the certificate's
`hexp0`/`hcos1` fields carried constants evaluated at the true (mid-box)
level-2 values instead of at the box endpoints actually named in the
statements:

* `exp (π/2 · 5.2346) = 3723.7647... < 3724`, refuting the original `hexp0`;
* `cos (π/2 · 1.1317) = -0.2054014... > -0.2055`, refuting the original
  `hcos1`.

The two theorems below preserve those refutations; they are what forced the
window widening of the `A198683N12Symbolic` level-3 ladder.
-/

/-- Refutation of the *original* (pre-repair) field `hexp0`: its stated lower
bound `3724` actually *exceeds* `exp (π/2 · 5.2346) ≈ 3723.7647`. -/
theorem uncorrected_hexp0_is_false :
    Real.exp (Real.pi / 2 * ((52346 : ℝ) / 10000)) < 3724 := by
  refine exp_pi_half_mul_lt (A := (82224904522411071 : ℝ) / 10000000000000000)
    (by norm_num) (by norm_num) ?_
  have hsplit : Real.exp ((82224904522411071 : ℝ) / 10000000000000000) =
      Real.exp 1 ^ 8 * Real.exp ((2224904522411071 : ℝ) / 10000000000000000) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hsplit]
  calc Real.exp 1 ^ 8 * Real.exp ((2224904522411071 : ℝ) / 10000000000000000)
      ≤ ((27182818285 : ℝ) / 10000000000) ^ 8 *
        ((∑ m ∈ Finset.range 14,
            ((2224904522411071 : ℝ) / 10000000000000000) ^ m / (Nat.factorial m : ℝ)) +
          ((2224904522411071 : ℝ) / 10000000000000000) ^ 14 * ((14 : ℝ) + 1) /
            ((Nat.factorial 14 : ℝ) * (14 : ℝ))) :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_le_d10 8)
          (exp_upper_taylor (by norm_num) (by norm_num))
          (Real.exp_pos _).le (by positivity)
    _ < 3724 := by norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Refutation of the *original* (pre-repair) field `hcos1`: its stated upper
bound `-411/2000 = -0.2055` is actually *below*
`cos (π/2 · 1.1317) ≈ -0.2054014`. -/
theorem uncorrected_hcos1_is_false :
    (-(411 : ℝ) / 2000) < Real.cos (Real.pi / 2 * ((11317 : ℝ) / 10000)) := by
  rw [cos_shift_one (c := (1317 : ℝ) / 10000) (by norm_num)]
  have hS : Real.sin (Real.pi / 2 * ((1317 : ℝ) / 10000)) < (411 : ℝ) / 2000 :=
    sin_pi_half_mul_lt (A := (258592345298627 : ℝ) / 1250000000000000)
      (by norm_num) (by norm_num) (by norm_num)
      (sin_taylor_lt (by norm_num) (by norm_num) 2
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  linarith

/-!
## The bundle and the unconditional near-`1` split
-/

/-- Every scalar endpoint estimate of the near-`1` split, bundled. -/
theorem nearOneEndpointBounds : A198683N12Certificate.NearOneEndpointBounds :=
  ⟨endpoint_htsin0, endpoint_htsin1, endpoint_htcos0, endpoint_htcos1,
    endpoint_hvexp0, endpoint_hvexp1, endpoint_hvcos0, endpoint_hvcos1,
    endpoint_hvsin0, endpoint_hvsin1,
    endpoint_hsrelo, endpoint_hsrehi, endpoint_hsimlo, endpoint_hsimhi,
    endpoint_h1relo, endpoint_h1rehi, endpoint_h1imlo, endpoint_h1imhi,
    endpoint_h2relo, endpoint_h2rehi, endpoint_h2imlo, endpoint_h2imhi,
    endpoint_hexp0, endpoint_hexp1, endpoint_hcos0, endpoint_hcos1⟩

/-- The near-one split, now unconditional. -/
theorem nearOneSplit : A198683N12Certificate.NearOneSplit :=
  A198683N12Certificate.nearOneSplit_of_endpointBounds nearOneEndpointBounds

/-!
## The tightened decision tree

With `nearOneSplit` proved, the near-`1` dichotomy disappears from the
`A198683(12)` decision tree of `LeanProofs.A198683N12Certificate`: any
partition witness alone now confines the value to two possibilities, and the
overflow no-miracles hypothesis alone decides between them.
-/

/-- Any partition witness alone confines `a198683 12` to two values; the
near-`1` split is no longer a hypothesis. -/
theorem a198683_twelve_mem_of_witness
    (w : A198683N12Certificate.N12PartitionWitness) :
    a198683 12 ∈ ({2925, 2926} : Set ℕ) :=
  w.a198683_twelve_mem_of_nearOneSplit nearOneSplit

/-- With a partition witness, the overflow no-miracles hypothesis pins the
expected value. -/
theorem a198683_twelve_eq_2926_of_overflowIsolated
    (w : A198683N12Certificate.N12PartitionWitness)
    (h : A198683N12Certificate.OverflowIsolated w) :
    a198683 12 = 2926 :=
  w.a198683_twelve_eq_2926 nearOneSplit h

/-- With a partition witness, an overflow collision forces the other value. -/
theorem a198683_twelve_eq_2925_of_overflowCollision
    (w : A198683N12Certificate.N12PartitionWitness)
    (h : ¬A198683N12Certificate.OverflowIsolated w) :
    a198683 12 = 2925 :=
  w.a198683_twelve_eq_2925_of_overflowCollision nearOneSplit h

end A198683N12Endpoints

end LeanProofs
