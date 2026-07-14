import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A290268: terms of the expanded n-th derivative of x^(x²) — the exact model

[A290268](https://oeis.org/A290268) counts the terms of the fully expanded
n-th derivative of `x^(x²)`. Every such derivative is an integer combination
of the functions `x^(x²+j) · (log x)^k`, and differentiating one of them gives

```text
d/dx (x^(x²+j) (log x)^k) =
  2 x^(x²+j+1) (log x)^(k+1) + x^(x²+j+1) (log x)^k
  + j x^(x²+j-1) (log x)^k + k x^(x²+j-1) (log x)^(k-1).
```

This module records the resulting coefficient array `coeff n j k` as a lattice
recurrence, the counting function `a n` (the number of nonzero coefficients,
which is what the OEIS entry computes with `Expand`/`nops`), the structural
support bounds (parity, triangle, and log-degree bounds), and the conjectured
closed form `closedForm`.

The OEIS conjecture, in the form proved conditionally downstream
(`LeanProofs/A290268Main.lean`), is `a n = closedForm n` for all `n`; the
closed form is interchangeable with the published order-12 linear recurrence
(`LeanProofs/A290268ClosedForm.lean`).

`a` is defined from the *symbolic* expansion, exactly as the Maple and
Mathematica programs in the OEIS entry compute it.  (Identifying the symbolic
term count with a statement about the analytic derivative additionally uses
the linear independence of the functions `x^(x²+j) (log x)^k` on `(1, ∞)`,
which is not formalized here.)
-/

namespace LeanProofs

namespace A290268

/-- `coeff n j k` is the coefficient of `x^(x²+j) · (log x)^k` in the fully
expanded n-th derivative of `x^(x²)`.  Both `j` and `k` range over `ℤ`
(the coefficient vanishes for `k < 0`, `|j| > n`, and `2k > n + j`;
see the support lemmas below). -/
def coeff : ℕ → ℤ → ℤ → ℤ
  | 0, j, k => if j = 0 ∧ k = 0 then 1 else 0
  | n + 1, j, k =>
      2 * coeff n (j - 1) (k - 1) + coeff n (j - 1) k
        + (j + 1) * coeff n (j + 1) k + (k + 1) * coeff n (j + 1) (k + 1)

@[simp] theorem coeff_zero (j k : ℤ) :
    coeff 0 j k = if j = 0 ∧ k = 0 then 1 else 0 := rfl

theorem coeff_succ (n : ℕ) (j k : ℤ) :
    coeff (n + 1) j k =
      2 * coeff n (j - 1) (k - 1) + coeff n (j - 1) k
        + (j + 1) * coeff n (j + 1) k + (k + 1) * coeff n (j + 1) (k + 1) := rfl

/-- The coefficient vanishes for negative log-degree. -/
theorem coeff_eq_zero_of_k_neg : ∀ (n : ℕ) (j k : ℤ), k < 0 → coeff n j k = 0
  | 0, j, k, hk => by
    rw [coeff_zero, if_neg]
    rintro ⟨rfl, rfl⟩; exact absurd hk (by norm_num)
  | n + 1, j, k, hk => by
    have h1 := coeff_eq_zero_of_k_neg n (j - 1) (k - 1) (by omega)
    have h2 := coeff_eq_zero_of_k_neg n (j - 1) k hk
    have h3 := coeff_eq_zero_of_k_neg n (j + 1) k hk
    have h4 : (k + 1) * coeff n (j + 1) (k + 1) = 0 := by
      rcases eq_or_lt_of_le (show k + 1 ≤ 0 by omega) with h | h
      · rw [h, zero_mul]
      · rw [coeff_eq_zero_of_k_neg n (j + 1) (k + 1) h, mul_zero]
    rw [coeff_succ, h1, h2, h3, h4]; ring

/-- The coefficient vanishes above the exponent range `j ≤ n`. -/
theorem coeff_eq_zero_of_gt : ∀ (n : ℕ) (j k : ℤ), (n : ℤ) < j → coeff n j k = 0
  | 0, j, k, hj => by
    rw [coeff_zero, if_neg]
    rintro ⟨rfl, rfl⟩; exact absurd hj (by norm_num)
  | n + 1, j, k, hj => by
    have h1 := coeff_eq_zero_of_gt n (j - 1) (k - 1) (by omega)
    have h2 := coeff_eq_zero_of_gt n (j - 1) k (by omega)
    have h3 := coeff_eq_zero_of_gt n (j + 1) k (by omega)
    have h4 := coeff_eq_zero_of_gt n (j + 1) (k + 1) (by omega)
    rw [coeff_succ, h1, h2, h3, h4]; ring

/-- The coefficient vanishes below the exponent range `-n ≤ j`. -/
theorem coeff_eq_zero_of_lt : ∀ (n : ℕ) (j k : ℤ), j < -(n : ℤ) → coeff n j k = 0
  | 0, j, k, hj => by
    rw [coeff_zero, if_neg]
    rintro ⟨rfl, rfl⟩; exact absurd hj (by norm_num)
  | n + 1, j, k, hj => by
    have h1 := coeff_eq_zero_of_lt n (j - 1) (k - 1) (by omega)
    have h2 := coeff_eq_zero_of_lt n (j - 1) k (by omega)
    have h3 := coeff_eq_zero_of_lt n (j + 1) k (by omega)
    have h4 := coeff_eq_zero_of_lt n (j + 1) (k + 1) (by omega)
    rw [coeff_succ, h1, h2, h3, h4]; ring

/-- Parity: the coefficient vanishes unless `j ≡ n (mod 2)`. -/
theorem coeff_eq_zero_of_parity : ∀ (n : ℕ) (j k : ℤ), (n + j) % 2 = 1 → coeff n j k = 0
  | 0, j, k, hj => by
    rw [coeff_zero, if_neg]
    rintro ⟨rfl, rfl⟩; simp at hj
  | n + 1, j, k, hj => by
    have h1 := coeff_eq_zero_of_parity n (j - 1) (k - 1) (by omega)
    have h2 := coeff_eq_zero_of_parity n (j - 1) k (by omega)
    have h3 := coeff_eq_zero_of_parity n (j + 1) k (by omega)
    have h4 := coeff_eq_zero_of_parity n (j + 1) (k + 1) (by omega)
    rw [coeff_succ, h1, h2, h3, h4]; ring

/-- Log-degree bound: the coefficient vanishes when `2k > n + j`
(each differentiation step raises `2k` by at most as much as `n + j`). -/
theorem coeff_eq_zero_of_two_k_gt : ∀ (n : ℕ) (j k : ℤ), (n : ℤ) + j < 2 * k → coeff n j k = 0
  | 0, j, k, h => by
    rw [coeff_zero, if_neg]
    rintro ⟨rfl, rfl⟩; exact absurd h (by norm_num)
  | n + 1, j, k, h => by
    have h1 := coeff_eq_zero_of_two_k_gt n (j - 1) (k - 1) (by omega)
    have h2 := coeff_eq_zero_of_two_k_gt n (j - 1) k (by omega)
    have h3 := coeff_eq_zero_of_two_k_gt n (j + 1) k (by omega)
    have h4 := coeff_eq_zero_of_two_k_gt n (j + 1) (k + 1) (by omega)
    rw [coeff_succ, h1, h2, h3, h4]; ring

/-- All nonzero coefficients lie in the window `-n ≤ j ≤ n`, `0 ≤ k ≤ n`. -/
theorem support_subset_window (n : ℕ) (j k : ℤ)
    (h : coeff n j k ≠ 0) : -(n : ℤ) ≤ j ∧ j ≤ n ∧ 0 ≤ k ∧ k ≤ n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hj; exact h (coeff_eq_zero_of_lt n j k (by omega))
  · by_contra hj; exact h (coeff_eq_zero_of_gt n j k (by omega))
  · by_contra hk; exact h (coeff_eq_zero_of_k_neg n j k (by omega))
  · by_contra hk
    have hjn : j ≤ n := by
      by_contra hj; exact h (coeff_eq_zero_of_gt n j k (by omega))
    exact h (coeff_eq_zero_of_two_k_gt n j k (by omega))

/-- `a n` is the number of terms of the fully expanded n-th derivative of
`x^(x²)`: the number of pairs `(j, k)` with a nonzero coefficient. -/
def a (n : ℕ) : ℕ :=
  (((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (0 : ℤ) n)).filter
    fun p => coeff n p.1 p.2 ≠ 0).card

/-- The conjectured closed form (Luschny's version of the conjecture):
`a(2m) = 2m² + 2m + 1` and `a(2m-1) = 2m² - ⌊m/4⌋`, i.e.
`a(n) = n²/2 + n + 1 - (n mod 2) * (1/2 + ⌊(n+1)/8⌋)`. -/
def closedForm (n : ℕ) : ℕ :=
  if n % 2 = 0 then n ^ 2 / 2 + n + 1 else (n + 1) ^ 2 / 2 - (n + 1) / 8

end A290268

end LeanProofs
