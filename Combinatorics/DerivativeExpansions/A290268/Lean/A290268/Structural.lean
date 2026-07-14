import A290268.Core
import A290268.Count

/-!
# A290268: the structural inclusion `support ⊆ S n`

The support characterization `coeff n j k ≠ 0 ↔ (j, k) ∈ S n` splits into two
inclusions.  This module proves the **structural** (left-to-right) inclusion
almost entirely from the zero lemmas of `A290268.Core`, reducing it to a single
residual fact — the vanishing of the coefficients on the *hole line* — which is
supplied downstream from the power-series reduction and the hole-vanishing
theorem.

The one new structural fact proved here is `coeff_negtop_eq_zero`: in a negative
column `j < 0` the top log-degree `k = (n + j)/2` already vanishes, so negative
columns are truncated one step below the triangle.  This is the `D = 0`,
`j < 0` edge of the support, and it has a clean self-contained induction: the
top-degree coefficients `t_n(j) := coeff n j ((n+j)/2)` satisfy
`t_{n+1}(j) = 2 t_n(j-1) + (j+1) t_n(j+1)`, from which `t_n(j) = 0` for `j < 0`
follows immediately by induction.
-/

namespace LeanProofs

namespace A290268

/-- In a negative column `j < 0`, the top log-degree coefficient
(`(n : ℤ) + j = 2k`) vanishes.  Proved by induction along the differentiation
recurrence: the only surviving neighbours are again negative-column tops one
level down, or carry a vanishing weight `(j + 1)` at `j = -1`. -/
theorem coeff_negtop_eq_zero : ∀ (n : ℕ) (j k : ℤ),
    (n : ℤ) + j = 2 * k → j < 0 → coeff n j k = 0
  | 0, j, k, _, hj => by
      rw [coeff_zero, if_neg]; rintro ⟨rfl, _⟩; exact absurd hj (by norm_num)
  | n + 1, j, k, hjk, hj => by
      have h1 : coeff n (j - 1) (k - 1) = 0 :=
        coeff_negtop_eq_zero n (j - 1) (k - 1) (by omega) (by omega)
      have h2 : coeff n (j - 1) k = 0 :=
        coeff_eq_zero_of_two_k_gt n (j - 1) k (by omega)
      have h4 : coeff n (j + 1) (k + 1) = 0 :=
        coeff_eq_zero_of_two_k_gt n (j + 1) (k + 1) (by omega)
      have h3 : (j + 1) * coeff n (j + 1) k = 0 := by
        rcases lt_or_eq_of_le (show j + 1 ≤ 0 by omega) with h | h
        · rw [coeff_negtop_eq_zero n (j + 1) k (by omega) h, mul_zero]
        · rw [h, zero_mul]
      rw [coeff_succ, h1, h2, h4, h3]; ring

/-- **Structural inclusion, modulo the hole.**  Given that the coefficients
vanish on the hole line (`hhole`), every nonzero coefficient of the n-th
derivative lies in the conjectured support set `S n`.  The remaining
ingredients — correct parity, the triangle bounds, and the negative-column
truncation — come from `A290268.Core` and `coeff_negtop_eq_zero`.

The hypothesis `hhole` is exactly the hole-vanishing statement, discharged
downstream (`A290268.Hole` via the power-series reduction). -/
theorem mem_S_of_coeff_ne_zero (n : ℕ)
    (hhole : ∀ j k : ℤ,
      (n : ℤ) % 2 = 1 → (-j) % 4 = (n : ℤ) % 4 → 3 ≤ -j → 2 * (-j) - 1 ≤ (n : ℤ) →
        2 * k = (n : ℤ) + 2 * j + 1 → coeff n j k = 0)
    (j k : ℤ) (hne : coeff n j k ≠ 0) : (j, k) ∈ S n := by
  rw [mem_S]
  have hpar : ((n : ℤ) + j) % 2 = 0 := by
    by_contra h; exact hne (coeff_eq_zero_of_parity n j k (by omega))
  have hk0 : 0 ≤ k := by
    by_contra h; exact hne (coeff_eq_zero_of_k_neg n j k (by omega))
  have hjn : j ≤ (n : ℤ) := by
    by_contra h; exact hne (coeff_eq_zero_of_gt n j k (by omega))
  have htri : 2 * k ≤ (n : ℤ) + j := by
    by_contra h; exact hne (coeff_eq_zero_of_two_k_gt n j k (by omega))
  refine ⟨hpar, hk0, ?_⟩
  by_cases hj : 0 ≤ j
  · exact Or.inl ⟨hj, hjn, htri⟩
  · push_neg at hj
    refine Or.inr ⟨hj, ?_, ?_⟩
    · have hnegtop : 2 * k ≠ (n : ℤ) + j := fun heq =>
        hne (coeff_negtop_eq_zero n j k (by omega) hj)
      omega
    · rintro ⟨hn2, hmod, hge, hle, heq⟩
      exact hne (hhole j k hn2 hmod hge hle heq)

end A290268

end LeanProofs
