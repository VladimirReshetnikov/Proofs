import A290268.Core
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.IntervalCases

/-!
# A290268: cardinality of the conjectured support set

This module is pure finite combinatorics: it defines the conjectured support
set `S n ⊆ ℤ × ℤ` of the coefficient array of
[A290268](https://oeis.org/A290268) and proves that its cardinality equals
`closedForm n`.  No facts about `coeff` are used here.

The set `S n` consists of the pairs `(j, k)` with `j ≡ n (mod 2)` and

* for `0 ≤ j ≤ n`: all `0 ≤ k ≤ (n + j) / 2`;
* for `j < 0`, writing `r = -j`: all `0 ≤ k ≤ (n - r) / 2 - 1`, **except**
  that the single point `k = (n - 2r + 1) / 2` is removed when `n` is odd,
  `r ≥ 3`, `r ≡ n (mod 4)` and `2r - 1 ≤ n`.

The cardinality is computed by slicing `S n` into columns `j = n - 2i` for
`i = 0, …, n`: a nonnegative column has `n - i + 1` points, a negative column
has `n - i` points minus one for the removed point ("hole").  Summing and
counting the holes (an arithmetic-progression count) gives `closedForm n`.
-/

namespace LeanProofs

namespace A290268

open Finset

/-- The conjectured support set of the coefficient array of the n-th
derivative: pairs `(j, k)` as described in the module docstring.  The removed
point condition `2k = n + 2j + 1` encodes `k = (n - 2r + 1) / 2` with
`r = -j`. -/
def S (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (n : ℤ))).filter fun p =>
    ((n : ℤ) + p.1) % 2 = 0 ∧
      ((0 ≤ p.1 ∧ 2 * p.2 ≤ (n : ℤ) + p.1) ∨
        (p.1 < 0 ∧ 2 * p.2 ≤ (n : ℤ) + p.1 - 2 ∧
          ¬((n : ℤ) % 2 = 1 ∧ (-p.1) % 4 = (n : ℤ) % 4 ∧ 3 ≤ -p.1 ∧
            2 * (-p.1) - 1 ≤ (n : ℤ) ∧ 2 * p.2 = (n : ℤ) + 2 * p.1 + 1)))

/-- Membership in the support set, spelled out. -/
theorem mem_S (n : ℕ) (j k : ℤ) :
    (j, k) ∈ S n ↔
      ((n : ℤ) + j) % 2 = 0 ∧ 0 ≤ k ∧
        ((0 ≤ j ∧ j ≤ (n : ℤ) ∧ 2 * k ≤ (n : ℤ) + j) ∨
          (j < 0 ∧ 2 * k ≤ (n : ℤ) + j - 2 ∧
            ¬((n : ℤ) % 2 = 1 ∧ (-j) % 4 = (n : ℤ) % 4 ∧ 3 ≤ -j ∧
              2 * (-j) - 1 ≤ (n : ℤ) ∧ 2 * k = (n : ℤ) + 2 * j + 1))) := by
  simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

/-- The support set lies in the window `-n ≤ j ≤ n`, `0 ≤ k ≤ n` used by the
counting function `a`. -/
theorem S_subset_window (n : ℕ) :
    S n ⊆ (Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (n : ℤ)) :=
  Finset.filter_subset _ _

/-- Size of the column `j = n - 2i` of the support set: `n - i + 1` for a
nonnegative column, `n - i` for a negative column, minus one for the removed
point when `n` is odd, `i ≡ n (mod 2)`, `n + 3 ≤ 2i` and `4i ≤ 3n + 1`
(the translation of `r ≥ 3`, `r ≡ n (mod 4)`, `2r - 1 ≤ n` to `r = 2i - n`). -/
def colCard (n i : ℕ) : ℕ :=
  if 2 * i ≤ n then n - i + 1
  else if n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1 then n - i - 1
  else n - i

/-- The fiber of `S n` over the column `j = n - 2i` has `colCard n i`
elements. -/
theorem card_fiber (n i : ℕ) (hi : i < n + 1) :
    ((S n).filter fun p => p.1 = (n : ℤ) - 2 * (i : ℤ)).card = colCard n i := by
  have hinj : Function.Injective fun k : ℤ => ((n : ℤ) - 2 * (i : ℤ), k) :=
    fun a b hab => (Prod.ext_iff.mp hab).2
  by_cases h2 : 2 * i ≤ n
  · -- nonnegative column: `k` ranges over `Icc 0 (n - i)`
    have himg : ((S n).filter fun p => p.1 = (n : ℤ) - 2 * (i : ℤ))
        = (Finset.Icc (0 : ℤ) ((n : ℤ) - (i : ℤ))).image
            (fun k => ((n : ℤ) - 2 * (i : ℤ), k)) := by
      ext ⟨j, k⟩
      simp only [Finset.mem_filter, mem_S, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
      constructor
      · rintro ⟨hS, rfl⟩
        exact ⟨k, ⟨by omega, by omega⟩, rfl, rfl⟩
      · rintro ⟨k', ⟨hk0, hk1⟩, hj, rfl⟩
        exact ⟨by omega, hj.symm⟩
    rw [himg, Finset.card_image_of_injective _ hinj, Int.card_Icc]
    simp only [colCard]
    split_ifs <;> omega
  · by_cases hh : n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1
    · -- negative column with a removed point
      have himg : ((S n).filter fun p => p.1 = (n : ℤ) - 2 * (i : ℤ))
          = ((Finset.Icc (0 : ℤ) ((n : ℤ) - (i : ℤ) - 1)).erase
                (((3 * n + 1 - 4 * i) / 2 : ℕ) : ℤ)).image
              (fun k => ((n : ℤ) - 2 * (i : ℤ), k)) := by
        ext ⟨j, k⟩
        simp only [Finset.mem_filter, mem_S, Finset.mem_image, Finset.mem_erase,
          Finset.mem_Icc, Prod.mk.injEq]
        constructor
        · rintro ⟨hS, rfl⟩
          exact ⟨k, ⟨by omega, by omega, by omega⟩, rfl, rfl⟩
        · rintro ⟨k', ⟨hne, hk0, hk1⟩, hj, rfl⟩
          exact ⟨by omega, hj.symm⟩
      have hmem : (((3 * n + 1 - 4 * i) / 2 : ℕ) : ℤ) ∈
          Finset.Icc (0 : ℤ) ((n : ℤ) - (i : ℤ) - 1) := by
        rw [Finset.mem_Icc]
        omega
      rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem hmem,
        Int.card_Icc]
      simp only [colCard]
      split_ifs <;> omega
    · -- negative column, no removed point
      have himg : ((S n).filter fun p => p.1 = (n : ℤ) - 2 * (i : ℤ))
          = (Finset.Icc (0 : ℤ) ((n : ℤ) - (i : ℤ) - 1)).image
              (fun k => ((n : ℤ) - 2 * (i : ℤ), k)) := by
        ext ⟨j, k⟩
        simp only [Finset.mem_filter, mem_S, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]
        constructor
        · rintro ⟨hS, rfl⟩
          exact ⟨k, ⟨by omega, by omega⟩, rfl, rfl⟩
        · rintro ⟨k', ⟨hk0, hk1⟩, hj, rfl⟩
          exact ⟨by omega, hj.symm⟩
      rw [himg, Finset.card_image_of_injective _ hinj, Int.card_Icc]
      simp only [colCard]
      split_ifs <;> omega

/-- Odd numbers below `b`: there are `b / 2` of them. -/
theorem card_odd_range (b : ℕ) :
    ((Finset.range b).filter fun i => i % 2 = 1).card = b / 2 := by
  induction b with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : m % 2 = 1
    · rw [if_pos h, Finset.card_insert_of_notMem
        (fun hmem => absurd (Finset.mem_range.mp (Finset.mem_filter.mp hmem).1)
          (lt_irrefl m)), ih]
      omega
    · rw [if_neg h, ih]
      omega

/-- Odd numbers in `[a, b)`: there are `b / 2 - a / 2` of them. -/
theorem card_odd_Ico (a b : ℕ) (hab : a ≤ b) :
    ((Finset.Ico a b).filter fun i => i % 2 = 1).card = b / 2 - a / 2 := by
  have key := card_odd_range b
  rw [Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) hab,
    Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 a b))] at key
  have h0 := card_odd_range a
  rw [Finset.range_eq_Ico] at h0
  omega

/-- For even `n` there are no removed points. -/
theorem card_hole_even (n : ℕ) (hn : n % 2 = 0) :
    ((Finset.range (n + 1)).filter fun i =>
      n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  omega

/-- For odd `n` the removed points are counted by `⌊(n + 1) / 8⌋`. -/
theorem card_hole_odd (n : ℕ) (hn : n % 2 = 1) :
    ((Finset.range (n + 1)).filter fun i =>
      n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1).card = (n + 1) / 8 := by
  have hset : ((Finset.range (n + 1)).filter fun i =>
        n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1)
      = (Finset.Ico ((n + 3) / 2) ((3 * n + 1) / 4 + 1)).filter fun i => i % 2 = 1 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, card_odd_Ico _ _ (by omega)]
  -- The remaining identity `((3n+1)/4+1)/2 - ((n+3)/2)/2 = (n+1)/8` mixes three
  -- nested divisions; expose the residue of `n` mod 8 so every quotient becomes
  -- linear, then `omega` closes each case.
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ n = 8 * q + r :=
    ⟨n / 8, n % 8, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r <;> omega

/-- Column-count summation: the total size of the support set. -/
theorem sum_colCard (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), colCard n i = closedForm n := by
  have key : ∀ i ∈ Finset.range (n + 1),
      colCard n i +
          (if n % 2 = 1 ∧ i % 2 = 1 ∧ n + 3 ≤ 2 * i ∧ 4 * i ≤ 3 * n + 1 then 1 else 0)
        = (n - i) + (if 2 * i ≤ n then 1 else 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [colCard]
    split_ifs <;> omega
  have hsum := Finset.sum_congr rfl key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter,
    ← Finset.card_filter] at hsum
  have hpos : ((Finset.range (n + 1)).filter fun i => 2 * i ≤ n).card = n / 2 + 1 := by
    have hp : ((Finset.range (n + 1)).filter fun i => 2 * i ≤ n)
        = Finset.range (n / 2 + 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hp, Finset.card_range]
  have hrefl : ∑ j ∈ Finset.range (n + 1), (n - j) = ∑ j ∈ Finset.range (n + 1), j := by
    simpa using Finset.sum_range_reflect (fun j => j) (n + 1)
  have h2G : (∑ i ∈ Finset.range (n + 1), i) * 2 = n * n + n := by
    have h := Finset.sum_range_id_mul_two (n + 1)
    simp only [Nat.add_sub_cancel] at h
    rw [h]; ring
  by_cases hpar : n % 2 = 0
  · have hHc := card_hole_even n hpar
    simp only [closedForm, if_pos hpar, pow_two]
    set s := n * n with hs
    omega
  · have hHc := card_hole_odd n (by omega)
    simp only [closedForm, if_neg hpar]
    have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    rw [hsq]
    set s := n * n with hs
    omega

/-- **The main count**: the conjectured support set has exactly `closedForm n`
elements. -/
theorem card_S (n : ℕ) : (S n).card = closedForm n := by
  have hmem : ∀ p ∈ S n, (fun p : ℤ × ℤ => p.1) p ∈
      (Finset.range (n + 1)).image fun i : ℕ => (n : ℤ) - 2 * (i : ℤ) := by
    rintro ⟨j, k⟩ hp
    rw [mem_S] at hp
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨((n : ℤ) - j).toNat / 2, by omega, by omega⟩
  have hinj : ∀ x ∈ Finset.range (n + 1), ∀ y ∈ Finset.range (n + 1),
      (n : ℤ) - 2 * (x : ℤ) = (n : ℤ) - 2 * (y : ℤ) → x = y := by
    intro x _ y _ h
    omega
  calc (S n).card
      = ∑ i ∈ Finset.range (n + 1),
          ((S n).filter fun p => p.1 = (n : ℤ) - 2 * (i : ℤ)).card := by
        rw [Finset.card_eq_sum_card_fiberwise hmem, Finset.sum_image hinj]
    _ = ∑ i ∈ Finset.range (n + 1), colCard n i :=
        Finset.sum_congr rfl fun i hi => card_fiber n i (Finset.mem_range.mp hi)
    _ = closedForm n := sum_colCard n

-- Numeric validation of the definition of `S` against the OEIS values.
example : (S 0).card = 1 := by decide
example : (S 1).card = 2 := by decide
example : (S 2).card = 5 := by decide
example : (S 3).card = 8 := by decide
example : (S 4).card = 13 := by decide
example : (S 9).card = 49 := by native_decide
example : (S 13).card = 97 := by native_decide

end A290268

end LeanProofs
