import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sum of integer square roots

This module records the reconstructed closed form

```text
sum_{k=1}^n floor(sqrt(k)) =
  s (n + 1) - s (s + 1) (2 s + 1) / 6,
where s = floor(sqrt(n)).
```

Lean's `Nat.sqrt k` is the natural-number floor of the real square root.
-/

open scoped BigOperators

namespace LeanProofs

/-- The reconstructed right-hand side, as a natural number. -/
def floorSqrtSumClosedForm (n : Nat) : Nat :=
  let s : Nat := Nat.sqrt n
  s * (n + 1) - s * (s + 1) * (2 * s + 1) / 6

/-- The same right-hand side in `Rat`, used internally for the algebraic proof. -/
private noncomputable def floorSqrtSumClosedFormRat (n : Nat) : Rat :=
  let s : Rat := Nat.sqrt n
  s * (n + 1 : Rat) - s * (s + 1) * (2 * s + 1) / 6

private lemma floorSqrtSumClosedFormRat_step_same
    (n q : Nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (n + 1) = q) :
    floorSqrtSumClosedFormRat (n + 1) = floorSqrtSumClosedFormRat n + (q : Rat) := by
  unfold floorSqrtSumClosedFormRat
  simp only [hq, hs, Nat.cast_add, Nat.cast_one]
  ring

private lemma floorSqrtSumClosedFormRat_step_jump
    (n q : Nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (n + 1) = q + 1)
    (hn : n + 1 = (q + 1) ^ 2) :
    floorSqrtSumClosedFormRat (n + 1) =
      floorSqrtSumClosedFormRat n + ((q + 1 : Nat) : Rat) := by
  have hn' : n = (q + 1) ^ 2 - 1 := by
    rw [← hn]
    simp
  unfold floorSqrtSumClosedFormRat
  simp only [hq, hs, Nat.cast_add, Nat.cast_one]
  rw [hn']
  norm_num
  ring

private lemma sqrt_succ_eq_self_or_succ (n : Nat) :
    Nat.sqrt (n + 1) = Nat.sqrt n ∨ Nat.sqrt (n + 1) = Nat.sqrt n + 1 := by
  let q := Nat.sqrt n
  let r := Nat.sqrt (n + 1)
  have hge : q ≤ r := by
    dsimp [q, r]
    exact Nat.sqrt_le_sqrt (Nat.le_succ n)
  have hle : r ≤ q + 1 := by
    dsimp [q, r]
    exact Nat.sqrt_succ_le_succ_sqrt n
  by_cases hlt : r < q + 1
  · have hrle : r ≤ q := Nat.lt_succ_iff.mp hlt
    exact Or.inl (by
      dsimp [q, r] at *
      exact le_antisymm hrle hge)
  · have hqle : q + 1 ≤ r := Nat.le_of_not_gt hlt
    exact Or.inr (by
      dsimp [q, r] at *
      exact le_antisymm hle hqle)

private lemma sqrt_jump_square
    (n q : Nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (n + 1) = q + 1) :
    n + 1 = (q + 1) ^ 2 := by
  apply le_antisymm
  · rw [Nat.pow_two]
    simpa [hq, Nat.pow_two] using Nat.lt_succ_sqrt n
  · exact Nat.le_sqrt'.mp (by simp [hs] : q + 1 ≤ Nat.sqrt (n + 1))

private lemma six_dvd_sqrt_sum_numer (s : Nat) :
    6 ∣ s * (s + 1) * (2 * s + 1) := by
  induction s with
  | zero =>
      norm_num
  | succ s ih =>
      have hstep : (s + 1) * (s + 1 + 1) * (2 * (s + 1) + 1) =
          s * (s + 1) * (2 * s + 1) + 6 * ((s + 1) * (s + 1)) := by
        ring
      rw [hstep]
      exact Nat.dvd_add ih (dvd_mul_right 6 ((s + 1) * (s + 1)))

private lemma floorSqrtSumClosedForm_subtrahend_le (n : Nat) :
    Nat.sqrt n * (Nat.sqrt n + 1) * (2 * Nat.sqrt n + 1) / 6 ≤
      Nat.sqrt n * (n + 1) := by
  let s := Nat.sqrt n
  have hs : s * s ≤ n := by
    dsimp [s]
    exact Nat.sqrt_le n
  have hpoly : (s + 1) * (2 * s + 1) ≤ 6 * (s * s + 1) := by
    apply Int.ofNat_le.mp
    push_cast
    nlinarith [sq_nonneg ((s : Int) - 1)]
  have hs' : s * s + 1 ≤ n + 1 := Nat.succ_le_succ hs
  apply Nat.div_le_of_le_mul
  calc
    s * (s + 1) * (2 * s + 1) = s * ((s + 1) * (2 * s + 1)) := by ring
    _ ≤ s * (6 * (s * s + 1)) := Nat.mul_le_mul_left s hpoly
    _ ≤ s * (6 * (n + 1)) := Nat.mul_le_mul_left s (Nat.mul_le_mul_left 6 hs')
    _ = 6 * (s * (n + 1)) := by ring

private lemma floorSqrtSumClosedForm_cast (n : Nat) :
    (floorSqrtSumClosedForm n : Rat) = floorSqrtSumClosedFormRat n := by
  dsimp [floorSqrtSumClosedForm, floorSqrtSumClosedFormRat]
  rw [Nat.cast_sub (floorSqrtSumClosedForm_subtrahend_le n)]
  rw [Nat.cast_div_charZero (six_dvd_sqrt_sum_numer (Nat.sqrt n))]
  push_cast
  ring

/--
For `s = floor(sqrt(n))`,

`sum_{k=1}^n floor(sqrt(k)) = s (n + 1) - s (s + 1) (2 s + 1) / 6`.

This private lemma keeps the algebra in `Rat`; the public theorem below states the
same identity in `Nat`.
-/
private theorem sum_floor_sqrt_eq_closedForm_rat (n : Nat) :
    ((∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) : Rat) =
      floorSqrtSumClosedFormRat n := by
  induction n with
  | zero =>
      simp [floorSqrtSumClosedFormRat]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos n)]
      simp only [Nat.cast_add]
      rw [ih]
      rcases sqrt_succ_eq_self_or_succ n with hs | hs
      · rw [floorSqrtSumClosedFormRat_step_same n (Nat.sqrt n) rfl hs]
        simp [hs]
      · have hn := sqrt_jump_square n (Nat.sqrt n) rfl hs
        rw [floorSqrtSumClosedFormRat_step_jump n (Nat.sqrt n) rfl hs hn]
        simp [hs]

/-- The reconstructed formula, stated as an equality of natural numbers. -/
theorem sum_floor_sqrt_eq_closedForm (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) =
      floorSqrtSumClosedForm n := by
  apply Nat.cast_injective (R := Rat)
  rw [sum_floor_sqrt_eq_closedForm_rat, floorSqrtSumClosedForm_cast]

/-- The reconstructed formula, expanded without the named right-hand side. -/
theorem sum_floor_sqrt_eq (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) =
      Nat.sqrt n * (n + 1)
        - Nat.sqrt n * (Nat.sqrt n + 1)
          * (2 * Nat.sqrt n + 1) / 6 := by
  simpa [floorSqrtSumClosedForm] using sum_floor_sqrt_eq_closedForm n

end LeanProofs
