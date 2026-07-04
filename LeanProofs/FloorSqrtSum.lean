import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt
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

/-- The reconstructed right-hand side, as a rational number. -/
noncomputable def floorSqrtSumClosedForm (n : Nat) : Rat :=
  let s : Rat := Nat.sqrt n
  s * (n + 1 : Rat) - s * (s + 1) * (2 * s + 1) / 6

private lemma floorSqrtSumClosedForm_step_same
    (n q : Nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (n + 1) = q) :
    floorSqrtSumClosedForm (n + 1) = floorSqrtSumClosedForm n + (q : Rat) := by
  unfold floorSqrtSumClosedForm
  simp only [hq, hs, Nat.cast_add, Nat.cast_one]
  ring

private lemma floorSqrtSumClosedForm_step_jump
    (n q : Nat) (hq : Nat.sqrt n = q) (hs : Nat.sqrt (n + 1) = q + 1)
    (hn : n + 1 = (q + 1) ^ 2) :
    floorSqrtSumClosedForm (n + 1) =
      floorSqrtSumClosedForm n + ((q + 1 : Nat) : Rat) := by
  have hn' : n = (q + 1) ^ 2 - 1 := by
    rw [← hn]
    simp
  unfold floorSqrtSumClosedForm
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

/--
For `s = floor(sqrt(n))`,

`sum_{k=1}^n floor(sqrt(k)) = s (n + 1) - s (s + 1) (2 s + 1) / 6`.

The equality is stated in `Rat` so that the displayed division by `6` is literal.
-/
theorem sum_floor_sqrt_eq_closedForm (n : Nat) :
    ((∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) : Rat) =
      floorSqrtSumClosedForm n := by
  induction n with
  | zero =>
      simp [floorSqrtSumClosedForm]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (Nat.succ_pos n)]
      simp only [Nat.cast_add]
      rw [ih]
      rcases sqrt_succ_eq_self_or_succ n with hs | hs
      · rw [floorSqrtSumClosedForm_step_same n (Nat.sqrt n) rfl hs]
        simp [hs]
      · have hn := sqrt_jump_square n (Nat.sqrt n) rfl hs
        rw [floorSqrtSumClosedForm_step_jump n (Nat.sqrt n) rfl hs hn]
        simp [hs]

/-- The reconstructed formula, expanded without the named right-hand side. -/
theorem sum_floor_sqrt_eq (n : Nat) :
    ((∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) : Rat) =
      (Nat.sqrt n : Rat) * (n + 1 : Rat)
        - (Nat.sqrt n : Rat) * ((Nat.sqrt n : Rat) + 1)
          * (2 * (Nat.sqrt n : Rat) + 1) / 6 := by
  simpa [floorSqrtSumClosedForm] using sum_floor_sqrt_eq_closedForm n

end LeanProofs
