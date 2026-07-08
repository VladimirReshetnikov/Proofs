/-
  BusyBeaverKnownValues.lean

  Concrete small-state busy-beaver machines for Rado's score function.

  The unconditional theorems in this file prove the witnessed lower-bound half
  of the requested OEIS A028444 prefix in the local Rado machine model: the
  standard 1-, 2-, 3-, and 4-state champions halt with scores 1, 4, 6, and 13.

  The exact upper-bound proofs for the later values are enumeration/certificate
  developments.  We expose a Lean certificate interface for the first four
  upper bounds and prove that any such certificates imply the advertised
  A028444 values for any function satisfying `IsSigma`.
-/

import SetTheory.BusyBeaver

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace KnownValues

/-! ## Transition-table helpers -/

/-- Concrete state index helper for small transition tables. -/
def state {states : Nat} (k : Nat) (h : k < states := by decide) : Fin states :=
  ⟨k, h⟩

/-- A halting transition.  The move component is kept because the Rado action
type records it even when the next state is `none`. -/
def halt {states : Nat} (write : Bool) (move : Move) : Action states where
  write := write
  move := move
  next := none

/-- A non-halting transition to another operational state. -/
def go {states : Nat} (write : Bool) (move : Move) (next : Fin states) : Action states where
  write := write
  move := move
  next := some next

/-! ## Standard score champions -/

/--
The 1-state score champion, in table notation:

```text
A0 -> 1RH
```
-/
def sigma1Champion : Machine 1 where
  transition q bit :=
    match q.val, bit with
    | _, false => halt true Move.right
    | _, true => halt false Move.right

/--
The 2-state score champion:

```text
A0 -> 1RB    A1 -> 1LB
B0 -> 1LA    B1 -> 1RH
```
-/
def sigma2Champion : Machine 2 where
  transition q bit :=
    match q.val, bit with
    | 0, false => go true Move.right (state 1)
    | 0, true => go true Move.left (state 1)
    | 1, false => go true Move.left (state 0)
    | _, true => halt true Move.right
    | _, _ => halt false Move.right

/--
The 3-state score champion:

```text
A0 -> 1RB    A1 -> 1RH
B0 -> 0RC    B1 -> 1RB
C0 -> 1LC    C1 -> 1LA
```
-/
def sigma3Champion : Machine 3 where
  transition q bit :=
    match q.val, bit with
    | 0, false => go true Move.right (state 1)
    | 0, true => halt true Move.right
    | 1, false => go false Move.right (state 2)
    | 1, true => go true Move.right (state 1)
    | 2, false => go true Move.left (state 2)
    | _, true => go true Move.left (state 0)
    | _, _ => halt false Move.right

/--
The 4-state score champion:

```text
A0 -> 1RB    A1 -> 1LB
B0 -> 1LA    B1 -> 0LC
C0 -> 1RH    C1 -> 1LD
D0 -> 1RD    D1 -> 0RA
```
-/
def sigma4Champion : Machine 4 where
  transition q bit :=
    match q.val, bit with
    | 0, false => go true Move.right (state 1)
    | 0, true => go true Move.left (state 1)
    | 1, false => go true Move.left (state 0)
    | 1, true => go false Move.left (state 2)
    | 2, false => halt true Move.right
    | 2, true => go true Move.left (state 3)
    | 3, false => go true Move.right (state 3)
    | _, true => go false Move.right (state 0)
    | _, _ => halt false Move.right

/-! ## Checked lower-bound witnesses -/

theorem sigma1Champion_haltsWithScore : sigma1Champion.HaltsWithScore 1 := by
  refine ⟨1, ?_, ?_⟩ <;> decide

theorem sigma2Champion_haltsWithScore : sigma2Champion.HaltsWithScore 4 := by
  refine ⟨6, ?_, ?_⟩ <;> decide

theorem sigma3Champion_haltsWithScore : sigma3Champion.HaltsWithScore 6 := by
  refine ⟨14, ?_, ?_⟩ <;> decide

theorem sigma4Champion_haltsWithScore : sigma4Champion.HaltsWithScore 13 := by
  refine ⟨107, ?_, ?_⟩ <;> decide

theorem attainableScore_one_one : AttainableScore 1 1 :=
  ⟨sigma1Champion, sigma1Champion_haltsWithScore⟩

theorem attainableScore_two_four : AttainableScore 2 4 :=
  ⟨sigma2Champion, sigma2Champion_haltsWithScore⟩

theorem attainableScore_three_six : AttainableScore 3 6 :=
  ⟨sigma3Champion, sigma3Champion_haltsWithScore⟩

theorem attainableScore_four_thirteen : AttainableScore 4 13 :=
  ⟨sigma4Champion, sigma4Champion_haltsWithScore⟩

theorem one_le_sigma_one {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    1 ≤ Sigma 1 :=
  hSigma.upper attainableScore_one_one

theorem four_le_sigma_two {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    4 ≤ Sigma 2 :=
  hSigma.upper attainableScore_two_four

theorem six_le_sigma_three {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    6 ≤ Sigma 3 :=
  hSigma.upper attainableScore_three_six

theorem thirteen_le_sigma_four {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    13 ≤ Sigma 4 :=
  hSigma.upper attainableScore_four_thirteen

/-- The machine-checked lower-bound part of the requested A028444 prefix. -/
theorem a028444_prefix_lower_bounds_through_four {Sigma : Nat -> Nat}
    (hSigma : IsSigma Sigma) :
    1 ≤ Sigma 1 ∧ 4 ≤ Sigma 2 ∧ 6 ≤ Sigma 3 ∧ 13 ≤ Sigma 4 := by
  exact ⟨one_le_sigma_one hSigma,
    four_le_sigma_two hSigma,
    six_le_sigma_three hSigma,
    thirteen_le_sigma_four hSigma⟩

/-! ## The 1-state upper bound -/

private theorem fin_one_eq_zero (q : Fin 1) : q = 0 := by
  cases q with
  | mk val isLt =>
      have h : val = 0 := by omega
      subst val
      rfl

private theorem oneState_zero_halts_run_succ
    {M : Machine 1}
    (hnext : (M.transition (0 : Fin 1) false).next = none) :
    ∀ t, (M.run (t + 1)).state = none ∧ (M.run (t + 1)).tape.length ≤ 1
  | 0 => by
      constructor
      · simp [Machine.run, Machine.step, initial, startState, Tape.read, hnext]
      · cases hwrite : (M.transition (0 : Fin 1) false).write <;>
          simp [Machine.run, Machine.step, initial, startState, Tape.read, Tape.write,
            hnext, hwrite]
  | t + 1 => by
      have ih := oneState_zero_halts_run_succ (M := M) hnext t
      constructor
      · change (M.step (M.run (t + 1))).state = none
        simp [Machine.step, ih.1]
      · change (M.step (M.run (t + 1))).tape.length ≤ 1
        simpa [Machine.step, ih.1] using ih.2

private theorem oneState_zero_continue_right_run
    {M : Machine 1}
    (hnext : (M.transition (0 : Fin 1) false).next = some 0)
    (hmove : (M.transition (0 : Fin 1) false).move = Move.right) :
    ∀ t, (M.run t).state = some (0 : Fin 1) ∧
      (M.run t).head = (t : Int) ∧
      ∀ q, q ∈ (M.run t).tape -> q < (M.run t).head
  | 0 => by
      constructor
      · rfl
      constructor
      · rfl
      · simp [Machine.run, initial]
  | t + 1 => by
      have ih := oneState_zero_continue_right_run (M := M) hnext hmove t
      have hnot : (M.run t).head ∉ (M.run t).tape := by
        intro hmem
        have hlt := ih.2.2 (M.run t).head hmem
        omega
      have hread : Tape.read (M.run t).tape (M.run t).head = false := by
        simp [Tape.read, hnot]
      have hreadNat : Tape.read (M.run t).tape (t : Int) = false := by
        simpa [ih.2.1] using hread
      constructor
      · simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hnext]
      constructor
      · simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hmove, Move.apply]
      · intro q hq
        have hq' : q ∈ Tape.write (M.run t).tape (M.run t).head
            (M.transition (0 : Fin 1) false).write := by
          simpa [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat] using hq
        have hnewhead : (M.run (t + 1)).head = (M.run t).head + 1 := by
          simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hmove, Move.apply]
        cases hwrite : (M.transition (0 : Fin 1) false).write
        · have hqOld : q ∈ (M.run t).tape := by
            simp [Tape.write, hwrite] at hq'
            exact hq'.1
          have hlt := ih.2.2 q hqOld
          omega
        · have hcases : q = (M.run t).head ∨ q ∈ (M.run t).tape := by
            simp [Tape.write, hwrite, hnot] at hq'
            exact hq'
          cases hcases with
          | inl hqhead => omega
          | inr hqOld =>
              have hlt := ih.2.2 q hqOld
              omega

private theorem oneState_zero_continue_left_run
    {M : Machine 1}
    (hnext : (M.transition (0 : Fin 1) false).next = some 0)
    (hmove : (M.transition (0 : Fin 1) false).move = Move.left) :
    ∀ t, (M.run t).state = some (0 : Fin 1) ∧
      (M.run t).head = -((t : Int)) ∧
      ∀ q, q ∈ (M.run t).tape -> (M.run t).head < q
  | 0 => by
      constructor
      · rfl
      constructor
      · rfl
      · simp [Machine.run, initial]
  | t + 1 => by
      have ih := oneState_zero_continue_left_run (M := M) hnext hmove t
      have hnot : (M.run t).head ∉ (M.run t).tape := by
        intro hmem
        have hlt := ih.2.2 (M.run t).head hmem
        omega
      have hread : Tape.read (M.run t).tape (M.run t).head = false := by
        simp [Tape.read, hnot]
      have hreadNat : Tape.read (M.run t).tape (-((t : Int))) = false := by
        simpa [ih.2.1] using hread
      constructor
      · simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hnext]
      constructor
      · simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hmove, Move.apply]
        omega
      · intro q hq
        have hq' : q ∈ Tape.write (M.run t).tape (M.run t).head
            (M.transition (0 : Fin 1) false).write := by
          simpa [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat] using hq
        have hnewhead : (M.run (t + 1)).head = (M.run t).head - 1 := by
          simp [Machine.run, Machine.step, ih.1, ih.2.1, hreadNat, hmove, Move.apply]
        cases hwrite : (M.transition (0 : Fin 1) false).write
        · have hqOld : q ∈ (M.run t).tape := by
            simp [Tape.write, hwrite] at hq'
            exact hq'.1
          have hlt := ih.2.2 q hqOld
          omega
        · have hcases : q = (M.run t).head ∨ q ∈ (M.run t).tape := by
            simp [Tape.write, hwrite, hnot] at hq'
            exact hq'
          cases hcases with
          | inl hqhead => omega
          | inr hqOld =>
              have hlt := ih.2.2 q hqOld
              omega

private theorem oneState_zero_continue_never_halts
    {M : Machine 1}
    (hnext : (M.transition (0 : Fin 1) false).next = some 0) :
    ∀ t, (M.run t).state = some (0 : Fin 1) := by
  intro t
  cases hmove : (M.transition (0 : Fin 1) false).move with
  | left => exact (oneState_zero_continue_left_run (M := M) hnext hmove t).1
  | right => exact (oneState_zero_continue_right_run (M := M) hnext hmove t).1

theorem upperBound_one : ∀ {score : Nat}, AttainableScore 1 score -> score ≤ 1 := by
  intro score h
  rcases h with ⟨M, t, hState, hScore⟩
  cases hnext : (M.transition (0 : Fin 1) false).next with
  | none =>
      cases t with
      | zero =>
          simp [Machine.run, initial, startState] at hState
      | succ k =>
          have hle := (oneState_zero_halts_run_succ (M := M) hnext k).2
          omega
  | some q =>
      have hq : q = (0 : Fin 1) := fin_one_eq_zero q
      subst q
      have hnever := oneState_zero_continue_never_halts (M := M) hnext t
      rw [hnever] at hState
      contradiction

/-! ## Exact values from explicit certificates -/

/-- A score is the exact busy-beaver score for a state count in the local
machine model. -/
def ExactScore (states score : Nat) : Prop :=
  AttainableScore states score ∧
    ∀ {other : Nat}, AttainableScore states other -> other ≤ score

theorem ExactScore.sigma_eq {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {states score : Nat} (hpos : 0 < states) (h : ExactScore states score) :
    Sigma states = score := by
  apply Nat.le_antisymm
  · exact h.2 (hSigma.attained hpos)
  · exact hSigma.upper h.1

theorem exactScore_one : ExactScore 1 1 :=
  ⟨attainableScore_one_one, upperBound_one⟩

theorem sigma_one_eq_one {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    Sigma 1 = 1 :=
  ExactScore.sigma_eq hSigma (by decide) exactScore_one

/--
Upper-bound certificate interface for the first four positive A028444 terms.

For example, the `four` field means that every halting 4-state machine in the
local Rado model scores at most 13.  This is the expensive part of the classical
busy-beaver value proofs.
-/
structure A028444UpperBoundsThroughFour : Prop where
  one : ∀ {score : Nat}, AttainableScore 1 score -> score ≤ 1
  two : ∀ {score : Nat}, AttainableScore 2 score -> score ≤ 4
  three : ∀ {score : Nat}, AttainableScore 3 score -> score ≤ 6
  four : ∀ {score : Nat}, AttainableScore 4 score -> score ≤ 13

/-- The remaining upper-bound obligations after the 1-state case has been
proved directly. -/
structure A028444UpperBoundsTwoThroughFour : Prop where
  two : ∀ {score : Nat}, AttainableScore 2 score -> score ≤ 4
  three : ∀ {score : Nat}, AttainableScore 3 score -> score ≤ 6
  four : ∀ {score : Nat}, AttainableScore 4 score -> score ≤ 13

theorem A028444UpperBoundsThroughFour.of_twoThroughFour
    (hUpper : A028444UpperBoundsTwoThroughFour) :
    A028444UpperBoundsThroughFour where
  one := upperBound_one
  two := hUpper.two
  three := hUpper.three
  four := hUpper.four

theorem exactScore_one_of_upperBounds (_hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 1 1 :=
  exactScore_one

theorem exactScore_two_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 2 4 :=
  ⟨attainableScore_two_four, fun h => hUpper.two h⟩

theorem exactScore_three_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 3 6 :=
  ⟨attainableScore_three_six, fun h => hUpper.three h⟩

theorem exactScore_four_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 4 13 :=
  ⟨attainableScore_four_thirteen, fun h => hUpper.four h⟩

theorem exactScore_two_of_remainingUpperBounds
    (hUpper : A028444UpperBoundsTwoThroughFour) :
    ExactScore 2 4 :=
  exactScore_two_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)

theorem exactScore_three_of_remainingUpperBounds
    (hUpper : A028444UpperBoundsTwoThroughFour) :
    ExactScore 3 6 :=
  exactScore_three_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)

theorem exactScore_four_of_remainingUpperBounds
    (hUpper : A028444UpperBoundsTwoThroughFour) :
    ExactScore 4 13 :=
  exactScore_four_of_upperBounds
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)

/--
Once the usual upper-bound certificates are supplied, any `IsSigma` function
has the requested positive A028444 prefix through four states.
-/
theorem a028444_values_through_four_from_upperBounds {Sigma : Nat -> Nat}
    (hSigma : IsSigma Sigma) (hUpper : A028444UpperBoundsThroughFour) :
    Sigma 1 = 1 ∧ Sigma 2 = 4 ∧ Sigma 3 = 6 ∧ Sigma 4 = 13 := by
  constructor
  · exact sigma_one_eq_one hSigma
  constructor
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_two_of_upperBounds hUpper)
  constructor
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_three_of_upperBounds hUpper)
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_four_of_upperBounds hUpper)

/--
Once the remaining 2-, 3-, and 4-state upper-bound certificates are supplied,
any `IsSigma` function has the requested positive A028444 prefix through four
states.  The 1-state upper bound is proved directly above.
-/
theorem a028444_values_through_four_from_remainingUpperBounds {Sigma : Nat -> Nat}
    (hSigma : IsSigma Sigma) (hUpper : A028444UpperBoundsTwoThroughFour) :
    Sigma 1 = 1 ∧ Sigma 2 = 4 ∧ Sigma 3 = 6 ∧ Sigma 4 = 13 := by
  exact a028444_values_through_four_from_upperBounds hSigma
    (A028444UpperBoundsThroughFour.of_twoThroughFour hUpper)

end KnownValues
end BusyBeaver
end SetTheory
