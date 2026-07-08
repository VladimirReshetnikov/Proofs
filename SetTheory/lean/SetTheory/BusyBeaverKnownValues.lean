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

theorem exactScore_one_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 1 1 :=
  ⟨attainableScore_one_one, fun h => hUpper.one h⟩

theorem exactScore_two_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 2 4 :=
  ⟨attainableScore_two_four, fun h => hUpper.two h⟩

theorem exactScore_three_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 3 6 :=
  ⟨attainableScore_three_six, fun h => hUpper.three h⟩

theorem exactScore_four_of_upperBounds (hUpper : A028444UpperBoundsThroughFour) :
    ExactScore 4 13 :=
  ⟨attainableScore_four_thirteen, fun h => hUpper.four h⟩

/--
Once the usual upper-bound certificates are supplied, any `IsSigma` function
has the requested positive A028444 prefix through four states.
-/
theorem a028444_values_through_four_from_upperBounds {Sigma : Nat -> Nat}
    (hSigma : IsSigma Sigma) (hUpper : A028444UpperBoundsThroughFour) :
    Sigma 1 = 1 ∧ Sigma 2 = 4 ∧ Sigma 3 = 6 ∧ Sigma 4 = 13 := by
  constructor
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_one_of_upperBounds hUpper)
  constructor
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_two_of_upperBounds hUpper)
  constructor
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_three_of_upperBounds hUpper)
  · exact ExactScore.sigma_eq hSigma (by decide) (exactScore_four_of_upperBounds hUpper)

end KnownValues
end BusyBeaver
end SetTheory
