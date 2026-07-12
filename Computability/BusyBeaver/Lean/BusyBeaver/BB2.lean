/-
  BusyBeaverBB2.lean

  Facade assembling the six independently kernel-checked left-moving BB(2)
  table-certificate blocks, plus reflection, into the exact score theorem.
-/

import BusyBeaver.BB2.FalseLeftHalt
import BusyBeaver.BB2.FalseLeftA
import BusyBeaver.BB2.FalseLeftB
import BusyBeaver.BB2.TrueLeftHalt
import BusyBeaver.BB2.TrueLeftA
import BusyBeaver.BB2.TrueLeftB

namespace SetTheory
namespace BusyBeaver
namespace BB2

open KnownValues

private theorem left_tablesCheckFor_eq_true (write : Bool)
    (next : Option (Fin 2)) :
    tablesCheckFor
      ({ write := write, move := Move.left, next := next } : Action 2) = true := by
  cases write
  · cases next with
    | none => exact Certificate.false_left_halt
    | some q =>
        fin_cases q
        · exact Certificate.false_left_a
        · exact Certificate.false_left_b
  · cases next with
    | none => exact Certificate.true_left_halt
    | some q =>
        fin_cases q
        · exact Certificate.true_left_a
        · exact Certificate.true_left_b

private theorem certified_of_tablesCheckFor {a0 : Action 2}
    (h : tablesCheckFor a0 = true) (a1 b0 b1 : Action 2) :
    CertifiedSafe (tableMachine a0 a1 b0 b1) := by
  simp only [tablesCheckFor, tablesCheckFor2, List.all_eq_true] at h
  have hDecide := h a1 (action_mem_actionList a1)
    b0 (action_mem_actionList b0) b1 (action_mem_actionList b1)
  exact of_decide_eq_true hDecide

private theorem left_table_certified (write : Bool) (next : Option (Fin 2))
    (a1 b0 b1 : Action 2) :
    CertifiedSafe
      (tableMachine
        ({ write := write, move := Move.left, next := next } : Action 2)
        a1 b0 b1) :=
  certified_of_tablesCheckFor (left_tablesCheckFor_eq_true write next) a1 b0 b1

/-- Kernel-checked score coverage of all `12^4 = 20,736` two-state tables.
Right-moving first actions are reduced to the checked left-moving half by tape
reflection. -/
theorem all_tables_score_le_four (a0 a1 b0 b1 : Action 2) {score : Nat}
    (hHalt : (tableMachine a0 a1 b0 b1).HaltsWithScore score) : score ≤ 4 := by
  rcases a0 with ⟨write, move, next⟩
  cases move with
  | left =>
      exact (left_table_certified write next a1 b0 b1).score_le_four hHalt
  | right =>
      have hReflected :
          (tableMachine
            ({ write := write, move := Move.left, next := next } : Action 2)
            (reflectAction a1) (reflectAction b0) (reflectAction b1)).HaltsWithScore
            score := by
        simpa [reflectAction, reflectMove] using (reflect_haltsWithScore hHalt)
      exact
        (left_table_certified write next (reflectAction a1)
          (reflectAction b0) (reflectAction b1)).score_le_four hReflected

/-- No halting two-state machine leaves more than four `1`s. -/
theorem upperBound_two {score : Nat} : AttainableScore 2 score -> score ≤ 4 := by
  rintro ⟨M, hHalt⟩
  rw [machine_eq_tableMachine M] at hHalt
  exact all_tables_score_le_four _ _ _ _ hHalt

theorem exactScore_two : KnownValues.ExactScore 2 4 := by
  constructor
  · exact KnownValues.attainableScore_two_four
  · intro other hScore
    exact upperBound_two hScore

/-- The second value of OEIS A028444 in the repository's Rado-machine model. -/
theorem sigma_two_eq_four {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma) :
    Sigma 2 = 4 :=
  KnownValues.ExactScore.sigma_eq hSigma (by decide) exactScore_two

end BB2
end BusyBeaver
end SetTheory
