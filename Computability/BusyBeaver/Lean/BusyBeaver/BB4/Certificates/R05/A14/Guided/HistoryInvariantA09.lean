/-
  A direct nonhalting invariant for the R05/A14 guided leaf
  `[a07, a11, a08, a01, a09]`.

  The generic history-6x2 builder also recognizes this machine, but reducing
  that builder in the kernel is unnecessarily expensive.  After a finite
  transient, this proof exhibits a six-cell word which is pumped every 130
  transitions.  The only undefined slot, `C/mark`, is therefore unreachable.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA09

open BB3
open Sporadic
open Sporadic.State

/-- `0RB1LB_1RC0LB_0RD---_1LD1LA`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨false, Move.right, B⟩
  | A, true => some ⟨true, Move.left, B⟩
  | B, false => some ⟨true, Move.right, C⟩
  | B, true => some ⟨false, Move.left, B⟩
  | C, false => some ⟨false, Move.right, D⟩
  | C, true => none
  | D, false => some ⟨true, Move.left, D⟩
  | D, true => some ⟨true, Move.left, A⟩

/-- The word added to the right-hand tail by one pump. -/
def chunk : List Bool := [false, false, true, true, true, true]

/-- `n` copies of the pumped word, nearest cells first. -/
def tail (n : Nat) : List Bool := (List.replicate n chunk).flatten

/-- Recurrent finite-zipper phase.  The head scans the marked center cell;
seven marked cells lie immediately to its left and three to its right. -/
def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, List.replicate 7 true, true, [true, true, true] ++ tail n⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

/-- The exact constant-time pump. -/
theorem phaseF_step (n : Nat) :
    FConfig.run? machine (phaseF n) 130 = some (phaseF (n + 1)) := by
  simp [phaseF, tail, chunk, List.replicate_succ, FConfig.run?,
    FConfig.step?, FConfig.stepAction, machine]

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) 130 = some (phase (n + 1)) := by
  have hBridge := FConfig.run?_toPConfig machine (phaseF n) 130
  rw [phaseF_step] at hBridge
  exact hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

/-- The blank run reaches the recurrent phase in 123 transitions. -/
theorem seed : PTM.run? machine (PConfig.blank A false) 123 = some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 123 = some (phaseF 0) := by
    decide
  have hBridge := FConfig.run?_toPConfig machine blankF 123
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime (n : Nat) : Nat := 123 + 130 * n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => simpa [phaseTime] using seed
  | succ n ih =>
      have hTime : phaseTime (n + 1) = phaseTime n + 130 := by
        simp [phaseTime, Nat.mul_add, Nat.add_assoc]
      rw [hTime, ptm_run?_add, ih]
      exact phase_step n

theorem phaseTime_large (n : Nat) : n ≤ phaseTime n := by
  simp [phaseTime]
  omega

theorem machine_nonhalts : machine.Nonhalts A false := by
  intro steps
  exact ptm_run?_prefix (phaseTime_large steps) (reaches_phase steps)

def machineFin : PTM (Fin 4) Bool := Sporadic.toFinPTM machine

theorem machineFin_nonhalts : machineFin.Nonhalts (0 : Fin 4) false := by
  have h := (Sporadic.projects_toFin machine).nonhalts machine_nonhalts
  simpa [machineFin, Sporadic.stateToFin] using h

def leaf (table : PTable) (_cfg : Config 4) : Bool :=
  tableMatches table machineFin

theorem leaf_sound : LeafSound leaf := by
  intro table _cfg total hAgree hMatch steps
  have hEq := tableMatches_eq hMatch
  apply PTable.nonhalts_machine_of_agrees _ hAgree steps
  rw [hEq]
  exact machineFin_nonhalts

end SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA09
