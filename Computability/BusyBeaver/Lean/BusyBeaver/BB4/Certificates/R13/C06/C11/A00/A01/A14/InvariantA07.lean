/-
  A direct nonhalting invariant for the legacy R13 branch
  `[a13, a06, a11, a00, a01, a14, a07]`.

  All state/bit entries except `B/mark` are assigned.  That slot is never
  reached: after a sixteen-step seed, the machine repeats a sixteen-step
  finite-zipper macro which appends the word `01` to its left tail.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R13C06C11A00A01A14A07Invariant

open BB3
open Sporadic
open Sporadic.State

/-- `1RB0LB_0RC---_1LD1RC_0LA0RD`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨true, Move.right, B⟩
  | A, true => some ⟨false, Move.left, B⟩
  | B, false => some ⟨false, Move.right, C⟩
  | B, true => none
  | C, false => some ⟨true, Move.left, D⟩
  | C, true => some ⟨true, Move.right, C⟩
  | D, false => some ⟨false, Move.left, A⟩
  | D, true => some ⟨false, Move.right, D⟩

/-- The two-cell word added to the far end of the stored left zipper. -/
def chunk : List Bool := [false, true]

def tail (n : Nat) : List Bool := (List.replicate n chunk).flatten

/-- Recurrent phase: `A` scans a blank and the left zipper is
`0001(01)^n`, nearest cells first. -/
def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, [false, false, false, true] ++ tail n, false, [false]⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

theorem phaseF_step (n : Nat) :
    FConfig.run? machine (phaseF n) 16 = some (phaseF (n + 1)) := by
  simp [phaseF, tail, chunk, List.replicate_succ, FConfig.run?,
    FConfig.step?, FConfig.stepAction, machine]

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) 16 = some (phase (n + 1)) := by
  have hBridge := FConfig.run?_toPConfig machine (phaseF n) 16
  rw [phaseF_step] at hBridge
  exact hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

theorem seed : PTM.run? machine (PConfig.blank A false) 16 =
    some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 16 = some (phaseF 0) := by
    decide
  have hBridge := FConfig.run?_toPConfig machine blankF 16
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime (n : Nat) : Nat := 16 + 16 * n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => simpa [phaseTime] using seed
  | succ n ih =>
      have hTime : phaseTime (n + 1) = phaseTime n + 16 := by
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

end SetTheory.BusyBeaver.BB4.Certificates.R13C06C11A00A01A14A07Invariant
