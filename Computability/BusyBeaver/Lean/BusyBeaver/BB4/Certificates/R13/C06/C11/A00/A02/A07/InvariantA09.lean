/-
  A direct nonhalting invariant for the legacy R13 branch
  `[a13, a06, a11, a00, a02, a07, a09]`.

  The only unassigned slot is `B/mark`, and the run never reaches it.  After
  a finite seed, a constant-time finite-zipper macro appends two marked cells
  to the far end of the stored right zipper.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R13C06C11A00A02A07A09Invariant

open BB3
open Sporadic
open Sporadic.State

/-- `1RB0LC_0RC---_1LD0RD_0LA1LB`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨true, Move.right, B⟩
  | A, true => some ⟨false, Move.left, C⟩
  | B, false => some ⟨false, Move.right, C⟩
  | B, true => none
  | C, false => some ⟨true, Move.left, D⟩
  | C, true => some ⟨false, Move.right, D⟩
  | D, false => some ⟨false, Move.left, A⟩
  | D, true => some ⟨true, Move.left, B⟩

def chunk : List Bool := [true, true]

def tail (n : Nat) : List Bool := (List.replicate n chunk).flatten

/-- Recurrent phase: `A` scans a mark, two blanks are stored on its left,
and the right zipper is `0 111 (11)^n`, nearest cells first. -/
def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, [false, false], true,
    [false, true, true, true] ++ tail n⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

theorem phaseF_step (n : Nat) :
    FConfig.run? machine (phaseF n) 24 = some (phaseF (n + 1)) := by
  simp [phaseF, tail, chunk, List.replicate_succ, FConfig.run?,
    FConfig.step?, FConfig.stepAction, machine]

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) 24 = some (phase (n + 1)) := by
  have hBridge := FConfig.run?_toPConfig machine (phaseF n) 24
  rw [phaseF_step] at hBridge
  exact hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

theorem seed : PTM.run? machine (PConfig.blank A false) 28 =
    some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 28 = some (phaseF 0) := by
    decide
  have hBridge := FConfig.run?_toPConfig machine blankF 28
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime (n : Nat) : Nat := 28 + 24 * n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => simpa [phaseTime] using seed
  | succ n ih =>
      have hTime : phaseTime (n + 1) = phaseTime n + 24 := by
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

end SetTheory.BusyBeaver.BB4.Certificates.R13C06C11A00A02A07A09Invariant
