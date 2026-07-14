/-
  Standalone fallback invariant for the R05/A14 guided leaf
  `[a08, a10, a13, a03, a08]`.

  The current certificate can use the existing history-4x2 hint without
  changing the trusted Guided verifier.  This module records the simpler
  direct semantics discovered independently: after 33 transitions, every
  17-transition cycle inserts one more blank into a growing right-hand gap.
  It is intentionally not imported by `Guided.lean` unless the generic pass
  later proves too expensive in the kernel.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA08A10A13A03A08

open BB3
open Sporadic
open Sporadic.State

/-- `0RB1LC_1RC1RB_1LA0LD_---1LA`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨false, Move.right, B⟩
  | A, true => some ⟨true, Move.left, C⟩
  | B, false => some ⟨true, Move.right, C⟩
  | B, true => some ⟨true, Move.right, B⟩
  | C, false => some ⟨true, Move.left, A⟩
  | C, true => some ⟨false, Move.left, D⟩
  | D, false => none
  | D, true => some ⟨true, Move.left, A⟩

def phaseRight (n : Nat) : List Bool :=
  [true, true, true, false, true] ++
    List.replicate (n + 1) false ++ [true]

def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, [], false, phaseRight n⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

/-- One cycle grows the blank gap by one cell. -/
theorem phaseF_step (n : Nat) :
    FConfig.run? machine (phaseF n) 17 = some (phaseF (n + 1)) := by
  simp [phaseF, phaseRight, List.replicate_succ, FConfig.run?,
    FConfig.step?, FConfig.stepAction, machine]

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) 17 = some (phase (n + 1)) := by
  have hBridge := FConfig.run?_toPConfig machine (phaseF n) 17
  rw [phaseF_step] at hBridge
  exact hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

theorem seed : PTM.run? machine (PConfig.blank A false) 33 = some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 33 = some (phaseF 0) := by
    decide
  have hBridge := FConfig.run?_toPConfig machine blankF 33
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime (n : Nat) : Nat := 33 + 17 * n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => simpa [phaseTime] using seed
  | succ n ih =>
      have hTime : phaseTime (n + 1) = phaseTime n + 17 := by
        simp [phaseTime, Nat.mul_add, Nat.add_assoc]
      rw [hTime, ptm_run?_add, ih]
      exact phase_step n

theorem phaseTime_large (n : Nat) : n ≤ phaseTime n := by
  unfold phaseTime
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

end SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA08A10A13A03A08
