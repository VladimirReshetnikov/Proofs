/-
  A direct nonhalting invariant for the R05/A14 guided leaf
  `[a15, a09, a03, a02, a04]`.

  The generic history-2x2 builder recognizes this partial machine, but its
  kernel reduction is disproportionately expensive.  After 66 transitions
  from blank, the machine enters a phase which prepends a fixed seven-cell
  word to the finite zipper's left side every 65 transitions.  The old left
  tail is never inspected during a pump, so the equality is exact already at
  the finite-zipper level.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA15A09A03A02A04

open BB3
open Sporadic
open Sporadic.State

/-- `0RB---_1RC0LD_1RD0RA_1LB0LC`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨false, Move.right, B⟩
  | A, true => none
  | B, false => some ⟨true, Move.right, C⟩
  | B, true => some ⟨false, Move.left, D⟩
  | C, false => some ⟨true, Move.right, D⟩
  | C, true => some ⟨false, Move.right, A⟩
  | D, false => some ⟨true, Move.left, B⟩
  | D, true => some ⟨false, Move.left, C⟩

/-- Seven cells newly placed nearest the head during one pump. -/
def chunk : List Bool := [false, true, false, false, true, true, false]

def phaseLeft (n : Nat) : List Bool :=
  (List.replicate n chunk).flatten ++ [false, true]

def phaseRight : List Bool :=
  [false, true, false, true, false, true, false, true, false, true]

def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, phaseLeft n, false, phaseRight⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

/-- The exact constant-time pump. -/
theorem phaseF_step (n : Nat) :
    FConfig.run? machine (phaseF n) 65 = some (phaseF (n + 1)) := by
  simp [phaseF, phaseLeft, phaseRight, chunk, List.replicate_succ,
    FConfig.run?, FConfig.step?, FConfig.stepAction, machine]

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) 65 = some (phase (n + 1)) := by
  have hBridge := FConfig.run?_toPConfig machine (phaseF n) 65
  rw [phaseF_step] at hBridge
  exact hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

/-- The blank run reaches the recurrent phase in 66 transitions. -/
theorem seed : PTM.run? machine (PConfig.blank A false) 66 = some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 66 = some (phaseF 0) := by
    decide
  have hBridge := FConfig.run?_toPConfig machine blankF 66
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime (n : Nat) : Nat := 66 + 65 * n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => simpa [phaseTime] using seed
  | succ n ih =>
      have hTime : phaseTime (n + 1) = phaseTime n + 65 := by
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

end SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA15A09A03A02A04
