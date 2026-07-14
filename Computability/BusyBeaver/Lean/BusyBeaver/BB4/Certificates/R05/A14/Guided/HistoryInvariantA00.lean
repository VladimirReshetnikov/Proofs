/-
  A direct nonhalting invariant for the R05/A14 guided leaf
  `[a07, a11, a08, a01, a00]`.

  At suitable boundaries the machine is in state C, scanning a blank, with a
  nonempty solid marked block immediately to its left.  A tiny side condition
  on the first two right-hand cells excludes the sole bad boundary (a block of
  length two followed by a blank).  Three exact macros preserve that condition
  forever.  This replaces a much more expensive generic history-6x2 build.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA00

open BB3
open Sporadic
open Sporadic.State

/-- `0RB0LA_1RC0LB_0RD---_1LD1LA`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨false, Move.right, B⟩
  | A, true => some ⟨false, Move.left, A⟩
  | B, false => some ⟨true, Move.right, C⟩
  | B, true => some ⟨false, Move.left, B⟩
  | C, false => some ⟨false, Move.right, D⟩
  | C, true => none
  | D, false => some ⟨true, Move.left, D⟩
  | D, true => some ⟨true, Move.left, A⟩

private theorem replicate_bit_succ (bit : Bool) (n : Nat) :
    List.replicate (n + 1) bit = bit :: List.replicate n bit := by
  simp [List.replicate_succ]

private theorem replicate_false_snoc (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail =
      List.replicate (n + 1) false ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [replicate_bit_succ, replicate_bit_succ]
      simp only [List.cons_append, List.cons.injEq]
      exact ⟨True.intro, ih⟩

private theorem replicate_two_succ (bit : Bool) (n : Nat) :
    List.replicate (n + 2) bit = bit :: bit :: List.replicate n bit := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    replicate_bit_succ, replicate_bit_succ]

/-- `A/mark` clears the current cell and `n` marked cells to its left,
stopping on the first blank. -/
theorem scan_A_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine
      ⟨A, List.replicate n true ++ false :: left, true, right⟩ (n + 1) =
    some ⟨A, left, false, List.replicate (n + 1) false ++ right⟩ := by
  induction n generalizing right with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine]
  | succ n ih =>
      rw [replicate_bit_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine
          ⟨A, true :: (List.replicate n true ++ false :: left),
            true, right⟩ 1 =
          some ⟨A, List.replicate n true ++ false :: left,
            true, false :: right⟩ := by
        rfl
      have hRest := ih (false :: right)
      have hAll := FConfig.run?_compose hFirst hRest
      have hTime : 1 + (n + 1) = n + 1 + 1 := by omega
      have hRight :
          List.replicate (n + 1) false ++ false :: right =
            List.replicate (1 + (n + 1)) false ++ right := by
        rw [show 1 + (n + 1) = n + 1 + 1 by omega]
        exact replicate_false_snoc (n + 1) right
      rw [← hTime, hAll]
      exact congrArg some (congrArg
        (fun xs => (FConfig.mk A left false xs : FConfig Sporadic.State))
        hRight)

/-- Boundary with a solid block of `ell` marks on the left.  The explicit
trailing blank on that side makes the exact finite macros compose cleanly. -/
def phaseF (ell : Nat) (right : List Bool) : FConfig Sporadic.State :=
  ⟨C, List.replicate ell true ++ [false], false, right⟩

def phase (ell : Nat) (right : List Bool) : PConfig Sporadic.State Bool :=
  (phaseF ell right).toPConfig

/-- Crossing a marked right cell grows the left block by one. -/
theorem marked_macro (ell : Nat) (right : List Bool) :
    FConfig.run? machine (phaseF ell (true :: right)) 5 =
      some (phaseF (ell + 1) right) := by
  simp [phaseF, FConfig.run?, FConfig.step?, FConfig.stepAction, machine,
    replicate_bit_succ]

/-- A blank after a one-cell block emits two marks. -/
theorem short_blank_macro (right : List Bool) :
    FConfig.run? machine (phaseF 1 (false :: right)) 7 =
      some ⟨C, [true], false, true :: true :: right⟩ := by
  simp [phaseF, FConfig.run?, FConfig.step?, FConfig.stepAction, machine]

theorem short_result_to_phase (right : List Bool) :
    (FConfig.mk C [true] false (true :: true :: right) :
      FConfig Sporadic.State).toPConfig =
      phase 1 (true :: true :: right) := by
  apply PConfig.ext
  · rfl
  · intro i
    have hPad := congrFun (Sporadic.pad_append_false [true]) i
    simpa [phase, phaseF, FConfig.toPConfig] using hPad.symm
  · rfl
  · intro i
    rfl

/-- A blank after a block of length `n+3` performs the long left sweep. -/
theorem long_blank_macro (n : Nat) (right : List Bool) :
    FConfig.run? machine (phaseF (n + 3) (false :: right)) (n + 8) =
      some (phaseF 1
        (List.replicate n false ++ [true, true, true] ++ right)) := by
  let afterPrefix : FConfig Sporadic.State :=
    ⟨A, List.replicate (n + 1) true ++ [false], true,
      [true, true, true] ++ right⟩
  have hPrefix : FConfig.run? machine
      (phaseF (n + 3) (false :: right)) 4 = some afterPrefix := by
    have hLeft : List.replicate (n + 3) true =
        true :: true :: List.replicate (n + 1) true := by
      rw [show n + 3 = (n + 1) + 2 by omega, replicate_two_succ]
    simp [phaseF, afterPrefix, hLeft, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine]
  let afterSweep : FConfig Sporadic.State :=
    ⟨A, [], false,
      List.replicate (n + 2) false ++ [true, true, true] ++ right⟩
  have hSweep : FConfig.run? machine afterPrefix (n + 2) =
      some afterSweep := by
    simpa [afterPrefix, afterSweep, show n + 2 = (n + 1) + 1 by omega]
      using scan_A_to_blank (n + 1) [] ([true, true, true] ++ right)
  have hFinish : FConfig.run? machine afterSweep 2 =
      some (phaseF 1
        (List.replicate n false ++ [true, true, true] ++ right)) := by
    have hZeros := replicate_two_succ false n
    simp [afterSweep, phaseF, hZeros, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine]
  have hPS := FConfig.run?_compose hPrefix hSweep
  have hAll := FConfig.run?_compose hPS hFinish
  have hTime : (4 + (n + 2)) + 2 = n + 8 := by omega
  simpa [hTime] using hAll

theorem phase_trailing_false (ell : Nat) (right : List Bool) :
    phase ell (right ++ [false]) = phase ell right := by
  apply PConfig.ext
  · rfl
  · intro i
    rfl
  · rfl
  · intro i
    have hPad := congrFun (Sporadic.pad_append_false right) i
    simpa [phase, phaseF, FConfig.toPConfig] using hPad

theorem marked_step (ell : Nat) (right : List Bool) :
    PTM.run? machine (phase ell (true :: right)) 5 =
      some (phase (ell + 1) right) := by
  have hBridge := FConfig.run?_toPConfig machine
    (phaseF ell (true :: right)) 5
  rw [marked_macro] at hBridge
  exact hBridge.symm

theorem short_blank_step (right : List Bool) :
    PTM.run? machine (phase 1 (false :: right)) 7 =
      some (phase 1 (true :: true :: right)) := by
  have hBridge := FConfig.run?_toPConfig machine
    (phaseF 1 (false :: right)) 7
  rw [short_blank_macro] at hBridge
  exact hBridge.symm.trans (congrArg some (short_result_to_phase right))

theorem long_blank_step (n : Nat) (right : List Bool) :
    PTM.run? machine (phase (n + 3) (false :: right)) (n + 8) =
      some (phase 1
        (List.replicate n false ++ [true, true, true] ++ right)) := by
  have hBridge := FConfig.run?_toPConfig machine
    (phaseF (n + 3) (false :: right)) (n + 8)
  rw [long_blank_macro] at hBridge
  exact hBridge.symm

theorem short_implicit_blank_step :
    PTM.run? machine (phase 1 []) 7 = some (phase 1 [true, true]) := by
  rw [← phase_trailing_false 1 []]
  simpa using short_blank_step []

theorem long_implicit_blank_step (n : Nat) :
    PTM.run? machine (phase (n + 3) []) (n + 8) =
      some (phase 1 (List.replicate n false ++ [true, true, true])) := by
  rw [← phase_trailing_false (n + 3) []]
  simpa using long_blank_step n []

structure PhaseSpec where
  ell : Nat
  right : List Bool

namespace PhaseSpec

/-- The only forbidden local situations are a length-one block followed by
`10`, and a length-two block followed by `0`. -/
def Good (p : PhaseSpec) : Prop :=
  1 ≤ p.ell ∧
  (p.ell = 1 → p.right.headD false = true →
    p.right.tail.headD false = true) ∧
  (p.ell = 2 → p.right.headD false = true)

def next : PhaseSpec → PhaseSpec
  | ⟨ell, true :: right⟩ => ⟨ell + 1, right⟩
  | ⟨1, false :: right⟩ => ⟨1, true :: true :: right⟩
  | ⟨ell, false :: right⟩ =>
      ⟨1, List.replicate (ell - 3) false ++ [true, true, true] ++ right⟩
  | ⟨1, []⟩ => ⟨1, [true, true]⟩
  | ⟨ell, []⟩ =>
      ⟨1, List.replicate (ell - 3) false ++ [true, true, true]⟩

def duration : PhaseSpec → Nat
  | ⟨_, true :: _⟩ => 5
  | ⟨1, false :: _⟩ => 7
  | ⟨ell, false :: _⟩ => ell + 5
  | ⟨1, []⟩ => 7
  | ⟨ell, []⟩ => ell + 5

theorem duration_pos (p : PhaseSpec) : 0 < p.duration := by
  rcases p with ⟨ell, right⟩
  cases right with
  | nil =>
      cases ell with
      | zero => simp [duration]
      | succ ell => cases ell <;> simp [duration]
  | cons bit right =>
      cases bit with
      | true => simp [duration]
      | false =>
          cases ell with
          | zero => simp [duration]
          | succ ell => cases ell <;> simp [duration]

theorem next_good {p : PhaseSpec} (h : p.Good) : p.next.Good := by
  rcases p with ⟨ell, right⟩
  rcases h with ⟨hPos, hOne, hTwo⟩
  change 1 ≤ ell at hPos
  change (ell = 1 → right.headD false = true →
    right.tail.headD false = true) at hOne
  change (ell = 2 → right.headD false = true) at hTwo
  cases right with
  | nil =>
      cases ell with
      | zero => simp at hPos
      | succ ell =>
          cases ell with
          | zero => simp [next, Good]
          | succ ell =>
              cases ell with
              | zero =>
                  have hBad := hTwo rfl
                  simp at hBad
              | succ n =>
                  cases n <;> simp [next, Good, List.replicate_succ]
  | cons bit right =>
      cases bit with
      | false =>
          cases ell with
          | zero => simp at hPos
          | succ ell =>
              cases ell with
              | zero => simp [next, Good]
              | succ ell =>
                  cases ell with
                  | zero =>
                      have hBad := hTwo rfl
                      simp at hBad
                  | succ n =>
                      cases n <;> simp [next, Good, List.replicate_succ]
      | true =>
          change Good ⟨ell + 1, right⟩
          refine ⟨by simp, ?_, ?_⟩
          · intro hEq
            change ell + 1 = 1 at hEq
            omega
          · intro hEq
            change ell + 1 = 2 at hEq
            have hEll : ell = 1 := by omega
            exact hOne hEll rfl

theorem run_next (p : PhaseSpec) (h : p.Good) :
    PTM.run? machine (phase p.ell p.right) p.duration =
      some (phase p.next.ell p.next.right) := by
  rcases p with ⟨ell, right⟩
  rcases h with ⟨hPos, _hOne, hTwo⟩
  change 1 ≤ ell at hPos
  change (ell = 2 → right.headD false = true) at hTwo
  cases right with
  | nil =>
      cases ell with
      | zero => simp at hPos
      | succ ell =>
          cases ell with
          | zero => simpa [duration, next] using short_implicit_blank_step
          | succ ell =>
              cases ell with
              | zero =>
                  have hBad := hTwo rfl
                  simp at hBad
              | succ n =>
                  simpa [duration, next] using long_implicit_blank_step n
  | cons bit right =>
      cases bit with
      | true => simpa [duration, next] using marked_step ell right
      | false =>
          cases ell with
          | zero => simp at hPos
          | succ ell =>
              cases ell with
              | zero => simpa [duration, next] using short_blank_step right
              | succ ell =>
                  cases ell with
                  | zero =>
                      have hBad := hTwo rfl
                      simp at hBad
                  | succ n =>
                      simpa [duration, next] using long_blank_step n right

end PhaseSpec

def initial : PhaseSpec := ⟨1, []⟩

def orbit : Nat → PhaseSpec
  | 0 => initial
  | n + 1 => (orbit n).next

def orbitTime : Nat → Nat
  | 0 => 2
  | n + 1 => orbitTime n + (orbit n).duration

theorem initial_good : initial.Good := by
  simp [initial, PhaseSpec.Good]

theorem orbit_good (n : Nat) : (orbit n).Good := by
  induction n with
  | zero => exact initial_good
  | succ n ih =>
      simpa [orbit] using PhaseSpec.next_good ih

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

theorem seed : PTM.run? machine (PConfig.blank A false) 2 =
    some (phase initial.ell initial.right) := by
  have hFinite : FConfig.run? machine blankF 2 =
      some (phaseF initial.ell initial.right) := by
    rfl
  have hBridge := FConfig.run?_toPConfig machine blankF 2
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

theorem reaches_orbit (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (orbitTime n) =
      some (phase (orbit n).ell (orbit n).right) := by
  induction n with
  | zero => simpa [orbitTime, orbit] using seed
  | succ n ih =>
      rw [orbitTime, ptm_run?_add, ih]
      exact PhaseSpec.run_next (orbit n) (orbit_good n)

theorem orbitTime_large (n : Nat) : n ≤ orbitTime n := by
  induction n with
  | zero => simp [orbitTime]
  | succ n ih =>
      simp only [orbitTime]
      have hPos := PhaseSpec.duration_pos (orbit n)
      omega

theorem machine_nonhalts : machine.Nonhalts A false := by
  intro steps
  exact ptm_run?_prefix (orbitTime_large steps) (reaches_orbit steps)

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

end SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariantA00
