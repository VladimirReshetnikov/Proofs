/-
  The sole partial table not covered by the standard BB4 n-gram/sporadic
  pipeline.  Its undefined `D/blank` slot is unreachable: an exact macro
  proof shows a solid marked interval growing without bound.
-/

import BusyBeaver.BB4.SporadicLeaf

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Uncovered

open BB3
open Sporadic
open Sporadic.State

/-- `1RB1LA_1RC1RD_0LA1RC_---0RC`. -/
def machine : PTM Sporadic.State Bool
  | A, false => some ⟨true, Move.right, B⟩
  | A, true => some ⟨true, Move.left, A⟩
  | B, false => some ⟨true, Move.right, C⟩
  | B, true => some ⟨true, Move.right, D⟩
  | C, false => some ⟨false, Move.left, A⟩
  | C, true => some ⟨true, Move.right, C⟩
  | D, false => none
  | D, true => some ⟨false, Move.right, C⟩

private theorem replicate_true_succ (n : Nat) :
    List.replicate (n + 1) true = true :: List.replicate n true := by
  simp [List.replicate_succ]

private theorem replicate_true_snoc (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail =
      List.replicate (n + 1) true ++ tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [replicate_true_succ, replicate_true_succ]
      simp only [List.cons_append, List.cons.injEq]
      exact ⟨True.intro, ih⟩

private theorem replicate_true_append (m n : Nat) :
    List.replicate m true ++ List.replicate n true =
      List.replicate (m + n) true := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [replicate_true_succ, show m + 1 + n = (m + n) + 1 by omega,
        replicate_true_succ]
      simp only [List.cons_append, List.cons.injEq]
      exact ⟨True.intro, ih⟩

/-- `A/mark` scans a solid block to the first blank on its left. -/
theorem scan_A_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine
      ⟨A, List.replicate n true ++ false :: left, true, right⟩ (n + 1) =
    some ⟨A, left, false, List.replicate (n + 1) true ++ right⟩ := by
  induction n generalizing right with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine
          ⟨A, true :: (List.replicate n true ++ false :: left), true, right⟩ 1 =
          some ⟨A, List.replicate n true ++ false :: left,
            true, true :: right⟩ := by
        rfl
      have hRest := ih (true :: right)
      have hComposed := FConfig.run?_compose
        (first := 1) (second := n + 1)
        (cfg := ⟨A, true :: (List.replicate n true ++ false :: left),
          true, right⟩)
        (middle := ⟨A, List.replicate n true ++ false :: left,
          true, true :: right⟩)
        hFirst hRest
      have hTime : 1 + (n + 1) = n + 1 + 1 := by omega
      have hList :
          List.replicate (n + 1) true ++ true :: right =
            List.replicate (1 + (n + 1)) true ++ right := by
        rw [replicate_true_snoc]
        congr 2 <;> omega
      rw [← hTime, hComposed]
      exact congrArg some (congrArg
        (fun xs => (FConfig.mk A left false xs : FConfig Sporadic.State)) hList)

/-- `C/mark` scans a solid block to the first blank on its right. -/
theorem scan_C_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine
      ⟨C, left, true, List.replicate n true ++ false :: right⟩ (n + 1) =
    some ⟨C, List.replicate (n + 1) true ++ left, false, right⟩ := by
  induction n generalizing left with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine
          ⟨C, left, true,
            true :: (List.replicate n true ++ false :: right)⟩ 1 =
          some ⟨C, true :: left, true,
            List.replicate n true ++ false :: right⟩ := by
        rfl
      have hRest := ih (true :: left)
      have hComposed := FConfig.run?_compose
        (first := 1) (second := n + 1)
        (cfg := ⟨C, left, true,
          true :: (List.replicate n true ++ false :: right)⟩)
        (middle := ⟨C, true :: left, true,
          List.replicate n true ++ false :: right⟩)
        hFirst hRest
      have hTime : 1 + (n + 1) = n + 1 + 1 := by omega
      have hList :
          List.replicate (n + 1) true ++ true :: left =
            List.replicate (1 + (n + 1)) true ++ left := by
        rw [replicate_true_snoc]
        congr 2 <;> omega
      rw [← hTime, hComposed]
      exact congrArg some (congrArg
        (fun xs => (FConfig.mk C xs false right : FConfig Sporadic.State)) hList)

/-- One sweep moves the unique hole two cells toward the right frontier. -/
theorem sweep (n : Nat) (tail : List Bool) :
    FConfig.run? machine
      ⟨A, List.replicate (2 * n + 3) true ++ false :: tail,
        true, [false]⟩ (4 * n + 10) =
    some ⟨A,
      List.replicate (2 * n + 1) true ++ false :: true :: true :: tail,
      true, [false]⟩ := by
  let afterA : FConfig Sporadic.State :=
    ⟨A, tail, false, List.replicate (2 * n + 4) true ++ [false]⟩
  have hA : FConfig.run? machine
      ⟨A, List.replicate (2 * n + 3) true ++ false :: tail,
        true, [false]⟩ (2 * n + 4) = some afterA := by
    simpa [afterA, show 2 * n + 4 = (2 * n + 3) + 1 by omega]
      using scan_A_to_blank (2 * n + 3) tail [false]
  let afterABD : FConfig Sporadic.State :=
    ⟨C, false :: true :: true :: tail, true,
      List.replicate (2 * n + 1) true ++ [false]⟩
  have hRight :
      List.replicate (2 * n + 4) true =
        true :: true :: true :: List.replicate (2 * n + 1) true := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 by omega,
      replicate_true_succ,
      show 2 * n + 3 = (2 * n + 2) + 1 by omega,
      replicate_true_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      replicate_true_succ]
  have hABD : FConfig.run? machine afterA 3 = some afterABD := by
    simp [afterA, afterABD, hRight, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine]
  let afterC : FConfig Sporadic.State :=
    ⟨C,
      List.replicate (2 * n + 2) true ++ false :: true :: true :: tail,
      false, []⟩
  have hC : FConfig.run? machine afterABD (2 * n + 2) = some afterC := by
    simpa [afterABD, afterC,
      show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      using scan_C_to_blank (2 * n + 1)
        (false :: true :: true :: tail) []
  have hFinal : FConfig.run? machine afterC 1 =
      some ⟨A,
        List.replicate (2 * n + 1) true ++ false :: true :: true :: tail,
        true, [false]⟩ := by
    have hRep : List.replicate (2 * n + 2) true =
        true :: List.replicate (2 * n + 1) true := by
      rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        replicate_true_succ]
    simp [afterC, hRep, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine]
  have h1 := FConfig.run?_compose hA hABD
  have h2 := FConfig.run?_compose h1 hC
  have h3 := FConfig.run?_compose h2 hFinal
  have hTime : (((2 * n + 4) + 3) + (2 * n + 2)) + 1 =
      4 * n + 10 := by omega
  simpa [hTime] using h3

/-- Machine phase: the head is on the right endpoint of a solid interval. -/
def phaseF (n : Nat) : FConfig Sporadic.State :=
  ⟨A, List.replicate (2 * n + 1) true, true, [false]⟩

def phase (n : Nat) : PConfig Sporadic.State Bool := (phaseF n).toPConfig

def phaseSeed (n : Nat) : FConfig Sporadic.State :=
  ⟨A, List.replicate (2 * n + 1) true ++ [false], true, [false]⟩

theorem phaseSeed_toPConfig (n : Nat) :
    (phaseSeed n).toPConfig = phase n := by
  apply PConfig.ext
  · rfl
  · intro i
    have hPad := congrFun
      (pad_append_false (List.replicate (2 * n + 1) true)) i
    simpa [phaseSeed, phase, phaseF, FConfig.toPConfig] using hPad
  · rfl
  · intro i
    rfl

/-- After `k` sweeps, `r` hole moves remain. -/
def mid (k r : Nat) : FConfig Sporadic.State :=
  ⟨A,
    List.replicate (2 * r + 1) true ++
      false :: List.replicate (2 * k + 2) true,
    true, [false]⟩

theorem enter (n : Nat) :
    FConfig.run? machine (phaseSeed (n + 1)) (4 * n + 10) =
      some (mid 0 n) := by
  have h := sweep n []
  simpa [phaseSeed, mid,
    show 2 * (n + 1) + 1 = 2 * n + 3 by omega] using h

theorem cycle (k n : Nat) :
    FConfig.run? machine (mid k (n + 1)) (4 * n + 10) =
      some (mid (k + 1) n) := by
  have h := sweep n (List.replicate (2 * k + 2) true)
  simpa [mid,
    show 2 * (n + 1) + 1 = 2 * n + 3 by omega,
    show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega,
    show List.replicate ((2 * k + 2) + 2) true =
      true :: true :: List.replicate (2 * k + 2) true by
        rw [show (2 * k + 2) + 2 = ((2 * k + 2) + 1) + 1 by omega,
          replicate_true_succ, replicate_true_succ]] using h

def cyclesTime : Nat -> Nat
  | 0 => 0
  | n + 1 => (4 * n + 10) + cyclesTime n

theorem cycles (k r : Nat) :
    FConfig.run? machine (mid k r) (cyclesTime r) =
      some (mid (k + r) 0) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
      have hFirst := cycle k r
      have hRest := ih (k + 1)
      have hAll := FConfig.run?_compose hFirst hRest
      have hIndex : k + 1 + r = k + (r + 1) := by omega
      simpa [cyclesTime, hIndex] using hAll

theorem finish (k : Nat) :
    FConfig.run? machine (mid k 0) 9 = some (phaseF (k + 2)) := by
  let afterA : FConfig Sporadic.State :=
    ⟨A, List.replicate (2 * k + 2) true, false,
      List.replicate 2 true ++ [false]⟩
  have hA : FConfig.run? machine (mid k 0) 2 = some afterA := by
    simpa [mid, afterA] using
      scan_A_to_blank 1 (List.replicate (2 * k + 2) true) [false]
  have hRest : FConfig.run? machine afterA 7 = some (phaseF (k + 2)) := by
    have hTwo : List.replicate 2 true = [true, true] := by rfl
    have hTail :
        true :: true :: true :: List.replicate (2 * k + 2) true =
          List.replicate (2 * (k + 2) + 1) true := by
      have h := replicate_true_append 3 (2 * k + 2)
      simpa [show 3 + (2 * k + 2) = 2 * (k + 2) + 1 by omega] using h
    simp [afterA, phaseF, hTwo, hTail, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine]
  have hAll := FConfig.run?_compose hA hRest
  simpa using hAll

def stepTime : Nat -> Nat
  | 0 => 9
  | n + 1 => (4 * n + 10) + cyclesTime n + 9

theorem phase_step (n : Nat) :
    PTM.run? machine (phase n) (stepTime n) = some (phase (n + 1)) := by
  cases n with
  | zero =>
      have hFinite : FConfig.run? machine (phaseSeed 0) 9 =
          some (phaseF 1) := by decide
      have hBridge := FConfig.run?_toPConfig machine (phaseSeed 0) 9
      rw [hFinite, phaseSeed_toPConfig] at hBridge
      simpa [stepTime, phase] using hBridge.symm
  | succ n =>
      have hEnter := enter n
      have hCycles := cycles 0 n
      have hCycles' : FConfig.run? machine (mid 0 n) (cyclesTime n) =
          some (mid n 0) := by simpa using hCycles
      have hFinish := finish n
      have hEC := FConfig.run?_compose hEnter hCycles'
      have hFinite := FConfig.run?_compose hEC hFinish
      have hTime : ((4 * n + 10) + cyclesTime n) + 9 =
          stepTime (n + 1) := by rfl
      have hFinite' : FConfig.run? machine (phaseSeed (n + 1))
          (stepTime (n + 1)) = some (phaseF (n + 2)) := by
        rw [← hTime]
        simpa using hFinite
      have hBridge := FConfig.run?_toPConfig machine (phaseSeed (n + 1))
        (stepTime (n + 1))
      rw [hFinite', phaseSeed_toPConfig] at hBridge
      simpa [phase] using hBridge.symm

def blankF : FConfig Sporadic.State := ⟨A, [], false, []⟩

theorem blankF_toPConfig : blankF.toPConfig = PConfig.blank A false := by
  rfl

theorem seed : PTM.run? machine (PConfig.blank A false) 3 = some (phase 0) := by
  have hFinite : FConfig.run? machine blankF 3 = some (phaseF 0) := by decide
  have hBridge := FConfig.run?_toPConfig machine blankF 3
  rw [hFinite, blankF_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime : Nat -> Nat
  | 0 => 3
  | n + 1 => phaseTime n + stepTime n

theorem reaches_phase (n : Nat) :
    PTM.run? machine (PConfig.blank A false) (phaseTime n) =
      some (phase n) := by
  induction n with
  | zero => exact seed
  | succ n ih =>
      rw [phaseTime, ptm_run?_add, ih]
      exact phase_step n

theorem phaseTime_large (n : Nat) : n <= phaseTime n := by
  induction n with
  | zero => simp [phaseTime]
  | succ n ih =>
      simp only [phaseTime]
      have hPositive : 0 < stepTime n := by
        cases n <;> simp [stepTime] <;> omega
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

end SetTheory.BusyBeaver.BB4.Certificates.C14Uncovered
