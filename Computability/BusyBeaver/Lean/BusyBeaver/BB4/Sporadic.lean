/-
  BusyBeaverBB4/Sporadic.lean

  Direct macro proofs for the two four-state machines that require the
  repeated-word-list decider in the upstream CoqBB4 enumeration.

  The proof layer uses finite zipper sides padded by blank symbols.  A generic
  simulation theorem connects that executable representation to the partial
  zipper semantics from `BusyBeaverBB3.Partial`.
-/

import BusyBeaver.BB3.Partial

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace Sporadic

open BB3

/-! ## A finite presentation of blank-padded zippers -/

/-- Read a finite list as an infinite list padded by `false`. -/
@[simp]
def pad : List Bool -> Nat -> Bool
  | [], _ => false
  | value :: _, 0 => value
  | _ :: rest, n + 1 => pad rest n

theorem pad_append_false (xs : List Bool) :
    pad (xs ++ [false]) = pad xs := by
  funext n
  induction xs generalizing n with
  | nil => cases n <;> rfl
  | cons value xs ih =>
      cases n with
      | zero => rfl
      | succ n => simpa using ih n

/-- A finite zipper.  Cells beyond the stored sides are blank. -/
structure FConfig (State : Type) where
  state : State
  left : List Bool
  center : Bool
  right : List Bool
  deriving DecidableEq, Repr

namespace FConfig

/-- Interpret a finite zipper as the generic infinite zipper. -/
def toPConfig {State : Type} (cfg : FConfig State) : PConfig State Bool where
  state := cfg.state
  left := pad cfg.left
  center := cfg.center
  right := pad cfg.right

/-- Execute a known continuing action on a finite zipper. -/
def stepAction {State : Type} (cfg : FConfig State)
    (action : PAction State Bool) : FConfig State :=
  match action.move with
  | Move.right =>
      { state := action.next
        left := action.write :: cfg.left
        center := pad cfg.right 0
        right := cfg.right.tail }
  | Move.left =>
      { state := action.next
        left := cfg.left.tail
        center := pad cfg.left 0
        right := action.write :: cfg.right }

/-- Execute one transition, stopping at an undefined table entry. -/
def step? {State : Type} (machine : PTM State Bool) (cfg : FConfig State) :
    Option (FConfig State) :=
  (machine cfg.state cfg.center).map (stepAction cfg)

/-- Execute exactly `steps` finite-zipper transitions. -/
def run? {State : Type} (machine : PTM State Bool) (cfg : FConfig State) :
    Nat -> Option (FConfig State)
  | 0 => some cfg
  | steps + 1 => (run? machine cfg steps).bind (step? machine)

@[simp]
theorem run?_zero {State : Type} (machine : PTM State Bool)
    (cfg : FConfig State) : run? machine cfg 0 = some cfg := rfl

@[simp]
theorem run?_succ {State : Type} (machine : PTM State Bool)
    (cfg : FConfig State) (steps : Nat) :
    run? machine cfg (steps + 1) =
      (run? machine cfg steps).bind (step? machine) := rfl

theorem toPConfig_stepAction {State : Type} (cfg : FConfig State)
    (action : PAction State Bool) :
    (stepAction cfg action).toPConfig =
      PTM.stepAction cfg.toPConfig action := by
  rcases cfg with ⟨state, left, center, right⟩
  rcases action with ⟨write, move, next⟩
  cases move with
  | left =>
      apply PConfig.ext
      · rfl
      · intro n
        cases left <;> cases n <;> rfl
      · rfl
      · intro n
        cases n <;> rfl
  | right =>
      apply PConfig.ext
      · rfl
      · intro n
        cases n <;> rfl
      · rfl
      · intro n
        cases right <;> cases n <;> rfl

theorem step?_toPConfig {State : Type} (machine : PTM State Bool)
    (cfg : FConfig State) :
    (step? machine cfg).map toPConfig =
      PTM.step? machine cfg.toPConfig := by
  unfold step? PTM.step?
  change
    Option.map toPConfig
        (Option.map (stepAction cfg) (machine cfg.state cfg.center)) =
      Option.map (PTM.stepAction cfg.toPConfig)
        (machine cfg.state cfg.center)
  cases hLookup : machine cfg.state cfg.center with
  | none => simp
  | some action =>
      simp only [Option.map_some]
      exact congrArg some (toPConfig_stepAction cfg action)

theorem run?_toPConfig {State : Type} (machine : PTM State Bool)
    (cfg : FConfig State) : forall steps,
    (run? machine cfg steps).map toPConfig =
      PTM.run? machine cfg.toPConfig steps := by
  intro steps
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [run?_succ, PTM.run?_succ]
      rw [← ih]
      cases hRun : run? machine cfg steps with
      | none => simp
      | some middle =>
          simp only [Option.map_some, Option.bind_some]
          exact step?_toPConfig machine middle

theorem run?_add {State : Type} (machine : PTM State Bool)
    (cfg : FConfig State) (first second : Nat) :
    run? machine cfg (first + second) =
      (run? machine cfg first).bind fun middle =>
        run? machine middle second := by
  induction second with
  | zero => simp
  | succ second ih =>
      simp only [Nat.add_succ, run?_succ, ih]
      cases run? machine cfg first <;> simp

theorem run?_compose {State : Type} {machine : PTM State Bool}
    {cfg middle result : FConfig State} {first second : Nat}
    (hFirst : run? machine cfg first = some middle)
    (hSecond : run? machine middle second = some result) :
    run? machine cfg (first + second) = some result := by
  rw [run?_add, hFirst]
  exact hSecond

end FConfig

/-- Split a generic partial-machine run at an arbitrary prefix. -/
theorem ptm_run?_add {State Symbol : Type} (machine : PTM State Symbol)
    (cfg : PConfig State Symbol) (first second : Nat) :
    PTM.run? machine cfg (first + second) =
      (PTM.run? machine cfg first).bind fun middle =>
        PTM.run? machine middle second := by
  induction second with
  | zero => simp
  | succ second ih =>
      simp only [Nat.add_succ, PTM.run?_succ, ih]
      cases PTM.run? machine cfg first <;> simp

/-- Every prefix of a successful partial-machine run is successful. -/
theorem ptm_run?_prefix {State Symbol : Type} {machine : PTM State Symbol}
    {cfg : PConfig State Symbol} {short long : Nat}
    (hLe : short ≤ long)
    {result : PConfig State Symbol}
    (hLong : PTM.run? machine cfg long = some result) :
    exists middle, PTM.run? machine cfg short = some middle := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hLe
  rw [ptm_run?_add] at hLong
  cases hShort : PTM.run? machine cfg short with
  | none => simp [hShort] at hLong
  | some middle => exact ⟨middle, rfl⟩

/-! ## The two residual machines -/

/-- Four operational states, named as in the upstream machine strings. -/
inductive State
  | A | B | C | D
  deriving DecidableEq, Repr

open State

/-- `1RB1LA_1LA0RC_1LD1RC_---0LA`: only `D0` is undefined. -/
def machine1 : PTM State Bool
  | A, false => some ⟨true, Move.right, B⟩
  | A, true => some ⟨true, Move.left, A⟩
  | B, false => some ⟨true, Move.left, A⟩
  | B, true => some ⟨false, Move.right, C⟩
  | C, false => some ⟨true, Move.left, D⟩
  | C, true => some ⟨true, Move.right, C⟩
  | D, false => none
  | D, true => some ⟨false, Move.left, A⟩

/-- `1RB0RB_1LC1RB_---0LD_1RA1LD`: only `C0` is undefined. -/
def machine2 : PTM State Bool
  | A, false => some ⟨true, Move.right, B⟩
  | A, true => some ⟨false, Move.right, B⟩
  | B, false => some ⟨true, Move.left, C⟩
  | B, true => some ⟨true, Move.right, B⟩
  | C, false => none
  | C, true => some ⟨false, Move.left, D⟩
  | D, false => some ⟨true, Move.right, A⟩
  | D, true => some ⟨true, Move.left, D⟩

/-! ## Shared exact scan lemmas -/

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

/-- Machine 1's `C1` transition scans a solid block to the right. -/
theorem machine1_scan_C (n : Nat) (left right : List Bool) :
    FConfig.run? machine1
      ⟨C, left, true, List.replicate n true ++ false :: right⟩ (n + 1) =
    some ⟨C, List.replicate (n + 1) true ++ left, false, right⟩ := by
  induction n generalizing left with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine1]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hStep :
          FConfig.step? machine1
            ⟨C, left, true,
              true :: (List.replicate n true ++ false :: right)⟩ =
            some ⟨C, true :: left, true,
              List.replicate n true ++ false :: right⟩ := by
        rfl
      have hRest := ih (true :: left)
      have hFirst : FConfig.run? machine1
          ⟨C, left, true,
            true :: (List.replicate n true ++ false :: right)⟩ 1 =
          some ⟨C, true :: left, true,
            List.replicate n true ++ false :: right⟩ := by
        simpa [FConfig.run?] using hStep
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
        (fun xs => (FConfig.mk C xs false right : FConfig State)) hList)

/-- Machine 1's `A1` transition scans a solid block to the left. -/
theorem machine1_scan_A (n : Nat) (left right : List Bool) :
    FConfig.run? machine1
      ⟨A, List.replicate n true ++ left, true, right⟩ n =
    some ⟨A, left, true, List.replicate n true ++ right⟩ := by
  induction n generalizing right with
  | zero => rfl
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine1
          ⟨A, true :: (List.replicate n true ++ left), true, right⟩ 1 =
          some ⟨A, List.replicate n true ++ left, true, true :: right⟩ := by
        rfl
      have hRest := ih (true :: right)
      have hComposed := FConfig.run?_compose
        (first := 1) (second := n)
        (cfg := ⟨A, true :: (List.replicate n true ++ left), true, right⟩)
        (middle := ⟨A, List.replicate n true ++ left, true, true :: right⟩)
        (result := ⟨A, left, true,
          List.replicate n true ++ true :: right⟩) hFirst hRest
      have hTime : 1 + n = n + 1 := by omega
      have hList :
          List.replicate n true ++ true :: right =
            true :: (List.replicate n true ++ right) := by
        rw [replicate_true_snoc, replicate_true_succ]
        rfl
      rw [← hTime, hComposed]
      exact congrArg some (congrArg
        (fun xs => (FConfig.mk A left true xs : FConfig State)) hList)

/-- Machine 1's `A1` transition scans left through `n + 1` marked cells
and stops on the first blank. -/
theorem machine1_scan_A_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine1
      ⟨A, List.replicate n true ++ false :: left, true, right⟩ (n + 1) =
    some ⟨A, left, false, List.replicate (n + 1) true ++ right⟩ := by
  induction n generalizing right with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine1]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine1
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
        (fun xs => (FConfig.mk A left false xs : FConfig State)) hList)

/-- Machine 2's `B1` transition scans a solid block to the right. -/
theorem machine2_scan_B_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine2
      ⟨B, left, true, List.replicate n true ++ false :: right⟩ (n + 1) =
    some ⟨B, List.replicate (n + 1) true ++ left, false, right⟩ := by
  induction n generalizing left with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine2]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine2
          ⟨B, left, true,
            true :: (List.replicate n true ++ false :: right)⟩ 1 =
          some ⟨B, true :: left, true,
            List.replicate n true ++ false :: right⟩ := by
        rfl
      have hRest := ih (true :: left)
      have hComposed := FConfig.run?_compose
        (first := 1) (second := n + 1)
        (cfg := ⟨B, left, true,
          true :: (List.replicate n true ++ false :: right)⟩)
        (middle := ⟨B, true :: left, true,
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
        (fun xs => (FConfig.mk B xs false right : FConfig State)) hList)

/-- The same `B1` scan when the blank is supplied by the implicit padded
tail rather than stored explicitly. -/
theorem machine2_scan_B_off_end (n : Nat) (left : List Bool) :
    FConfig.run? machine2
      ⟨B, left, true, List.replicate n true⟩ (n + 1) =
    some ⟨B, List.replicate (n + 1) true ++ left, false, []⟩ := by
  induction n generalizing left with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine2]
  | succ n ih =>
      rw [replicate_true_succ]
      have hFirst : FConfig.run? machine2
          ⟨B, left, true, true :: List.replicate n true⟩ 1 =
          some ⟨B, true :: left, true, List.replicate n true⟩ := by
        rfl
      have hRest := ih (true :: left)
      have hComposed := FConfig.run?_compose hFirst hRest
      have hTime : 1 + (n + 1) = n + 1 + 1 := by omega
      have hList :
          List.replicate (n + 1) true ++ true :: left =
            List.replicate (1 + (n + 1)) true ++ left := by
        rw [replicate_true_snoc]
        congr 2 <;> omega
      rw [← hTime, hComposed]
      exact congrArg some (congrArg
        (fun xs => (FConfig.mk B xs false [] : FConfig State)) hList)

/-- Machine 2's `D1` transition scans left through `n + 1` marked cells
and stops on the first blank. -/
theorem machine2_scan_D_to_blank (n : Nat) (left right : List Bool) :
    FConfig.run? machine2
      ⟨D, List.replicate n true ++ false :: left, true, right⟩ (n + 1) =
    some ⟨D, left, false, List.replicate (n + 1) true ++ right⟩ := by
  induction n generalizing right with
  | zero => simp [FConfig.run?, FConfig.step?, FConfig.stepAction, machine2]
  | succ n ih =>
      rw [replicate_true_succ]
      simp only [List.cons_append]
      have hFirst : FConfig.run? machine2
          ⟨D, true :: (List.replicate n true ++ false :: left), true, right⟩ 1 =
          some ⟨D, List.replicate n true ++ false :: left,
            true, true :: right⟩ := by
        rfl
      have hRest := ih (true :: right)
      have hComposed := FConfig.run?_compose
        (first := 1) (second := n + 1)
        (cfg := ⟨D, true :: (List.replicate n true ++ false :: left),
          true, right⟩)
        (middle := ⟨D, List.replicate n true ++ false :: left,
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
        (fun xs => (FConfig.mk D left false xs : FConfig State)) hList)

/-! ## Machine 2: exact nested macro -/

/-- The intermediate configuration after `k` outer sweeps, with `r` sweeps
still to perform.  The isolated blank in `left` is the moving separator. -/
def mid2 (k r : Nat) : FConfig State :=
  ⟨B,
    List.replicate (2 * r + 1) true ++
      false :: List.replicate k true,
    false,
    List.replicate k true⟩

/-- Time spent by the decreasing inner loop of machine 2. -/
def cyclesTime2 : Nat -> Nat
  | 0 => 0
  | r + 1 => (4 * (r + 1) + 3) + cyclesTime2 r

private theorem replicate_true_two_succ (n : Nat) :
    List.replicate (n + 2) true =
      true :: true :: List.replicate n true := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    replicate_true_succ, replicate_true_succ]

/-- One machine-2 sweep takes `4r+3` steps and decreases the sweep counter. -/
theorem machine2_cycle (k n : Nat) :
    FConfig.run? machine2 (mid2 k (n + 1)) (4 * (n + 1) + 3) =
      some (mid2 (k + 1) n) := by
  have hOuter :
      List.replicate (2 * (n + 1) + 1) true =
        true :: true :: List.replicate (2 * n + 1) true := by
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      replicate_true_two_succ]
  let afterBC : FConfig State :=
    ⟨D,
      List.replicate (2 * n + 1) true ++
        false :: List.replicate k true,
      true,
      false :: true :: List.replicate k true⟩
  have hBC : FConfig.run? machine2 (mid2 k (n + 1)) 2 =
      some afterBC := by
    simp [mid2, afterBC, hOuter, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine2]
  let afterD : FConfig State :=
    ⟨D,
      List.replicate k true,
      false,
      List.replicate (2 * n + 2) true ++
        false :: true :: List.replicate k true⟩
  have hD : FConfig.run? machine2 afterBC (2 * n + 2) =
      some afterD := by
    simpa [afterBC, afterD, show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      using machine2_scan_D_to_blank (2 * n + 1)
        (List.replicate k true) (false :: true :: List.replicate k true)
  let beforeBScan : FConfig State :=
    ⟨B,
      false :: true :: List.replicate k true,
      true,
      List.replicate (2 * n) true ++
        false :: true :: List.replicate k true⟩
  have hInner :
      List.replicate (2 * n + 2) true =
        true :: true :: List.replicate (2 * n) true := by
    exact replicate_true_two_succ (2 * n)
  have hDA : FConfig.run? machine2 afterD 2 = some beforeBScan := by
    simp [afterD, beforeBScan, hInner, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine2]
  have hB : FConfig.run? machine2 beforeBScan (2 * n + 1) =
      some (mid2 (k + 1) n) := by
    have hScan := machine2_scan_B_to_blank (2 * n)
      (false :: true :: List.replicate k true)
      (true :: List.replicate k true)
    unfold mid2
    rw [replicate_true_succ k]
    simpa [beforeBScan] using hScan
  have hBCD := FConfig.run?_compose hBC hD
  have hBCDA := FConfig.run?_compose hBCD hDA
  have hAll := FConfig.run?_compose hBCDA hB
  have hTime : ((2 + (2 * n + 2)) + 2) + (2 * n + 1) =
      4 * (n + 1) + 3 := by omega
  simpa [hTime] using hAll

/-- Execute all `r` remaining machine-2 sweeps. -/
theorem machine2_cycles (k r : Nat) :
    FConfig.run? machine2 (mid2 k r) (cyclesTime2 r) =
      some (mid2 (k + r) 0) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
      have hFirst := machine2_cycle k r
      have hRest := ih (k + 1)
      have hAll := FConfig.run?_compose hFirst hRest
      have hIndex : k + 1 + r = k + (r + 1) := by omega
      simpa [cyclesTime2, hIndex] using hAll

theorem cyclesTime2_closed (r : Nat) :
    cyclesTime2 r = 2 * r * r + 5 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [cyclesTime2, ih, Nat.mul_add, Nat.add_mul,
        Nat.mul_one]
      omega

/-- The solid-interval phase for machine 2.  Relative to the head, exactly
the `2n+1` cells immediately to the left are marked. -/
def phase2F (n : Nat) : FConfig State :=
  ⟨B, List.replicate (2 * n + 1) true, false, []⟩

def phase2 (n : Nat) : PConfig State Bool := (phase2F n).toPConfig

/-- The final straight-line part after all decreasing sweeps. -/
theorem machine2_finish (n : Nat) :
    FConfig.run? machine2 (mid2 n 0) (n + 5) =
      some (phase2F (n + 1)) := by
  let beforeScan : FConfig State :=
    ⟨B, List.replicate (n + 2) true, true,
      List.replicate n true⟩
  have hPrefix : FConfig.run? machine2 (mid2 n 0) 4 =
      some beforeScan := by
    simp [mid2, beforeScan, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine2, replicate_true_two_succ]
  have hScan := machine2_scan_B_off_end n (List.replicate (n + 2) true)
  have hAll := FConfig.run?_compose hPrefix hScan
  have hLists :
      List.replicate (n + 1) true ++ List.replicate (n + 2) true =
        List.replicate (2 * (n + 1) + 1) true := by
    rw [replicate_true_append]
    apply congrArg (fun width => List.replicate width true)
    omega
  have hTime : 4 + (n + 1) = n + 5 := by omega
  rw [← hTime]
  rw [hAll]
  exact congrArg some (congrArg
    (fun xs => (FConfig.mk B xs false [] : FConfig State)) hLists)

/-- Exact P2 macro: `P2(n) -> P2(n+1)` in `2n²+6n+5` steps. -/
theorem machine2_phase_step (n : Nat) :
    PTM.run? machine2 (phase2 n) (2 * n * n + 6 * n + 5) =
      some (phase2 (n + 1)) := by
  have hCycles := machine2_cycles 0 n
  have hFinish := machine2_finish n
  have hCycles' :
      FConfig.run? machine2 (mid2 0 n) (cyclesTime2 n) =
        some (mid2 n 0) := by
    simpa using hCycles
  have hFinite := FConfig.run?_compose hCycles' hFinish
  have hTime : cyclesTime2 n + (n + 5) = 2 * n * n + 6 * n + 5 := by
    rw [cyclesTime2_closed]
    omega
  have hFinite' :
      FConfig.run? machine2 (mid2 0 n) (2 * n * n + 6 * n + 5) =
        some (phase2F (n + 1)) := by
    rw [← hTime]
    simpa using hFinite
  have hBridge := FConfig.run?_toPConfig machine2 (mid2 0 n)
    (2 * n * n + 6 * n + 5)
  rw [hFinite'] at hBridge
  have hStart : (mid2 0 n).toPConfig = phase2 n := by
    apply PConfig.ext
    · rfl
    · intro i
      have hPad := congrFun (pad_append_false
        (List.replicate (2 * n + 1) true)) i
      simpa [mid2, phase2, phase2F, FConfig.toPConfig] using hPad
    · rfl
    · intro i
      rfl
  rw [hStart] at hBridge
  exact hBridge.symm

/-- Absolute phase times, including the single initial `A0` transition. -/
def phaseTime2 : Nat -> Nat
  | 0 => 1
  | n + 1 => phaseTime2 n + (2 * n * n + 6 * n + 5)

theorem machine2_reaches_phase (n : Nat) :
    PTM.run? machine2 (PConfig.blank A false) (phaseTime2 n) =
      some (phase2 n) := by
  induction n with
  | zero =>
      simp only [phaseTime2, PTM.run?_succ, PTM.run?_zero,
        Option.bind_some, PTM.step?, machine2]
      apply congrArg some
      apply PConfig.ext
      · rfl
      · intro i
        cases i <;> rfl
      · rfl
      · intro i
        rfl
  | succ n ih =>
      rw [phaseTime2, ptm_run?_add, ih]
      exact machine2_phase_step n

theorem phaseTime2_large (n : Nat) : n + 1 ≤ phaseTime2 n := by
  induction n with
  | zero => simp [phaseTime2]
  | succ n ih =>
      simp only [phaseTime2]
      omega

/-- The second RepWL-only four-state machine runs forever. -/
theorem machine2_nonhalts : machine2.Nonhalts A false := by
  intro steps
  have hLong := machine2_reaches_phase steps
  apply ptm_run?_prefix (result := phase2 steps) (long := phaseTime2 steps)
  · have hLarge := phaseTime2_large steps
    omega
  · exact hLong

/-! ## Machine 1: exact nested macro -/

/-- Machine 1 after `k` completed sweeps with `r` sweeps remaining. -/
def mid1 (k : Nat) : Nat -> FConfig State
  | 0 =>
      ⟨B, List.replicate (k + 1) true ++ [false], false,
        List.replicate k true⟩
  | r + 1 =>
      ⟨B, List.replicate (k + 1) true ++ [false], true,
        List.replicate (2 * r + 1) true ++
          false :: List.replicate k true⟩

def cyclesTime1 : Nat -> Nat
  | 0 => 0
  | r + 1 => (4 * (r + 1) + 1) + cyclesTime1 r

/-- One machine-1 sweep takes `4r+1` steps and decreases the counter. -/
theorem machine1_cycle (k n : Nat) :
    FConfig.run? machine1 (mid1 k (n + 1)) (4 * (n + 1) + 1) =
      some (mid1 (k + 1) n) := by
  cases n with
  | zero =>
      simp [mid1, FConfig.run?, FConfig.step?, FConfig.stepAction,
        machine1, replicate_true_succ]
  | succ m =>
      have hRight :
          List.replicate (2 * (m + 1) + 1) true =
            true :: List.replicate (2 * m + 2) true := by
        rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          replicate_true_succ]
      let afterB : FConfig State :=
        ⟨C,
          false :: (List.replicate (k + 1) true ++ [false]),
          true,
          List.replicate (2 * m + 2) true ++
            false :: List.replicate k true⟩
      have hB : FConfig.run? machine1 (mid1 k (m + 2)) 1 =
          some afterB := by
        simp [mid1, afterB, hRight, FConfig.run?, FConfig.step?,
          FConfig.stepAction, machine1]
      let afterC : FConfig State :=
        ⟨C,
          List.replicate (2 * m + 3) true ++
            false :: (List.replicate (k + 1) true ++ [false]),
          false,
          List.replicate k true⟩
      have hC : FConfig.run? machine1 afterB (2 * m + 3) =
          some afterC := by
        simpa [afterB, afterC,
          show 2 * m + 3 = (2 * m + 2) + 1 by omega]
          using machine1_scan_C (2 * m + 2)
            (false :: (List.replicate (k + 1) true ++ [false]))
            (List.replicate k true)
      let beforeA : FConfig State :=
        ⟨A,
          List.replicate (2 * m + 1) true ++
            false :: (List.replicate (k + 1) true ++ [false]),
          true,
          false :: true :: List.replicate k true⟩
      have hBlock :
          List.replicate (2 * m + 3) true =
            true :: true :: List.replicate (2 * m + 1) true := by
        rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega,
          replicate_true_two_succ]
      have hCD : FConfig.run? machine1 afterC 2 = some beforeA := by
        simp [afterC, beforeA, hBlock, FConfig.run?, FConfig.step?,
          FConfig.stepAction, machine1]
      let afterA : FConfig State :=
        ⟨A,
          List.replicate (k + 1) true ++ [false],
          false,
          List.replicate (2 * m + 2) true ++
            false :: true :: List.replicate k true⟩
      have hA : FConfig.run? machine1 beforeA (2 * m + 2) =
          some afterA := by
        simpa [beforeA, afterA,
          show 2 * m + 2 = (2 * m + 1) + 1 by omega]
          using machine1_scan_A_to_blank (2 * m + 1)
            (List.replicate (k + 1) true ++ [false])
            (false :: true :: List.replicate k true)
      have hFinal : FConfig.run? machine1 afterA 1 =
          some (mid1 (k + 1) (m + 1)) := by
        unfold mid1
        simp [afterA, FConfig.run?, FConfig.step?,
          FConfig.stepAction, machine1, replicate_true_succ]
      have hBC := FConfig.run?_compose hB hC
      have hBCD := FConfig.run?_compose hBC hCD
      have hBCDA := FConfig.run?_compose hBCD hA
      have hAll := FConfig.run?_compose hBCDA hFinal
      have hTime : (((1 + (2 * m + 3)) + 2) + (2 * m + 2)) + 1 =
          4 * (m + 2) + 1 := by omega
      simpa [hTime] using hAll

theorem machine1_cycles (k r : Nat) :
    FConfig.run? machine1 (mid1 k r) (cyclesTime1 r) =
      some (mid1 (k + r) 0) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
      have hFirst := machine1_cycle k r
      have hRest := ih (k + 1)
      have hAll := FConfig.run?_compose hFirst hRest
      have hIndex : k + 1 + r = k + (r + 1) := by omega
      simpa [cyclesTime1, hIndex] using hAll

theorem cyclesTime1_closed (r : Nat) :
    cyclesTime1 r = 2 * r * r + 3 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [cyclesTime1, ih, Nat.mul_add, Nat.add_mul,
        Nat.mul_one]
      omega

/-- The solid-interval phase for machine 1.  Relative to the head, exactly
the `2n` cells immediately to the right are marked. -/
def phase1F (n : Nat) : FConfig State :=
  ⟨A, [], false, List.replicate (2 * n) true⟩

def phase1 (n : Nat) : PConfig State Bool := (phase1F n).toPConfig

/-- A semantically invisible blank sentinel on both finite sides. -/
def phase1Seed (n : Nat) : FConfig State :=
  ⟨A, [false], false, List.replicate (2 * n) true ++ [false]⟩

theorem phase1Seed_toPConfig (n : Nat) :
    (phase1Seed n).toPConfig = phase1 n := by
  apply PConfig.ext
  · rfl
  · intro i
    cases i <;> rfl
  · rfl
  · intro i
    have hPad := congrFun
      (pad_append_false (List.replicate (2 * n) true)) i
    simpa [phase1Seed, phase1, phase1F, FConfig.toPConfig] using hPad

theorem machine1_enter (n : Nat) :
    FConfig.run? machine1 (phase1Seed n) 1 = some (mid1 0 n) := by
  cases n with
  | zero => rfl
  | succ n =>
      have hWidth :
          List.replicate (2 * (n + 1)) true =
            true :: List.replicate (2 * n + 1) true := by
        rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
          replicate_true_succ]
      simp [phase1Seed, mid1, hWidth, FConfig.run?, FConfig.step?,
        FConfig.stepAction, machine1]

theorem machine1_finish (n : Nat) :
    FConfig.run? machine1 (mid1 n 0) (n + 2) =
      some (phase1F (n + 1)) := by
  let beforeScan : FConfig State :=
    ⟨A, List.replicate n true ++ [false], true,
      List.replicate (n + 1) true⟩
  have hFirst : FConfig.run? machine1 (mid1 n 0) 1 =
      some beforeScan := by
    simp [mid1, beforeScan, FConfig.run?, FConfig.step?,
      FConfig.stepAction, machine1, replicate_true_succ]
  have hScan := machine1_scan_A_to_blank n []
    (List.replicate (n + 1) true)
  have hAll := FConfig.run?_compose hFirst hScan
  have hLists :
      List.replicate (n + 1) true ++ List.replicate (n + 1) true =
        List.replicate (2 * (n + 1)) true := by
    rw [replicate_true_append]
    apply congrArg (fun width => List.replicate width true)
    omega
  have hTime : 1 + (n + 1) = n + 2 := by omega
  rw [← hTime, hAll]
  exact congrArg some (congrArg
    (fun xs => (FConfig.mk A [] false xs : FConfig State)) hLists)

/-- Exact P1 macro: `P1(n) -> P1(n+1)` in `2n²+4n+3` steps. -/
theorem machine1_phase_step (n : Nat) :
    PTM.run? machine1 (phase1 n) (2 * n * n + 4 * n + 3) =
      some (phase1 (n + 1)) := by
  have hEnter := machine1_enter n
  have hCycles := machine1_cycles 0 n
  have hCycles' :
      FConfig.run? machine1 (mid1 0 n) (cyclesTime1 n) =
        some (mid1 n 0) := by
    simpa using hCycles
  have hFinish := machine1_finish n
  have hEC := FConfig.run?_compose hEnter hCycles'
  have hFinite := FConfig.run?_compose hEC hFinish
  have hTime : (1 + cyclesTime1 n) + (n + 2) =
      2 * n * n + 4 * n + 3 := by
    rw [cyclesTime1_closed]
    omega
  have hFinite' :
      FConfig.run? machine1 (phase1Seed n) (2 * n * n + 4 * n + 3) =
        some (phase1F (n + 1)) := by
    rw [← hTime]
    simpa using hFinite
  have hBridge := FConfig.run?_toPConfig machine1 (phase1Seed n)
    (2 * n * n + 4 * n + 3)
  rw [hFinite', phase1Seed_toPConfig] at hBridge
  exact hBridge.symm

def phaseTime1 : Nat -> Nat
  | 0 => 0
  | n + 1 => phaseTime1 n + (2 * n * n + 4 * n + 3)

theorem machine1_reaches_phase (n : Nat) :
    PTM.run? machine1 (PConfig.blank A false) (phaseTime1 n) =
      some (phase1 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [phaseTime1, ptm_run?_add, ih]
      exact machine1_phase_step n

theorem phaseTime1_large (n : Nat) : n ≤ phaseTime1 n := by
  induction n with
  | zero => simp [phaseTime1]
  | succ n ih =>
      simp only [phaseTime1]
      omega

/-- The first RepWL-only four-state machine runs forever. -/
theorem machine1_nonhalts : machine1.Nonhalts A false := by
  intro steps
  exact ptm_run?_prefix (phaseTime1_large steps)
    (machine1_reaches_phase steps)

/-! ## `Fin 4` export for table-search integration -/

def stateToFin : State -> Fin 4
  | A => 0
  | B => 1
  | C => 2
  | D => 3

def stateOfFin : Fin 4 -> State :=
  Fin.cases A (Fin.cases B (Fin.cases C (fun _ => D)))

/-- The two explicit state encodings are mutual inverses. -/
theorem stateOfFin_toFin (state : State) :
    stateOfFin (stateToFin state) = state := by
  cases state <;> rfl

theorem stateToFin_ofFin (state : Fin 4) :
    stateToFin (stateOfFin state) = state := by
  refine Fin.cases ?_ ?_ state
  · rfl
  · intro state3
    refine Fin.cases ?_ ?_ state3
    · rfl
    · intro state2
      refine Fin.cases ?_ ?_ state2
      · rfl
      · intro state1
        refine Fin.cases ?_ ?_ state1
        · rfl
        · intro impossible
          exact Fin.elim0 impossible

/-- Transport a named-state partial machine to the `Fin 4` state type used by
future lazy table search. -/
def toFinPTM (machine : PTM State Bool) : PTM (Fin 4) Bool :=
  fun state symbol =>
    (machine (stateOfFin state) symbol).map fun action =>
      action.map stateToFin id

def machine1Fin : PTM (Fin 4) Bool := toFinPTM machine1
def machine2Fin : PTM (Fin 4) Bool := toFinPTM machine2

theorem projects_toFin (machine : PTM State Bool) :
    PTM.Projects machine (toFinPTM machine) stateToFin id := by
  intro state symbol action hAction
  unfold toFinPTM
  rw [stateOfFin_toFin]
  simp only [id_eq, hAction, Option.map_some]

theorem machine1Fin_nonhalts : machine1Fin.Nonhalts (0 : Fin 4) false := by
  have h := (projects_toFin machine1).nonhalts machine1_nonhalts
  simpa [machine1Fin, stateToFin] using h

theorem machine2Fin_nonhalts : machine2Fin.Nonhalts (0 : Fin 4) false := by
  have h := (projects_toFin machine2).nonhalts machine2_nonhalts
  simpa [machine2Fin, stateToFin] using h

end Sporadic
end BB4
end BusyBeaver
end SetTheory
