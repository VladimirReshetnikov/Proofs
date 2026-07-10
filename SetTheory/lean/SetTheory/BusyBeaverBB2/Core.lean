/-
  BusyBeaverBB2/Core.lean

  A checked finite classification of two-state, two-symbol Rado machines.

  The finite computation in this file is only the final coverage check.  Every
  table classified as nonhalting carries one of four independently proved
  certificates: a translated configuration loop, a one-way blank escape, a
  closed three-cell local abstraction, or one of seven frontier-growth
  invariants (up to reflection).  Thus failure to halt during a bounded
  simulation is never itself used as evidence of nonhalting.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import SetTheory.BusyBeaverKnownValues

set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SetTheory
namespace BusyBeaver
namespace BB2

open KnownValues

private abbrev A : Fin 2 := 0
private abbrev B : Fin 2 := 1

/-! ## Small finite transition tables -/

instance : Fintype Move where
  elems := {Move.left, Move.right}
  complete move := by cases move <;> simp

private def actionEquiv (states : Nat) :
    Action states ≃ Bool × Move × Option (Fin states) where
  toFun action := (action.write, action.move, action.next)
  invFun data :=
    { write := data.1
      move := data.2.1
      next := data.2.2 }
  left_inv action := by cases action; rfl
  right_inv data := by rcases data with ⟨write, move, next⟩; rfl

instance (states : Nat) : Fintype (Action states) :=
  Fintype.ofEquiv (Bool × Move × Option (Fin states)) (actionEquiv states).symm

/-- A two-state machine assembled from its four transition-table entries. -/
def tableMachine (a0 a1 b0 b1 : Action 2) : Machine 2 where
  transition q bit :=
    if q = A then
      if bit then a1 else a0
    else
      if bit then b1 else b0

@[simp] theorem tableMachine_a0 (a0 a1 b0 b1 : Action 2) :
    (tableMachine a0 a1 b0 b1).transition A false = a0 := by
  simp [tableMachine]

@[simp] theorem tableMachine_a1 (a0 a1 b0 b1 : Action 2) :
    (tableMachine a0 a1 b0 b1).transition A true = a1 := by
  simp [tableMachine]

@[simp] theorem tableMachine_b0 (a0 a1 b0 b1 : Action 2) :
    (tableMachine a0 a1 b0 b1).transition B false = b0 := by
  simp [tableMachine]

@[simp] theorem tableMachine_b1 (a0 a1 b0 b1 : Action 2) :
    (tableMachine a0 a1 b0 b1).transition B true = b1 := by
  simp [tableMachine]

theorem machine_eq_tableMachine (M : Machine 2) :
    M = tableMachine (M.transition A false) (M.transition A true)
      (M.transition B false) (M.transition B true) := by
  cases M with
  | mk transition =>
      congr
      funext q bit
      fin_cases q <;> cases bit <;> rfl

/-! ## Halt stabilization -/

theorem run_add_of_halted {states : Nat} (M : Machine states) {h : Nat}
    (hHalted : (M.run h).state = none) :
    ∀ k, M.run (h + k) = M.run h
  | 0 => by simp
  | k + 1 => by
      rw [Nat.add_succ, Machine.run]
      rw [run_add_of_halted M hHalted k]
      simp [Machine.step, hHalted]

theorem run_eq_of_halted {states : Nat} (M : Machine states) {i j : Nat}
    (hi : (M.run i).state = none) (hj : (M.run j).state = none) :
    M.run i = M.run j := by
  rcases le_total i j with hij | hji
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact (run_add_of_halted M hi k).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact run_add_of_halted M hj k

/-- The bounded positive certificate: by step six the machine has halted with
at most four marked cells. -/
def SafeAtSix (M : Machine 2) : Prop :=
  (M.run 6).state = none ∧ (M.run 6).tape.length ≤ 4

instance (M : Machine 2) : Decidable (SafeAtSix M) := by
  unfold SafeAtSix
  infer_instance

theorem SafeAtSix.score_le_four {M : Machine 2} (hSafe : SafeAtSix M)
    {score : Nat} (hHalt : M.HaltsWithScore score) : score ≤ 4 := by
  rcases hHalt with ⟨t, hState, hScore⟩
  have hEq := run_eq_of_halted M hState hSafe.1
  calc
    score = (M.run t).tape.length := hScore.symm
    _ = (M.run 6).tape.length := congrArg (fun cfg => cfg.tape.length) hEq
    _ ≤ 4 := hSafe.2

/-! ## Translated-loop certificates -/

def ShiftLoopAt (M : Machine 2) (start period : Nat) : Prop :=
  0 < period ∧
  M.run (start + period) =
    (M.run start).shift ((M.run (start + period)).head - (M.run start).head) ∧
  ∀ t : Fin (start + period), (M.run t).state ≠ none

instance (M : Machine 2) (start period : Nat) :
    Decidable (ShiftLoopAt M start period) := by
  unfold ShiftLoopAt
  infer_instance

theorem ShiftLoopAt.not_halts {M : Machine 2} {start period : Nat}
    (h : ShiftLoopAt M start period) {score : Nat} :
    ¬ M.HaltsWithScore score := by
  apply M.not_haltsWithScore_of_shift_loop_from_run h.1
  · rw [← M.run_add_eq_runFrom start period]
    exact h.2.1
  · intro r hr
    rw [← M.run_add_eq_runFrom start r]
    exact h.2.2 ⟨start + r, by omega⟩
  · intro t ht
    exact h.2.2 ⟨t, by omega⟩

/-- All loop witnesses needed by the finite classification occur within these
small bounds: start at most six, period at most eight. -/
def HasShortShiftLoop (M : Machine 2) : Prop :=
  ∃ start : Fin 7, ∃ period : Fin 8, ShiftLoopAt M start (period + 1)

instance (M : Machine 2) : Decidable (HasShortShiftLoop M) := by
  unfold HasShortShiftLoop
  infer_instance

theorem HasShortShiftLoop.not_halts {M : Machine 2} (h : HasShortShiftLoop M)
    {score : Nat} : ¬ M.HaltsWithScore score := by
  rcases h with ⟨start, period, hLoop⟩
  exact hLoop.not_halts

/-! ## One-way blank escapes -/

inductive Direction where
  | left
  | right
  deriving DecidableEq

instance : Fintype Direction where
  elems := {Direction.left, Direction.right}
  complete direction := by cases direction <;> simp

def Direction.move : Direction -> Move
  | .left => Move.left
  | .right => Move.right

def Behind (direction : Direction) (cfg : Config 2) : Prop :=
  match direction with
  | .left => ∀ p, p ∈ cfg.tape -> cfg.head < p
  | .right => ∀ p, p ∈ cfg.tape -> p < cfg.head

def BlankClosed (M : Machine 2) (direction : Direction)
    (states : Finset (Fin 2)) : Prop :=
  ∀ q, q ∈ states ->
    (M.transition q false).move = direction.move ∧
    ∃ next, (M.transition q false).next = some next ∧ next ∈ states

instance (M : Machine 2) (direction : Direction) (states : Finset (Fin 2)) :
    Decidable (BlankClosed M direction states) := by
  unfold BlankClosed
  infer_instance

def EscapesAt (M : Machine 2) (direction : Direction)
    (states : Finset (Fin 2)) (start : Nat) : Prop :=
  (∃ q, (M.run start).state = some q ∧ q ∈ states) ∧
    Behind direction (M.run start) ∧
    BlankClosed M direction states ∧
    ∀ t : Fin start, (M.run t).state ≠ none

instance (direction : Direction) (cfg : Config 2) :
    Decidable (Behind direction cfg) := by
  cases direction
  · exact decidable_of_iff (cfg.tape.Forall (fun p => cfg.head < p))
      List.forall_iff_forall_mem
  · exact decidable_of_iff (cfg.tape.Forall (fun p => p < cfg.head))
      List.forall_iff_forall_mem

instance (M : Machine 2) (direction : Direction) (states : Finset (Fin 2))
    (start : Nat) : Decidable (EscapesAt M direction states start) := by
  unfold EscapesAt
  infer_instance

private theorem behind_head_not_mem {direction : Direction} {cfg : Config 2}
    (h : Behind direction cfg) : cfg.head ∉ cfg.tape := by
  intro hmem
  cases direction
  · exact (Int.lt_irrefl _ (h cfg.head hmem))
  · exact (Int.lt_irrefl _ (h cfg.head hmem))

private theorem mem_write_true_iff (tape : Tape) (pos p : Int) :
    p ∈ Tape.write tape pos true ↔ p = pos ∨ p ∈ tape := by
  by_cases h : pos ∈ tape
  · simp [Tape.write, h]
    intro hp
    subst p
    exact h
  · simp [Tape.write, h]

private theorem mem_write_false_iff (tape : Tape) (pos p : Int) :
    p ∈ Tape.write tape pos false ↔ p ∈ tape ∧ p ≠ pos := by
  simp [Tape.write]

private theorem behind_step {M : Machine 2} {direction : Direction}
    {states : Finset (Fin 2)} {cfg : Config 2} {q next : Fin 2}
    (hState : cfg.state = some q) (hBehind : Behind direction cfg)
    (hClosed : BlankClosed M direction states) (hq : q ∈ states)
    (_hNext : (M.transition q false).next = some next) :
    Behind direction (M.step cfg) := by
  have hHeadNot : cfg.head ∉ cfg.tape := behind_head_not_mem hBehind
  have hRead : Tape.read cfg.tape cfg.head = false := by
    simp [Tape.read, hHeadNot]
  have hMove := (hClosed q hq).1
  cases direction with
  | left =>
      simp only [Behind] at hBehind ⊢
      intro p hp
      simp only [Machine.step, hState, hRead] at hp ⊢
      simp only [Direction.move] at hMove
      rw [hMove]
      simp only [Move.apply]
      cases hWrite : (M.transition q false).write
      · simp only [hWrite] at hp
        have hp' := (mem_write_false_iff cfg.tape cfg.head p).mp hp
        exact Int.lt_trans (by omega) (hBehind p hp'.1)
      · simp only [hWrite] at hp
        have hp' := (mem_write_true_iff cfg.tape cfg.head p).mp hp
        rcases hp' with hp' | hp'
        · subst p
          omega
        · exact Int.lt_trans (by omega) (hBehind p hp')
  | right =>
      simp only [Behind] at hBehind ⊢
      intro p hp
      simp only [Machine.step, hState, hRead] at hp ⊢
      simp only [Direction.move] at hMove
      rw [hMove]
      simp only [Move.apply]
      cases hWrite : (M.transition q false).write
      · simp only [hWrite] at hp
        have hp' := (mem_write_false_iff cfg.tape cfg.head p).mp hp
        exact Int.lt_trans (hBehind p hp'.1) (by omega)
      · simp only [hWrite] at hp
        have hp' := (mem_write_true_iff cfg.tape cfg.head p).mp hp
        rcases hp' with hp' | hp'
        · subst p
          omega
        · exact Int.lt_trans (hBehind p hp') (by omega)

private theorem EscapesAt.runFrom_invariant {M : Machine 2} {direction : Direction}
    {states : Finset (Fin 2)} {start : Nat}
    (hEscape : EscapesAt M direction states start) :
    ∀ t, ∃ q,
      (M.runFrom (M.run start) t).state = some q ∧ q ∈ states ∧
      Behind direction (M.runFrom (M.run start) t)
  | 0 => by
      rcases hEscape.1 with ⟨q, hState, hq⟩
      exact ⟨q, by simpa [Machine.runFrom] using hState, hq,
        by simpa [Machine.runFrom] using hEscape.2.1⟩
  | t + 1 => by
      rcases hEscape.runFrom_invariant t with ⟨q, hState, hq, hBehind⟩
      rcases hEscape.2.2.1 q hq with ⟨hMove, next, hNext, hnextMem⟩
      have hRead :
          Tape.read (M.runFrom (M.run start) t).tape
            (M.runFrom (M.run start) t).head = false := by
        simp [Tape.read, behind_head_not_mem hBehind]
      refine ⟨next, ?_, hnextMem, ?_⟩
      · simp [Machine.runFrom, Machine.step, hState, hRead, hNext]
      · rw [Machine.runFrom]
        exact behind_step hState hBehind hEscape.2.2.1 hq hNext

theorem EscapesAt.runFrom_ne_none {M : Machine 2} {direction : Direction}
    {states : Finset (Fin 2)} {start : Nat}
    (hEscape : EscapesAt M direction states start) :
    ∀ t, (M.runFrom (M.run start) t).state ≠ none := by
  intro t hNone
  rcases hEscape.runFrom_invariant t with ⟨q, hState, _⟩
  rw [hNone] at hState
  contradiction

theorem EscapesAt.not_halts {M : Machine 2} {direction : Direction}
    {states : Finset (Fin 2)} {start : Nat}
    (hEscape : EscapesAt M direction states start) {score : Nat} :
    ¬ M.HaltsWithScore score := by
  intro hHalt
  rcases hHalt with ⟨t, hState, _⟩
  by_cases ht : t < start
  · exact hEscape.2.2.2 ⟨t, ht⟩ hState
  · have hstart : start ≤ t := Nat.le_of_not_gt ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hstart
    rw [M.run_add_eq_runFrom] at hState
    exact hEscape.runFrom_ne_none k hState

private def stateSet : Fin 3 -> Finset (Fin 2)
  | ⟨0, _⟩ => {A}
  | ⟨1, _⟩ => {B}
  | _ => {A, B}

def HasShortBlankEscape (M : Machine 2) : Prop :=
  ∃ direction : Direction, ∃ states : Fin 3, ∃ start : Fin 7,
    EscapesAt M direction (stateSet states) start

instance (M : Machine 2) : Decidable (HasShortBlankEscape M) := by
  unfold HasShortBlankEscape
  infer_instance

theorem HasShortBlankEscape.not_halts {M : Machine 2}
    (h : HasShortBlankEscape M) {score : Nat} : ¬ M.HaltsWithScore score := by
  rcases h with ⟨direction, states, start, hEscape⟩
  exact hEscape.not_halts

/-! ## Closed three-cell local abstractions -/

/-- State together with the tape symbols immediately left of, under, and
immediately right of the head. -/
abbrev Local := Fin 2 × Bool × Bool × Bool

private def localState (view : Local) : Fin 2 := view.1
private def localLeft (view : Local) : Bool := view.2.1
private def localCenter (view : Local) : Bool := view.2.2.1
private def localRight (view : Local) : Bool := view.2.2.2

private def localSnapshot (cfg : Config 2) (q : Fin 2) : Local :=
  (q, Tape.read cfg.tape (cfg.head - 1), Tape.read cfg.tape cfg.head,
    Tape.read cfg.tape (cfg.head + 1))

private def initialLocal : Local := (A, false, false, false)

/-- Abstract successors expose one unknown boundary cell.  Both Boolean
possibilities are retained, so this is an over-approximation of every concrete
step, not a guessed continuation. -/
def localSuccessors (M : Machine 2) (view : Local) : Finset Local :=
  let action := M.transition (localState view) (localCenter view)
  match action.next with
  | none => ∅
  | some next =>
      match action.move with
      | Move.left =>
          {(next, false, localLeft view, action.write),
            (next, true, localLeft view, action.write)}
      | Move.right =>
          {(next, action.write, localRight view, false),
            (next, action.write, localRight view, true)}

def expandLocals (M : Machine 2) (locals : Finset Local) : Finset Local :=
  locals ∪ locals.biUnion (localSuccessors M)

private def localClosureFrom (M : Machine 2) : Nat -> Finset Local
  | 0 => {initialLocal}
  | n + 1 => expandLocals M (localClosureFrom M n)

/-- Sixteen rounds suffice for the sixteen-element abstract state space.  The
certificate nevertheless checks closure explicitly, so soundness does not
depend on that cardinality observation. -/
def localClosure (M : Machine 2) : Finset Local :=
  localClosureFrom M 16

def ClosedLocalInvariant (M : Machine 2) (locals : Finset Local) : Prop :=
  initialLocal ∈ locals ∧
  ∀ view, view ∈ locals ->
    (M.transition (localState view) (localCenter view)).next ≠ none ∧
    localSuccessors M view ⊆ locals

instance (M : Machine 2) (locals : Finset Local) :
    Decidable (ClosedLocalInvariant M locals) := by
  unfold ClosedLocalInvariant
  infer_instance

def HasClosedLocalInvariant (M : Machine 2) : Prop :=
  ClosedLocalInvariant M (localClosure M)

instance (M : Machine 2) : Decidable (HasClosedLocalInvariant M) := by
  unfold HasClosedLocalInvariant
  infer_instance

private theorem localSnapshot_initial :
    localSnapshot (initial 2) A = initialLocal := by
  decide

private theorem localSnapshot_step_mem_successors {M : Machine 2}
    {cfg : Config 2} {q next : Fin 2}
    (hState : cfg.state = some q)
    (hNext : (M.transition q (Tape.read cfg.tape cfg.head)).next = some next) :
    localSnapshot (M.step cfg) next ∈ localSuccessors M (localSnapshot cfg q) := by
  have hLeftNe : cfg.head - 1 ≠ cfg.head := by omega
  have hRightNe : cfg.head + 1 ≠ cfg.head := by omega
  have hFarLeftNe : cfg.head - 1 - 1 ≠ cfg.head := by omega
  have hFarRightNe : cfg.head + 1 + 1 ≠ cfg.head := by omega
  cases hMove : (M.transition q (Tape.read cfg.tape cfg.head)).move
  · cases hFar : Tape.read cfg.tape (cfg.head - 1 - 1) <;>
      simp [localSnapshot, localSuccessors, localState, localLeft, localCenter,
        localRight, Machine.step, hState, hNext, hMove, Move.apply,
        Tape.read_write_same, Tape.read_write_of_ne, hLeftNe, hFarLeftNe, hFar]
  · cases hFar : Tape.read cfg.tape (cfg.head + 1 + 1) <;>
      simp [localSnapshot, localSuccessors, localState, localLeft, localCenter,
        localRight, Machine.step, hState, hNext, hMove, Move.apply,
        Tape.read_write_same, Tape.read_write_of_ne, hRightNe, hFarRightNe, hFar]

private theorem ClosedLocalInvariant.run_invariant {M : Machine 2}
    {locals : Finset Local} (hClosed : ClosedLocalInvariant M locals) :
    ∀ t, ∃ q, (M.run t).state = some q ∧ localSnapshot (M.run t) q ∈ locals
  | 0 => by
      refine ⟨A, rfl, ?_⟩
      simpa [Machine.run, localSnapshot_initial] using hClosed.1
  | t + 1 => by
      rcases hClosed.run_invariant t with ⟨q, hState, hLocal⟩
      have hAt := hClosed.2 (localSnapshot (M.run t) q) hLocal
      have hCenter :
          localCenter (localSnapshot (M.run t) q) =
            Tape.read (M.run t).tape (M.run t).head := rfl
      rw [hCenter] at hAt
      rcases hActionNext :
          (M.transition q (Tape.read (M.run t).tape (M.run t).head)).next with _ | next
      · exact False.elim (hAt.1 hActionNext)
      · refine ⟨next, ?_, ?_⟩
        · simp [Machine.run, Machine.step, hState, hActionNext]
        · apply hAt.2
          exact localSnapshot_step_mem_successors hState hActionNext

theorem HasClosedLocalInvariant.not_halts {M : Machine 2}
    (h : HasClosedLocalInvariant M) {score : Nat} : ¬ M.HaltsWithScore score := by
  rintro ⟨t, hState, _⟩
  rcases h.run_invariant t with ⟨q, hSome, _⟩
  rw [hState] at hSome
  contradiction

/-! ## Frontier-growth certificates -/

theorem runFrom_ne_none_of_macro_invariant {states : Nat} (M : Machine states)
    (Inv : Config states -> Prop) {period : Nat} (hPeriod : 0 < period)
    (hActive : ∀ cfg, Inv cfg -> ∀ r, r < period ->
      (M.runFrom cfg r).state ≠ none)
    (hPreserve : ∀ cfg, Inv cfg -> Inv (M.runFrom cfg period)) :
    ∀ cfg, Inv cfg -> ∀ t, (M.runFrom cfg t).state ≠ none := by
  intro cfg hInv t
  induction t using Nat.strong_induction_on generalizing cfg with
  | h t ih =>
      by_cases ht : t < period
      · exact hActive cfg hInv t ht
      · have hle : period ≤ t := Nat.le_of_not_gt ht
        let k := t - period
        have hk : k < t := by dsimp [k]; omega
        have htEq : period + k = t := by dsimp [k]; omega
        rw [← htEq, M.runFrom_add]
        exact ih k hk (M.runFrom cfg period) (hPreserve cfg hInv)

theorem not_haltsWithScore_of_macro_invariant_from_run {states score : Nat}
    (M : Machine states) (Inv : Config states -> Prop) {start period : Nat}
    (hPeriod : 0 < period)
    (hActive : ∀ cfg, Inv cfg -> ∀ r, r < period ->
      (M.runFrom cfg r).state ≠ none)
    (hPreserve : ∀ cfg, Inv cfg -> Inv (M.runFrom cfg period))
    (hStart : Inv (M.run start))
    (hPrefix : ∀ t, t < start -> (M.run t).state ≠ none) :
    ¬ M.HaltsWithScore score := by
  have hNever := runFrom_ne_none_of_macro_invariant M Inv hPeriod hActive hPreserve
    (M.run start) hStart
  rintro ⟨t, hState, _⟩
  by_cases ht : t < start
  · exact hPrefix t ht hState
  · have hle : start ≤ t := Nat.le_of_not_gt ht
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [M.run_add_eq_runFrom] at hState
    exact hNever k hState

def LeftFrontier (cfg : Config 2) : Prop :=
  cfg.state = some A ∧ ∀ p, p ∈ cfg.tape -> cfg.head < p

def RightFrontier (cfg : Config 2) : Prop :=
  cfg.state = some A ∧ ∀ p, p ∈ cfg.tape -> p < cfg.head

def RightGapFrontier (cfg : Config 2) : Prop :=
  cfg.state = some A ∧ ∀ p, p ∈ cfg.tape -> p < cfg.head - 1

def RightMarkedFrontier (cfg : Config 2) : Prop :=
  RightFrontier cfg ∧ cfg.head - 1 ∈ cfg.tape

private theorem leftFrontier_not_mem {cfg : Config 2} (h : LeftFrontier cfg)
    {p : Int} (hp : p ≤ cfg.head) : p ∉ cfg.tape := by
  intro hmem
  have := h.2 p hmem
  omega

private theorem rightFrontier_not_mem {cfg : Config 2} (h : RightFrontier cfg)
    {p : Int} (hp : cfg.head ≤ p) : p ∉ cfg.tape := by
  intro hmem
  have := h.2 p hmem
  omega

private theorem rightGapFrontier_not_mem {cfg : Config 2} (h : RightGapFrontier cfg)
    {p : Int} (hp : cfg.head - 1 ≤ p) : p ∉ cfg.tape := by
  intro hmem
  have := h.2 p hmem
  omega

def FrontierPattern1 (M : Machine 2) : Prop :=
  M.transition A false = go false Move.left B ∧
  M.transition B false = go true Move.right A ∧
  M.transition B true = go true Move.left A

private theorem frontierPattern1_macro {M : Machine 2}
    (hPattern : FrontierPattern1 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) :
    M.runFrom cfg 4 =
      { state := some A
        head := cfg.head - 2
        tape := Tape.write cfg.tape (cfg.head - 1) true } := by
  have hHead : cfg.head ∉ cfg.tape := by
    intro hmem
    exact (Int.lt_irrefl _ (hInv.2 cfg.head hmem))
  have hLeft : cfg.head - 1 ∉ cfg.tape := by
    intro hmem
    have := hInv.2 (cfg.head - 1) hmem
    omega
  have hReadHead : Tape.read cfg.tape cfg.head = false := by
    simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by
    simp [Tape.read, hLeft]
  have hWriteHead : Tape.write cfg.tape cfg.head false = cfg.tape := by
    simpa [hReadHead] using Tape.write_read_self cfg.tape cfg.head
  have hReadAfterAtHead :
      Tape.read (Tape.write cfg.tape (cfg.head - 1) true) cfg.head = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadHead
    · omega
  have hWriteAfterAtHead :
      Tape.write (Tape.write cfg.tape (cfg.head - 1) true) cfg.head false =
        Tape.write cfg.tape (cfg.head - 1) true := by
    simpa [hReadAfterAtHead] using
      Tape.write_read_self (Tape.write cfg.tape (cfg.head - 1) true) cfg.head
  have hWriteLeftAgain :
      Tape.write (Tape.write cfg.tape (cfg.head - 1) true) (cfg.head - 1) true =
        Tape.write cfg.tape (cfg.head - 1) true := by
    simpa using Tape.write_read_self (Tape.write cfg.tape (cfg.head - 1) true)
      (cfg.head - 1)
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
    hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
    hWriteHead, hReadAfterAtHead, hWriteAfterAtHead, hWriteLeftAgain,
    Tape.read_write_same] <;> omega

private theorem frontierPattern1_preserves {M : Machine 2}
    (hPattern : FrontierPattern1 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) : LeftFrontier (M.runFrom cfg 4) := by
  rw [frontierPattern1_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write cfg.tape (cfg.head - 1) true -> cfg.head - 2 < p
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff cfg.tape (cfg.head - 1) p).mp hp with hp | hp
    · subst p
      omega
    · have := hInv.2 p hp
      omega

private theorem frontierPattern1_active {M : Machine 2}
    (hPattern : FrontierPattern1 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) {r : Nat} (hr : r < 4) :
    (M.runFrom cfg r).state ≠ none := by
  have hHead : cfg.head ∉ cfg.tape := by
    intro hmem
    exact (Int.lt_irrefl _ (hInv.2 cfg.head hmem))
  have hLeft : cfg.head - 1 ∉ cfg.tape := by
    intro hmem
    have := hInv.2 (cfg.head - 1) hmem
    omega
  have hReadHead : Tape.read cfg.tape cfg.head = false := by
    simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by
    simp [Tape.read, hLeft]
  have hWriteHead : Tape.write cfg.tape cfg.head false = cfg.tape := by
    simpa [hReadHead] using Tape.write_read_self cfg.tape cfg.head
  have hReadAfterAtHead :
      Tape.read (Tape.write cfg.tape (cfg.head - 1) true) cfg.head = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadHead
    · omega
  have hWriteAfterAtHead :
      Tape.write (Tape.write cfg.tape (cfg.head - 1) true) cfg.head false =
        Tape.write cfg.tape (cfg.head - 1) true := by
    simpa [hReadAfterAtHead] using
      Tape.write_read_self (Tape.write cfg.tape (cfg.head - 1) true) cfg.head
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hrCases with rfl | rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
      hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
      hWriteHead, hReadAfterAtHead, hWriteAfterAtHead, Tape.read_write_same]

theorem FrontierPattern1.not_halts {M : Machine 2}
    (hPattern : FrontierPattern1 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : LeftFrontier (initial 2) := by
    simp [LeftFrontier, initial, startState]
  have hNever := runFrom_ne_none_of_macro_invariant M LeftFrontier (by decide)
    (fun _cfg hInv r hr => frontierPattern1_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern1_preserves hPattern hInv)
    (initial 2) hInitial
  rintro ⟨t, hState, _⟩
  have hEq : M.run t = M.runFrom (initial 2) t := by
    simpa [Machine.run] using M.run_add_eq_runFrom 0 t
  apply hNever t
  rw [← hEq]
  exact hState

def FrontierPattern2 (M : Machine 2) : Prop :=
  M.transition A false = go false Move.left B ∧
  M.transition B false = go true Move.right A ∧
  M.transition B true = go true Move.right B

private theorem frontierPattern2_macro {M : Machine 2}
    (hPattern : FrontierPattern2 M) {cfg : Config 2}
    (hInv : RightMarkedFrontier cfg) :
    M.runFrom cfg 3 =
      { state := some A
        head := cfg.head + 1
        tape := Tape.write cfg.tape cfg.head true } := by
  have hHead := rightFrontier_not_mem hInv.1 (p := cfg.head) (by omega)
  have hRight := rightFrontier_not_mem hInv.1 (p := cfg.head + 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by
    simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = true := by
    simp [Tape.read, hInv.2]
  have hWriteHead : Tape.write cfg.tape cfg.head false = cfg.tape := by
    simpa [hReadHead] using Tape.write_read_self cfg.tape cfg.head
  have hWriteLeft : Tape.write cfg.tape (cfg.head - 1) true = cfg.tape := by
    simpa [hReadLeft] using Tape.write_read_self cfg.tape (cfg.head - 1)
  simp [Machine.runFrom, Machine.step, hInv.1.1, hReadHead, hReadLeft,
    hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
    hWriteHead, hWriteLeft, Tape.read_write_same] <;> omega

private theorem frontierPattern2_preserves {M : Machine 2}
    (hPattern : FrontierPattern2 M) {cfg : Config 2}
    (hInv : RightMarkedFrontier cfg) : RightMarkedFrontier (M.runFrom cfg 3) := by
  rw [frontierPattern2_macro hPattern hInv]
  constructor
  · change (some A = some A) ∧
      ∀ p, p ∈ Tape.write cfg.tape cfg.head true -> p < cfg.head + 1
    constructor
    · rfl
    · intro p hp
      rcases (mem_write_true_iff cfg.tape cfg.head p).mp hp with hp | hp
      · subst p; omega
      · exact Int.lt_trans (hInv.1.2 p hp) (by omega)
  · have hm : cfg.head ∈ Tape.write cfg.tape cfg.head true :=
      (mem_write_true_iff cfg.tape cfg.head cfg.head).mpr (Or.inl rfl)
    change cfg.head + 1 - 1 ∈ Tape.write cfg.tape cfg.head true
    convert hm using 1 <;> omega

private theorem frontierPattern2_active {M : Machine 2}
    (hPattern : FrontierPattern2 M) {cfg : Config 2}
    (hInv : RightMarkedFrontier cfg) {r : Nat} (hr : r < 3) :
    (M.runFrom cfg r).state ≠ none := by
  have hHead := rightFrontier_not_mem hInv.1 (p := cfg.head) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by
    simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = true := by
    simp [Tape.read, hInv.2]
  have hWriteHead : Tape.write cfg.tape cfg.head false = cfg.tape := by
    simpa [hReadHead] using Tape.write_read_self cfg.tape cfg.head
  have hWriteLeft : Tape.write cfg.tape (cfg.head - 1) true = cfg.tape := by
    simpa [hReadLeft] using Tape.write_read_self cfg.tape (cfg.head - 1)
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrCases with rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1.1, hReadHead, hReadLeft,
      hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
      hWriteHead, hWriteLeft, Tape.read_write_same]

private theorem frontierPattern2_start {M : Machine 2}
    (hPattern : FrontierPattern2 M) : RightMarkedFrontier (M.run 2) := by
  change RightMarkedFrontier (M.step (M.step (initial 2)))
  simp [RightMarkedFrontier, RightFrontier, Machine.step, initial, startState,
    Tape.read, Tape.write, hPattern.1, hPattern.2.1, go, Move.apply]

private theorem frontierPattern2_prefix {M : Machine 2}
    (hPattern : FrontierPattern2 M) {t : Nat} (ht : t < 2) :
    (M.run t).state ≠ none := by
  have htCases : t = 0 ∨ t = 1 := by omega
  rcases htCases with rfl | rfl <;>
    simp [Machine.run, Machine.step, initial, startState, Tape.read, Tape.write,
      hPattern.1, go, Move.apply]

theorem FrontierPattern2.not_halts {M : Machine 2}
    (hPattern : FrontierPattern2 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  exact not_haltsWithScore_of_macro_invariant_from_run M RightMarkedFrontier
    (by decide)
    (fun _cfg hInv r hr => frontierPattern2_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern2_preserves hPattern hInv)
    (frontierPattern2_start hPattern)
    (fun _t ht => frontierPattern2_prefix hPattern ht)

def FrontierPattern3 (M : Machine 2) : Prop :=
  M.transition A false = go true Move.left B ∧
  M.transition B false = go false Move.right B ∧
  M.transition B true = go true Move.left A

private theorem frontierPattern3_macro {M : Machine 2}
    (hPattern : FrontierPattern3 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) :
    M.runFrom cfg 3 =
      { state := some A
        head := cfg.head - 1
        tape := Tape.write cfg.tape cfg.head true } := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadWritten : Tape.read (Tape.write cfg.tape cfg.head true) cfg.head = true :=
    Tape.read_write_same _ _ _
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using
      Tape.write_read_self (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hWriteHeadAgain :
      Tape.write (Tape.write cfg.tape cfg.head true) cfg.head true =
        Tape.write cfg.tape cfg.head true := by
    simpa using Tape.write_read_self (Tape.write cfg.tape cfg.head true) cfg.head
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
    hReadWritten, hReadWrittenLeft, hWriteWrittenLeft, hWriteHeadAgain,
    hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
    Tape.read_write_same] <;> omega

private theorem frontierPattern3_preserves {M : Machine 2}
    (hPattern : FrontierPattern3 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) : LeftFrontier (M.runFrom cfg 3) := by
  rw [frontierPattern3_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write cfg.tape cfg.head true -> cfg.head - 1 < p
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff cfg.tape cfg.head p).mp hp with hp | hp
    · subst p; omega
    · exact Int.lt_trans (by omega) (hInv.2 p hp)

private theorem frontierPattern3_active {M : Machine 2}
    (hPattern : FrontierPattern3 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) {r : Nat} (hr : r < 3) :
    (M.runFrom cfg r).state ≠ none := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using
      Tape.write_read_self (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrCases with rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
      hReadWrittenLeft, hWriteWrittenLeft, hPattern.1, hPattern.2.1,
      hPattern.2.2, go, Move.apply, Tape.read_write_same]

theorem FrontierPattern3.not_halts {M : Machine 2}
    (hPattern : FrontierPattern3 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : LeftFrontier (M.run 0) := by
    simp [Machine.run, LeftFrontier, initial, startState]
  exact not_haltsWithScore_of_macro_invariant_from_run M LeftFrontier
    (start := 0) (by decide)
    (fun _cfg hInv r hr => frontierPattern3_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern3_preserves hPattern hInv)
    hInitial (by omega)

def FrontierPattern5 (M : Machine 2) : Prop :=
  M.transition A false = go true Move.left B ∧
  M.transition A true = go true Move.left A ∧
  M.transition B false = go false Move.right A

private theorem frontierPattern5_macro {M : Machine 2}
    (hPattern : FrontierPattern5 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) :
    M.runFrom cfg 3 =
      { state := some A
        head := cfg.head - 1
        tape := Tape.write cfg.tape cfg.head true } := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using
      Tape.write_read_self (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hWriteHeadAgain :
      Tape.write (Tape.write cfg.tape cfg.head true) cfg.head true =
        Tape.write cfg.tape cfg.head true := by
    simpa using Tape.write_read_self (Tape.write cfg.tape cfg.head true) cfg.head
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
    hReadWrittenLeft, hWriteWrittenLeft, hWriteHeadAgain,
    hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
    Tape.read_write_same] <;> omega

private theorem frontierPattern5_preserves {M : Machine 2}
    (hPattern : FrontierPattern5 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) : LeftFrontier (M.runFrom cfg 3) := by
  rw [frontierPattern5_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write cfg.tape cfg.head true -> cfg.head - 1 < p
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff cfg.tape cfg.head p).mp hp with hp | hp
    · subst p; omega
    · exact Int.lt_trans (by omega) (hInv.2 p hp)

private theorem frontierPattern5_active {M : Machine 2}
    (hPattern : FrontierPattern5 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) {r : Nat} (hr : r < 3) :
    (M.runFrom cfg r).state ≠ none := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using
      Tape.write_read_self (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrCases with rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
      hReadWrittenLeft, hWriteWrittenLeft, hPattern.1, hPattern.2.1,
      hPattern.2.2, go, Move.apply, Tape.read_write_same]

theorem FrontierPattern5.not_halts {M : Machine 2}
    (hPattern : FrontierPattern5 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : LeftFrontier (M.run 0) := by
    simp [Machine.run, LeftFrontier, initial, startState]
  exact not_haltsWithScore_of_macro_invariant_from_run M LeftFrontier
    (start := 0) (by decide)
    (fun _cfg hInv r hr => frontierPattern5_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern5_preserves hPattern hInv)
    hInitial (by omega)

def FrontierPattern4 (M : Machine 2) : Prop :=
  M.transition A false = go true Move.left B ∧
  M.transition B false = go true Move.right B ∧
  M.transition B true = go false Move.right A

private theorem frontierPattern4_macro {M : Machine 2}
    (hPattern : FrontierPattern4 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) :
    M.runFrom cfg 3 =
      { state := some A
        head := cfg.head + 1
        tape := Tape.write cfg.tape (cfg.head - 1) true } := by
  have hLeft := rightGapFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hHead := rightGapFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadAfterLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hReadAfterBoth :
      Tape.read (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head = true := by
    rw [Tape.read_write_of_ne]
    · exact Tape.read_write_same _ _ _
    · omega
  have hFinalTape :
      Tape.write (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head false =
        Tape.write cfg.tape (cfg.head - 1) true := by
    simp [Tape.write, hHead, hLeft]
    intro a ha heq
    exact hHead (heq ▸ ha)
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
    hReadAfterLeft, hReadAfterBoth, hFinalTape, hPattern.1, hPattern.2.1,
    hPattern.2.2, go, Move.apply, Tape.read_write_same] <;> omega

private theorem frontierPattern4_preserves {M : Machine 2}
    (hPattern : FrontierPattern4 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) : RightGapFrontier (M.runFrom cfg 3) := by
  rw [frontierPattern4_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write cfg.tape (cfg.head - 1) true ->
      p < cfg.head + 1 - 1
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff cfg.tape (cfg.head - 1) p).mp hp with hp | hp
    · subst p; omega
    · have := hInv.2 p hp
      omega

private theorem frontierPattern4_active {M : Machine 2}
    (hPattern : FrontierPattern4 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) {r : Nat} (hr : r < 3) :
    (M.runFrom cfg r).state ≠ none := by
  have hLeft := rightGapFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hHead := rightGapFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadAfterLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrCases with rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
      hReadAfterLeft, hPattern.1, hPattern.2.1, hPattern.2.2,
      go, Move.apply, Tape.read_write_same]

theorem FrontierPattern4.not_halts {M : Machine 2}
    (hPattern : FrontierPattern4 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : RightGapFrontier (M.run 0) := by
    simp [Machine.run, RightGapFrontier, initial, startState]
  exact not_haltsWithScore_of_macro_invariant_from_run M RightGapFrontier
    (start := 0) (by decide)
    (fun _cfg hInv r hr => frontierPattern4_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern4_preserves hPattern hInv)
    hInitial (by omega)

def FrontierPattern6 (M : Machine 2) : Prop :=
  M.transition A false = go true Move.left B ∧
  M.transition A true = go true Move.left A ∧
  M.transition B false = go true Move.right A

private theorem frontierPattern6_macro {M : Machine 2}
    (hPattern : FrontierPattern6 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) :
    M.runFrom cfg 4 =
      { state := some A
        head := cfg.head - 2
        tape := Tape.write (Tape.write cfg.tape cfg.head true)
          (cfg.head - 1) true } := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadAfterLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hReadBothHead :
      Tape.read (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head = true := by
    rw [Tape.read_write_of_ne]
    · exact Tape.read_write_same _ _ _
    · omega
  have hReadBothLeft :
      Tape.read (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) (cfg.head - 1) = true :=
    Tape.read_write_same _ _ _
  have hWriteBothHead :
      Tape.write (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head true =
        Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true := by
    simpa [hReadBothHead] using Tape.write_read_self
      (Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true) cfg.head
  have hWriteBothLeft :
      Tape.write (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) (cfg.head - 1) true =
        Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true := by
    simpa [hReadBothLeft] using Tape.write_read_self
      (Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true)
      (cfg.head - 1)
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
    hReadAfterLeft, hReadBothHead, hReadBothLeft, hWriteBothHead, hWriteBothLeft,
    hPattern.1, hPattern.2.1, hPattern.2.2, go, Move.apply,
    Tape.read_write_same] <;> omega

private theorem frontierPattern6_preserves {M : Machine 2}
    (hPattern : FrontierPattern6 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) : LeftFrontier (M.runFrom cfg 4) := by
  rw [frontierPattern6_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write (Tape.write cfg.tape cfg.head true)
      (cfg.head - 1) true -> cfg.head - 2 < p
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff (Tape.write cfg.tape cfg.head true)
      (cfg.head - 1) p).mp hp with hp | hp
    · subst p; omega
    · rcases (mem_write_true_iff cfg.tape cfg.head p).mp hp with hp | hp
      · subst p; omega
      · exact Int.lt_trans (by omega) (hInv.2 p hp)

private theorem frontierPattern6_active {M : Machine 2}
    (hPattern : FrontierPattern6 M) {cfg : Config 2}
    (hInv : LeftFrontier cfg) {r : Nat} (hr : r < 4) :
    (M.runFrom cfg r).state ≠ none := by
  have hHead := leftFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hLeft := leftFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadAfterLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hReadBothHead :
      Tape.read (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head = true := by
    rw [Tape.read_write_of_ne]
    · exact Tape.read_write_same _ _ _
    · omega
  have hWriteBothHead :
      Tape.write (Tape.write (Tape.write cfg.tape cfg.head true)
        (cfg.head - 1) true) cfg.head true =
        Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true := by
    simpa [hReadBothHead] using Tape.write_read_self
      (Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) true) cfg.head
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hrCases with rfl | rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft,
      hReadAfterLeft, hReadBothHead, hWriteBothHead, hPattern.1,
      hPattern.2.1, hPattern.2.2, go, Move.apply, Tape.read_write_same]

theorem FrontierPattern6.not_halts {M : Machine 2}
    (hPattern : FrontierPattern6 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : LeftFrontier (M.run 0) := by
    simp [Machine.run, LeftFrontier, initial, startState]
  exact not_haltsWithScore_of_macro_invariant_from_run M LeftFrontier
    (start := 0) (by decide)
    (fun _cfg hInv r hr => frontierPattern6_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern6_preserves hPattern hInv)
    hInitial (by omega)

def FrontierPattern7 (M : Machine 2) : Prop :=
  M.transition A false = go true Move.left B ∧
  M.transition A true = go true Move.right B ∧
  M.transition B false = go false Move.right A

private theorem frontierPattern7_macro {M : Machine 2}
    (hPattern : FrontierPattern7 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) :
    M.runFrom cfg 4 =
      { state := some A
        head := cfg.head + 2
        tape := Tape.write cfg.tape cfg.head true } := by
  have hLeft := rightGapFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hHead := rightGapFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hRight := rightGapFrontier_not_mem hInv (p := cfg.head + 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadRight : Tape.read cfg.tape (cfg.head + 1) = false := by simp [Tape.read, hRight]
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hReadWrittenRight :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head + 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadRight
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using Tape.write_read_self
      (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hWriteWrittenRight :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head + 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenRight] using Tape.write_read_self
      (Tape.write cfg.tape cfg.head true) (cfg.head + 1)
  have hWriteHeadAgain :
      Tape.write (Tape.write cfg.tape cfg.head true) cfg.head true =
        Tape.write cfg.tape cfg.head true := by
    simpa using Tape.write_read_self (Tape.write cfg.tape cfg.head true) cfg.head
  simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft, hReadRight,
    hReadWrittenLeft, hReadWrittenRight, hWriteWrittenLeft, hWriteWrittenRight,
    hWriteHeadAgain, hPattern.1, hPattern.2.1, hPattern.2.2,
    go, Move.apply, Tape.read_write_same] <;> omega

private theorem frontierPattern7_preserves {M : Machine 2}
    (hPattern : FrontierPattern7 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) : RightGapFrontier (M.runFrom cfg 4) := by
  rw [frontierPattern7_macro hPattern hInv]
  change (some A = some A) ∧
    ∀ p, p ∈ Tape.write cfg.tape cfg.head true -> p < cfg.head + 2 - 1
  constructor
  · rfl
  · intro p hp
    rcases (mem_write_true_iff cfg.tape cfg.head p).mp hp with hp | hp
    · subst p; omega
    · have := hInv.2 p hp
      omega

private theorem frontierPattern7_active {M : Machine 2}
    (hPattern : FrontierPattern7 M) {cfg : Config 2}
    (hInv : RightGapFrontier cfg) {r : Nat} (hr : r < 4) :
    (M.runFrom cfg r).state ≠ none := by
  have hLeft := rightGapFrontier_not_mem hInv (p := cfg.head - 1) (by omega)
  have hHead := rightGapFrontier_not_mem hInv (p := cfg.head) (by omega)
  have hRight := rightGapFrontier_not_mem hInv (p := cfg.head + 1) (by omega)
  have hReadHead : Tape.read cfg.tape cfg.head = false := by simp [Tape.read, hHead]
  have hReadLeft : Tape.read cfg.tape (cfg.head - 1) = false := by simp [Tape.read, hLeft]
  have hReadRight : Tape.read cfg.tape (cfg.head + 1) = false := by simp [Tape.read, hRight]
  have hReadWrittenLeft :
      Tape.read (Tape.write cfg.tape cfg.head true) (cfg.head - 1) = false := by
    rw [Tape.read_write_of_ne]
    · exact hReadLeft
    · omega
  have hWriteWrittenLeft :
      Tape.write (Tape.write cfg.tape cfg.head true) (cfg.head - 1) false =
        Tape.write cfg.tape cfg.head true := by
    simpa [hReadWrittenLeft] using Tape.write_read_self
      (Tape.write cfg.tape cfg.head true) (cfg.head - 1)
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases hrCases with rfl | rfl | rfl | rfl <;>
    simp [Machine.runFrom, Machine.step, hInv.1, hReadHead, hReadLeft, hReadRight,
      hReadWrittenLeft, hWriteWrittenLeft, hPattern.1, hPattern.2.1,
      hPattern.2.2, go, Move.apply, Tape.read_write_same]

theorem FrontierPattern7.not_halts {M : Machine 2}
    (hPattern : FrontierPattern7 M) {score : Nat} : ¬ M.HaltsWithScore score := by
  have hInitial : RightGapFrontier (M.run 0) := by
    simp [Machine.run, RightGapFrontier, initial, startState]
  exact not_haltsWithScore_of_macro_invariant_from_run M RightGapFrontier
    (start := 0) (by decide)
    (fun _cfg hInv r hr => frontierPattern7_active hPattern hInv hr)
    (fun _cfg hInv => frontierPattern7_preserves hPattern hInv)
    hInitial (by omega)

/-! ## Reflection -/

def reflectMove : Move -> Move
  | Move.left => Move.right
  | Move.right => Move.left

def reflectAction {states : Nat} (action : Action states) : Action states where
  write := action.write
  move := reflectMove action.move
  next := action.next

def reflectMachine {states : Nat} (M : Machine states) : Machine states where
  transition q bit := reflectAction (M.transition q bit)

@[simp] theorem reflect_tableMachine (a0 a1 b0 b1 : Action 2) :
    reflectMachine (tableMachine a0 a1 b0 b1) =
      tableMachine (reflectAction a0) (reflectAction a1)
        (reflectAction b0) (reflectAction b1) := by
  rw [machine_eq_tableMachine (reflectMachine (tableMachine a0 a1 b0 b1))]
  simp [reflectMachine]

def reflectTape (tape : Tape) : Tape := tape.map (fun p => -p)

def reflectConfig {states : Nat} (cfg : Config states) : Config states where
  state := cfg.state
  head := -cfg.head
  tape := reflectTape cfg.tape

@[simp] private theorem mem_tape_reflect_neg (tape : Tape) (p : Int) :
    -p ∈ reflectTape tape ↔ p ∈ tape := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨q, hq, hEq⟩
    have : q = p := by omega
    simpa [this] using hq
  · intro h
    exact List.mem_map.mpr ⟨p, h, rfl⟩

@[simp] theorem Tape.read_reflect_neg (tape : Tape) (p : Int) :
    Tape.read (reflectTape tape) (-p) = Tape.read tape p := by
  simp [Tape.read]

private theorem bne_neg_iff (a p : Int) :
    (-a != -p) = (a != p) := by
  by_cases h : a = p
  · subst a; simp
  · have hn : -a ≠ -p := by omega
    exact Eq.trans (bne_iff_ne.mpr hn) (bne_iff_ne.mpr h).symm

@[simp] private theorem reflect_filter_ne (tape : Tape) (p : Int) :
    reflectTape (tape.filter (fun q => q != p)) =
      (reflectTape tape).filter (fun q => q != -p) := by
  induction tape with
  | nil => rfl
  | cons a rest ih =>
      by_cases h : a != p
      · have hn : (-a != -p) = true := by simpa [bne_neg_iff] using h
        simp [reflectTape, List.filter, h, hn]
        simpa [reflectTape] using ih
      · have hf : (a != p) = false := Bool.eq_false_iff.mpr h
        have hnf : (-a != -p) = false := by simpa [bne_neg_iff] using hf
        simp [reflectTape, List.filter, hf, hnf]
        simpa [reflectTape] using ih

@[simp] theorem Tape.reflect_write (tape : Tape) (p : Int) (bit : Bool) :
    reflectTape (Tape.write tape p bit) = Tape.write (reflectTape tape) (-p) bit := by
  cases bit
  · simp [Tape.write]
  · by_cases h : p ∈ tape
    · have hn : -p ∈ reflectTape tape := mem_tape_reflect_neg tape p |>.2 h
      simp [Tape.write, h, hn, reflectTape]
    · have hn : -p ∉ reflectTape tape := by simpa using h
      simp [Tape.write, h, hn, reflectTape]

@[simp] theorem Move.reflect_apply_neg (move : Move) (p : Int) :
    (reflectMove move).apply (-p) = -(move.apply p) := by
  cases move <;> simp [reflectMove, Move.apply] <;> omega

@[simp] theorem reflect_step {states : Nat} (M : Machine states)
    (cfg : Config states) :
    (reflectMachine M).step (reflectConfig cfg) = reflectConfig (M.step cfg) := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some q =>
          simp [reflectMachine, reflectAction, reflectConfig, Machine.step,
            Tape.read_reflect_neg, Tape.reflect_write]

@[simp] theorem reflect_initial (states : Nat) :
    reflectConfig (initial states) = initial states := by
  simp [reflectConfig, initial, reflectTape]

@[simp] theorem reflect_run {states : Nat} (M : Machine states) :
    ∀ t, (reflectMachine M).run t = reflectConfig (M.run t)
  | 0 => by simp [Machine.run]
  | t + 1 => by simp [Machine.run, reflect_run M t]

theorem reflect_haltsWithScore {states score : Nat} {M : Machine states} :
    M.HaltsWithScore score -> (reflectMachine M).HaltsWithScore score := by
  rintro ⟨t, hState, hScore⟩
  refine ⟨t, ?_, ?_⟩
  · simpa [reflect_run, reflectConfig, hState]
  · simpa [reflect_run, reflectConfig, reflectTape] using hScore

def CanonicalFrontierPattern (M : Machine 2) : Prop :=
  FrontierPattern1 M ∨ FrontierPattern2 M ∨ FrontierPattern3 M ∨
  FrontierPattern4 M ∨ FrontierPattern5 M ∨ FrontierPattern6 M ∨
  FrontierPattern7 M

def HasFrontierCertificate (M : Machine 2) : Prop :=
  CanonicalFrontierPattern M ∨ CanonicalFrontierPattern (reflectMachine M)

instance (M : Machine 2) : Decidable (HasFrontierCertificate M) := by
  unfold HasFrontierCertificate CanonicalFrontierPattern FrontierPattern1
    FrontierPattern2 FrontierPattern3 FrontierPattern4 FrontierPattern5
    FrontierPattern6 FrontierPattern7
  infer_instance

theorem CanonicalFrontierPattern.not_halts {M : Machine 2}
    (h : CanonicalFrontierPattern M) {score : Nat} : ¬ M.HaltsWithScore score := by
  rcases h with h | h | h | h | h | h | h
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts

theorem HasFrontierCertificate.not_halts {M : Machine 2}
    (h : HasFrontierCertificate M) {score : Nat} : ¬ M.HaltsWithScore score := by
  rcases h with h | h
  · exact h.not_halts
  · intro hHalt
    exact h.not_halts (reflect_haltsWithScore hHalt)

/-! ## Exhaustive coverage and the exact value -/

def NonhaltingCertificate (M : Machine 2) : Prop :=
  HasShortShiftLoop M ∨ HasShortBlankEscape M ∨
  HasClosedLocalInvariant M ∨ HasFrontierCertificate M

def CertifiedSafe (M : Machine 2) : Prop :=
  SafeAtSix M ∨ NonhaltingCertificate M

instance (M : Machine 2) : Decidable (CertifiedSafe M) := by
  unfold CertifiedSafe NonhaltingCertificate
  infer_instance

theorem NonhaltingCertificate.not_halts {M : Machine 2}
    (h : NonhaltingCertificate M) {score : Nat} : ¬ M.HaltsWithScore score := by
  rcases h with h | h | h | h
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts
  · exact h.not_halts

theorem CertifiedSafe.score_le_four {M : Machine 2} (h : CertifiedSafe M)
    {score : Nat} (hHalt : M.HaltsWithScore score) : score ≤ 4 := by
  rcases h with hSafe | hNever
  · exact hSafe.score_le_four hHalt
  · exact False.elim (hNever.not_halts hHalt)

def actionList : List (Action 2) :=
  [ halt false Move.left, go false Move.left A, go false Move.left B,
    halt false Move.right, go false Move.right A, go false Move.right B,
    halt true Move.left, go true Move.left A, go true Move.left B,
    halt true Move.right, go true Move.right A, go true Move.right B ]

theorem action_mem_actionList (action : Action 2) : action ∈ actionList := by
  rcases action with ⟨write, move, next⟩
  cases write <;> cases move <;> cases next with
  | none => simp [actionList, halt, go]
  | some q => fin_cases q <;> simp [actionList, halt, go]

def tablesCheckFor2 (a0 a1 : Action 2) : Bool :=
  actionList.all fun b0 =>
  actionList.all fun b1 =>
    decide (CertifiedSafe (tableMachine a0 a1 b0 b1))

def tablesCheckFor (a0 : Action 2) : Bool :=
  actionList.all (tablesCheckFor2 a0)

end BB2
end BusyBeaver
end SetTheory
