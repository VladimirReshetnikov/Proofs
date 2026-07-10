/-
  BusyBeaverBB3/Search.lean

  A sound lazy exploration of three-state transition tables.

  The table records only continuing transitions.  When execution first reaches
  an unassigned slot, the checker separately verifies both possible final
  writes and then explores the twelve possible continuing transitions.  At the
  simulation horizon it delegates to an abstract, independently proved
  nonhalting checker.  This keeps the finite search independent of the concrete
  n-gram certificate used by the final BB(3) development.
-/

import SetTheory.BusyBeaverKnownValues

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB3

/-! ## Partial continuing-transition tables -/

/-- A transition known to continue in one of the three operational states. -/
structure GoAction where
  write : Bool
  move : Move
  next : Fin 3
  deriving DecidableEq, Repr

namespace GoAction

/-- Forget that a transition is known to continue. -/
def toAction (action : GoAction) : Action 3 where
  write := action.write
  move := action.move
  next := some action.next

end GoAction

/-- A partially assigned table.  `none` means that a slot has not yet been
encountered, not that the represented total machine necessarily halts there. -/
abbrev PTable := Fin 3 -> Bool -> Option GoAction

namespace PTable

def empty : PTable := fun _ _ => none

def set (table : PTable) (q : Fin 3) (bit : Bool) (action : GoAction) : PTable :=
  fun q' bit' =>
    if q' = q then
      if bit' = bit then some action else table q' bit'
    else table q' bit'

/-- Every assigned partial-table entry is the corresponding transition of the
given total Rado machine. -/
def Agrees (table : PTable) (M : Machine 3) : Prop :=
  forall q bit action, table q bit = some action ->
    action.toAction = M.transition q bit

theorem empty_agrees (M : Machine 3) : empty.Agrees M := by
  intro q bit action h
  cases h

theorem set_agrees {table : PTable} {M : Machine 3}
    (hTable : table.Agrees M) {q : Fin 3} {bit : Bool} {action : GoAction}
    (hAction : action.toAction = M.transition q bit) :
    (table.set q bit action).Agrees M := by
  intro q' bit' action' hLookup
  by_cases hq : q' = q
  · subst q'
    by_cases hb : bit' = bit
    · subst bit'
      have hEq : action = action' := by
        simpa [set] using hLookup
      subst action'
      exact hAction
    · have hOld : table q bit' = some action' := by
        simpa [set, hb] using hLookup
      exact hTable q bit' action' hOld
  · have hOld : table q' bit' = some action' := by
      simpa [set, hq] using hLookup
    exact hTable q' bit' action' hOld

end PTable

private abbrev A : Fin 3 := 0
private abbrev B : Fin 3 := 1
private abbrev C : Fin 3 := 2

private def go (write : Bool) (move : Move) (next : Fin 3) : GoAction :=
  { write, move, next }

/-- The twelve continuing actions available in a three-state Rado machine. -/
def actionList : List GoAction :=
  [ go false Move.left A, go false Move.left B, go false Move.left C,
    go false Move.right A, go false Move.right B, go false Move.right C,
    go true Move.left A, go true Move.left B, go true Move.left C,
    go true Move.right A, go true Move.right B, go true Move.right C ]

theorem action_mem_actionList (action : GoAction) : action ∈ actionList := by
  rcases action with ⟨write, move, ⟨next, hNext⟩⟩
  have hCases : next = 0 ∨ next = 1 ∨ next = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;>
    cases write <;> cases move <;> simp [actionList, go, A, B, C]

/-! ## Concrete execution and the final-write check -/

/-- Execute an explicitly supplied Rado action from an active configuration. -/
def stepAction (cfg : Config 3) (action : Action 3) : Config 3 where
  state := action.next
  head := action.move.apply cfg.head
  tape := Tape.write cfg.tape cfg.head action.write

def stepGo (cfg : Config 3) (action : GoAction) : Config 3 :=
  stepAction cfg action.toAction

theorem stepAction_eq_step (M : Machine 3) (cfg : Config 3) (q : Fin 3)
    (action : Action 3) (hState : cfg.state = some q)
    (hAction : action = M.transition q (Tape.read cfg.tape cfg.head)) :
    stepAction cfg action = M.step cfg := by
  cases cfg with
  | mk state head tape =>
      simp_all [stepAction, Machine.step]

theorem stepGo_eq_step (M : Machine 3) (cfg : Config 3) (q : Fin 3)
    (action : GoAction) (hState : cfg.state = some q)
    (hAction : action.toAction = M.transition q (Tape.read cfg.tape cfg.head)) :
    stepGo cfg action = M.step cfg :=
  stepAction_eq_step M cfg q action.toAction hState hAction

/-- Both possible writes of a halting transition leave at most six marks.  The
move is immaterial after the final write. -/
def haltWritesSafe (cfg : Config 3) : Bool :=
  decide ((Tape.write cfg.tape cfg.head false).length <= 6) &&
  decide ((Tape.write cfg.tape cfg.head true).length <= 6)

theorem haltWritesSafe_sound {cfg : Config 3} (h : haltWritesSafe cfg = true)
    (write : Bool) : (Tape.write cfg.tape cfg.head write).length <= 6 := by
  have hs := Bool.and_eq_true_iff.mp h
  cases write
  · exact of_decide_eq_true hs.1
  · exact of_decide_eq_true hs.2

/-! ## The lazy checker -/

/--
`checkFrom leaf fuel table cfg` follows the single execution path represented
by `table`.  A fresh slot has two kinds of completion: a halting transition
(whose two distinct final writes are checked by `haltWritesSafe`) or one of the
twelve continuing transitions.  At fuel zero, `leaf` must certify that every
total machine agreeing with `table` runs forever from the blank tape.
-/
def checkFrom (leaf : PTable -> Config 3 -> Bool) :
    Nat -> PTable -> Config 3 -> Bool
  | 0, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 6)
      | some _ => leaf table cfg
  | fuel + 1, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 6)
      | some q =>
          let bit := Tape.read cfg.tape cfg.head
          match table q bit with
          | some action => checkFrom leaf fuel table (stepGo cfg action)
          | none =>
              haltWritesSafe cfg &&
                actionList.all (fun action =>
                  checkFrom leaf fuel (table.set q bit action) (stepGo cfg action))

/-- A leaf checker is sound when success rules out halting from the blank tape
for every agreeing total machine.  The configuration remains an input so an
implementation may use it as a consistency check, but the conclusion is the
global one needed by blank-seeded n-gram certificates. -/
def LeafSound (leaf : PTable -> Config 3 -> Bool) : Prop :=
  forall table cfg M,
    table.Agrees M ->
    leaf table cfg = true ->
    forall t, (M.run t).state ≠ none

/-- A configuration reached on the total machine's blank-tape run. -/
def Reachable (M : Machine 3) (cfg : Config 3) : Prop :=
  ∃ start, cfg = M.run start

theorem Reachable.step {M : Machine 3} {cfg : Config 3}
    (h : Reachable M cfg) : Reachable M (M.step cfg) := by
  rcases h with ⟨start, rfl⟩
  exact ⟨start + 1, rfl⟩

theorem runFrom_succ_start (M : Machine 3) (cfg : Config 3) (t : Nat) :
    M.runFrom cfg (t + 1) = M.runFrom (M.step cfg) t := by
  rw [show t + 1 = 1 + t by omega, Machine.runFrom_add]
  rfl

theorem runFrom_of_halted (M : Machine 3) (cfg : Config 3)
    (hHalted : cfg.state = none) : forall t, M.runFrom cfg t = cfg
  | 0 => rfl
  | t + 1 => by
      rw [Machine.runFrom_succ]
      rw [runFrom_of_halted M cfg hHalted t]
      simp [Machine.step, hHalted]

/-- Soundness of the lazy search, independently of the implementation of its
nonhalting leaf checker. -/
theorem checkFrom_sound {leaf : PTable -> Config 3 -> Bool}
    (hLeaf : LeafSound leaf) :
    forall fuel table cfg M,
      checkFrom leaf fuel table cfg = true ->
      table.Agrees M ->
      Reachable M cfg ->
      forall t,
        (M.runFrom cfg t).state = none ->
        (M.runFrom cfg t).tape.length <= 6 := by
  intro fuel
  induction fuel with
  | zero =>
      intro table cfg M hCheck hAgree hReach t hHalted
      cases hState : cfg.state with
      | none =>
          have hRun : M.runFrom cfg t = cfg := runFrom_of_halted M cfg hState t
          have hBound : cfg.tape.length <= 6 :=
            of_decide_eq_true (by simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some q =>
          have hLeafCheck : leaf table cfg = true := by
            simpa [checkFrom, hState] using hCheck
          rcases hReach with ⟨start, hCfg⟩
          have hRun : M.run (start + t) = M.runFrom cfg t := by
            rw [hCfg, Machine.run_add_eq_runFrom]
          have hGlobalHalted : (M.run (start + t)).state = none :=
            (congrArg Config.state hRun).trans hHalted
          exact False.elim
            (hLeaf table cfg M hAgree hLeafCheck (start + t) hGlobalHalted)
  | succ fuel ih =>
      intro table cfg M hCheck hAgree hReach t hHalted
      cases hState : cfg.state with
      | none =>
          have hRun : M.runFrom cfg t = cfg := runFrom_of_halted M cfg hState t
          have hBound : cfg.tape.length <= 6 :=
            of_decide_eq_true (by simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some q =>
          cases t with
          | zero =>
              simp [Machine.runFrom, hState] at hHalted
          | succ t =>
              let bit := Tape.read cfg.tape cfg.head
              cases hLookup : table q bit with
              | some action =>
                  have hAction := hAgree q bit action hLookup
                  have hStep := stepGo_eq_step M cfg q action hState hAction
                  have hReach' : Reachable M (stepGo cfg action) := by
                    rw [hStep]
                    exact hReach.step
                  have hBranch :
                      checkFrom leaf fuel table (stepGo cfg action) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  rw [runFrom_succ_start, <- hStep] at hHalted
                  rw [runFrom_succ_start, <- hStep]
                  exact ih table (stepGo cfg action) M hBranch hAgree hReach' t hHalted
              | none =>
                  have hNode :
                      (haltWritesSafe cfg &&
                        actionList.all (fun action =>
                          checkFrom leaf fuel (table.set q bit action)
                            (stepGo cfg action))) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  have hParts := Bool.and_eq_true_iff.mp hNode
                  cases hTransition : M.transition q bit with
                  | mk write move next =>
                      cases next with
                      | none =>
                          have hStepState : (M.step cfg).state = none := by
                            simp [Machine.step, hState, bit, hTransition]
                          rw [runFrom_succ_start]
                          rw [runFrom_of_halted M (M.step cfg) hStepState t]
                          simpa [Machine.step, hState, bit, hTransition] using
                            haltWritesSafe_sound hParts.1 write
                      | some next =>
                          let action : GoAction := { write, move, next }
                          have hAction :
                              action.toAction = M.transition q bit := by
                            simp [action, GoAction.toAction, hTransition]
                          have hMember : action ∈ actionList :=
                            action_mem_actionList action
                          have hBranch :
                              checkFrom leaf fuel (table.set q bit action)
                                (stepGo cfg action) = true :=
                            (List.all_eq_true.mp hParts.2) action hMember
                          have hAgree' : (table.set q bit action).Agrees M :=
                            PTable.set_agrees hAgree hAction
                          have hStep := stepGo_eq_step M cfg q action hState hAction
                          have hReach' : Reachable M (stepGo cfg action) := by
                            rw [hStep]
                            exact hReach.step
                          rw [runFrom_succ_start, <- hStep] at hHalted
                          rw [runFrom_succ_start, <- hStep]
                          exact ih (table.set q bit action) (stepGo cfg action) M
                            hBranch hAgree' hReach' t hHalted

/-- The complete lazy tree starts on the blank tape with no assigned slots. -/
def check (leaf : PTable -> Config 3 -> Bool) : Bool :=
  checkFrom leaf 21 PTable.empty (initial 3)

/-- Any successful sound leaf checker proves the three-state score upper
bound. -/
theorem upperBound_of_check {leaf : PTable -> Config 3 -> Bool}
    (hLeaf : LeafSound leaf) (hCheck : check leaf = true) {score : Nat} :
    AttainableScore 3 score -> score <= 6 := by
  rintro ⟨M, t, hState, hScore⟩
  have hBound := checkFrom_sound hLeaf 21 PTable.empty (initial 3) M
    hCheck (PTable.empty_agrees M) ⟨0, rfl⟩ t
  have hRun : M.runFrom (initial 3) t = M.run t := by
    simpa [Machine.run] using (Machine.run_add_eq_runFrom M 0 t).symm
  rw [hRun] at hBound
  calc
    score = (M.run t).tape.length := hScore.symm
    _ <= 6 := hBound hState

end BB3
end BusyBeaver
end SetTheory
