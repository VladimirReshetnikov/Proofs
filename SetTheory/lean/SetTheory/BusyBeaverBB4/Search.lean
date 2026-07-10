/-
  BusyBeaverBB4/Search.lean

  Sound lazy exploration of four-state transition tables.  The semantic proof
  is independent of the concrete nonhalting leaf implementation.
-/

import SetTheory.BusyBeaverKnownValues

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB4

/-! ## Partial continuing-transition tables -/

structure GoAction where
  write : Bool
  move : Move
  next : Fin 4
  deriving DecidableEq, Repr

namespace GoAction

def toAction (action : GoAction) : Action 4 where
  write := action.write
  move := action.move
  next := some action.next

end GoAction

/-- `none` denotes an as-yet unassigned table slot. -/
abbrev PTable := Fin 4 -> Bool -> Option GoAction

namespace PTable

def empty : PTable := fun _ _ => none

def set (table : PTable) (q : Fin 4) (bit : Bool) (action : GoAction) : PTable :=
  fun q' bit' =>
    if q' = q then
      if bit' = bit then some action else table q' bit'
    else table q' bit'

def Agrees (table : PTable) (machine : Machine 4) : Prop :=
  forall q bit action, table q bit = some action ->
    action.toAction = machine.transition q bit

theorem empty_agrees (machine : Machine 4) : empty.Agrees machine := by
  intro q bit action h
  cases h

theorem set_agrees {table : PTable} {machine : Machine 4}
    (hTable : table.Agrees machine) {q : Fin 4} {bit : Bool}
    {action : GoAction}
    (hAction : action.toAction = machine.transition q bit) :
    (table.set q bit action).Agrees machine := by
  intro q' bit' action' hLookup
  by_cases hq : q' = q
  · subst q'
    by_cases hb : bit' = bit
    · subst bit'
      have hEq : action = action' := by
        simpa [set] using hLookup
      subst action'
      exact hAction
    · exact hTable q bit' action' (by simpa [set, hb] using hLookup)
  · exact hTable q' bit' action' (by simpa [set, hq] using hLookup)

end PTable

private abbrev A : Fin 4 := 0
private abbrev B : Fin 4 := 1
private abbrev C : Fin 4 := 2
private abbrev D : Fin 4 := 3

private def go (write : Bool) (move : Move) (next : Fin 4) : GoAction :=
  { write, move, next }

/-- All `2 * 2 * 4 = 16` continuing actions. -/
def actionList : List GoAction :=
  [ go false Move.left A, go false Move.left B,
    go false Move.left C, go false Move.left D,
    go false Move.right A, go false Move.right B,
    go false Move.right C, go false Move.right D,
    go true Move.left A, go true Move.left B,
    go true Move.left C, go true Move.left D,
    go true Move.right A, go true Move.right B,
    go true Move.right C, go true Move.right D ]

theorem action_mem_actionList (action : GoAction) : action ∈ actionList := by
  rcases action with ⟨write, move, ⟨next, hNext⟩⟩
  have hCases : next = 0 ∨ next = 1 ∨ next = 2 ∨ next = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl <;>
    cases write <;> cases move <;>
      simp [actionList, go, A, B, C, D]

/-! ## Concrete execution and final-write score check -/

def stepAction (cfg : Config 4) (action : Action 4) : Config 4 where
  state := action.next
  head := action.move.apply cfg.head
  tape := Tape.write cfg.tape cfg.head action.write

def stepGo (cfg : Config 4) (action : GoAction) : Config 4 :=
  stepAction cfg action.toAction

theorem stepAction_eq_step (machine : Machine 4) (cfg : Config 4)
    (q : Fin 4) (action : Action 4) (hState : cfg.state = some q)
    (hAction : action = machine.transition q (Tape.read cfg.tape cfg.head)) :
    stepAction cfg action = machine.step cfg := by
  cases cfg with
  | mk state head tape => simp_all [stepAction, Machine.step]

theorem stepGo_eq_step (machine : Machine 4) (cfg : Config 4)
    (q : Fin 4) (action : GoAction) (hState : cfg.state = some q)
    (hAction : action.toAction =
      machine.transition q (Tape.read cfg.tape cfg.head)) :
    stepGo cfg action = machine.step cfg :=
  stepAction_eq_step machine cfg q action.toAction hState hAction

/-- Both possible writes of a final transition leave at most thirteen marks. -/
def haltWritesSafe (cfg : Config 4) : Bool :=
  decide ((Tape.write cfg.tape cfg.head false).length ≤ 13) &&
  decide ((Tape.write cfg.tape cfg.head true).length ≤ 13)

theorem haltWritesSafe_sound {cfg : Config 4} (h : haltWritesSafe cfg = true)
    (write : Bool) : (Tape.write cfg.tape cfg.head write).length ≤ 13 := by
  have hs := Bool.and_eq_true_iff.mp h
  cases write
  · exact of_decide_eq_true hs.1
  · exact of_decide_eq_true hs.2

/-! ## Lazy checker and abstract soundness -/

def checkFrom (leaf : PTable -> Config 4 -> Bool) :
    Nat -> PTable -> Config 4 -> Bool
  | 0, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length ≤ 13)
      | some _ => leaf table cfg
  | fuel + 1, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length ≤ 13)
      | some q =>
          let bit := Tape.read cfg.tape cfg.head
          match table q bit with
          | some action => checkFrom leaf fuel table (stepGo cfg action)
          | none =>
              haltWritesSafe cfg &&
                actionList.all (fun action =>
                  checkFrom leaf fuel (table.set q bit action)
                    (stepGo cfg action))

def LeafSound (leaf : PTable -> Config 4 -> Bool) : Prop :=
  forall table cfg machine,
    table.Agrees machine ->
    leaf table cfg = true ->
    forall t, (machine.run t).state ≠ none

def Reachable (machine : Machine 4) (cfg : Config 4) : Prop :=
  ∃ start, cfg = machine.run start

theorem Reachable.step {machine : Machine 4} {cfg : Config 4}
    (h : Reachable machine cfg) : Reachable machine (machine.step cfg) := by
  rcases h with ⟨start, rfl⟩
  exact ⟨start + 1, rfl⟩

theorem runFrom_succ_start (machine : Machine 4) (cfg : Config 4) (t : Nat) :
    machine.runFrom cfg (t + 1) = machine.runFrom (machine.step cfg) t := by
  rw [show t + 1 = 1 + t by omega, Machine.runFrom_add]
  rfl

theorem runFrom_of_halted (machine : Machine 4) (cfg : Config 4)
    (hHalted : cfg.state = none) : forall t, machine.runFrom cfg t = cfg
  | 0 => rfl
  | t + 1 => by
      rw [Machine.runFrom_succ]
      rw [runFrom_of_halted machine cfg hHalted t]
      simp [Machine.step, hHalted]

theorem checkFrom_sound {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) :
    forall fuel table cfg machine,
      checkFrom leaf fuel table cfg = true ->
      table.Agrees machine ->
      Reachable machine cfg ->
      forall t,
        (machine.runFrom cfg t).state = none ->
        (machine.runFrom cfg t).tape.length ≤ 13 := by
  intro fuel
  induction fuel with
  | zero =>
      intro table cfg machine hCheck hAgree hReach t hHalted
      cases hState : cfg.state with
      | none =>
          have hRun := runFrom_of_halted machine cfg hState t
          have hBound : cfg.tape.length ≤ 13 :=
            of_decide_eq_true (by simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some q =>
          have hLeafCheck : leaf table cfg = true := by
            simpa [checkFrom, hState] using hCheck
          rcases hReach with ⟨start, hCfg⟩
          have hRun : machine.run (start + t) = machine.runFrom cfg t := by
            rw [hCfg, Machine.run_add_eq_runFrom]
          have hGlobalHalted : (machine.run (start + t)).state = none :=
            (congrArg Config.state hRun).trans hHalted
          exact False.elim
            (hLeaf table cfg machine hAgree hLeafCheck (start + t)
              hGlobalHalted)
  | succ fuel ih =>
      intro table cfg machine hCheck hAgree hReach t hHalted
      cases hState : cfg.state with
      | none =>
          have hRun := runFrom_of_halted machine cfg hState t
          have hBound : cfg.tape.length ≤ 13 :=
            of_decide_eq_true (by simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some q =>
          cases t with
          | zero => simp [Machine.runFrom, hState] at hHalted
          | succ t =>
              let bit := Tape.read cfg.tape cfg.head
              cases hLookup : table q bit with
              | some action =>
                  have hAction := hAgree q bit action hLookup
                  have hStep :=
                    stepGo_eq_step machine cfg q action hState hAction
                  have hReach' : Reachable machine (stepGo cfg action) := by
                    rw [hStep]
                    exact hReach.step
                  have hBranch :
                      checkFrom leaf fuel table (stepGo cfg action) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  rw [runFrom_succ_start, ← hStep] at hHalted
                  rw [runFrom_succ_start, ← hStep]
                  exact ih table (stepGo cfg action) machine hBranch hAgree
                    hReach' t hHalted
              | none =>
                  have hNode :
                      (haltWritesSafe cfg &&
                        actionList.all (fun action =>
                          checkFrom leaf fuel (table.set q bit action)
                            (stepGo cfg action))) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  have hParts := Bool.and_eq_true_iff.mp hNode
                  cases hTransition : machine.transition q bit with
                  | mk write move next =>
                      cases next with
                      | none =>
                          have hStepState : (machine.step cfg).state = none := by
                            simp [Machine.step, hState, bit, hTransition]
                          rw [runFrom_succ_start]
                          rw [runFrom_of_halted machine (machine.step cfg)
                            hStepState t]
                          simpa [Machine.step, hState, bit, hTransition] using
                            haltWritesSafe_sound hParts.1 write
                      | some next =>
                          let action : GoAction := { write, move, next }
                          have hAction :
                              action.toAction = machine.transition q bit := by
                            simp [action, GoAction.toAction, hTransition]
                          have hMember : action ∈ actionList :=
                            action_mem_actionList action
                          have hBranch :
                              checkFrom leaf fuel (table.set q bit action)
                                (stepGo cfg action) = true :=
                            (List.all_eq_true.mp hParts.2) action hMember
                          have hAgree' :
                              (table.set q bit action).Agrees machine :=
                            PTable.set_agrees hAgree hAction
                          have hStep :=
                            stepGo_eq_step machine cfg q action hState hAction
                          have hReach' :
                              Reachable machine (stepGo cfg action) := by
                            rw [hStep]
                            exact hReach.step
                          rw [runFrom_succ_start, ← hStep] at hHalted
                          rw [runFrom_succ_start, ← hStep]
                          exact ih (table.set q bit action) (stepGo cfg action)
                            machine hBranch hAgree' hReach' t hHalted

def check (leaf : PTable -> Config 4 -> Bool) : Bool :=
  checkFrom leaf 107 PTable.empty (initial 4)

theorem upperBound_of_check {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) (hCheck : check leaf = true) {score : Nat} :
    AttainableScore 4 score -> score ≤ 13 := by
  rintro ⟨machine, t, hState, hScore⟩
  have hBound := checkFrom_sound hLeaf 107 PTable.empty (initial 4) machine
    hCheck (PTable.empty_agrees machine) ⟨0, rfl⟩ t
  have hRun : machine.runFrom (initial 4) t = machine.run t := by
    simpa [Machine.run] using
      (Machine.run_add_eq_runFrom machine 0 t).symm
  rw [hRun] at hBound
  calc
    score = (machine.run t).tape.length := hScore.symm
    _ ≤ 13 := hBound hState

end BB4
end BusyBeaver
end SetTheory
