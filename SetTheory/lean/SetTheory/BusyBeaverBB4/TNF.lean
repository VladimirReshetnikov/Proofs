/-
  BusyBeaverBB4/TNF.lean

  A sound tree-normal-form reduction for the four-state lazy search.  States
  already named by the explored prefix are `0, ..., used - 1`; a continuing
  transition may target one of those states or introduce exactly `used`.
-/

import SetTheory.BusyBeaverBB4.TNFRenaming

set_option maxRecDepth 10000

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace TNF

/-- Continuing actions whose target is already named or is the single next
canonical fresh state.  For `used = 1,2,3,4`, this has `8,12,16,16` actions. -/
def canonicalActions (used : Nat) : List GoAction :=
  BB4.actionList.filter fun action => decide (action.next.val <= used)

theorem canonicalActionCounts :
    [ (canonicalActions 1).length,
      (canonicalActions 2).length,
      (canonicalActions 3).length,
      (canonicalActions 4).length ] = [8, 12, 16, 16] := by
  decide

theorem mem_canonicalActions {used : Nat} (action : GoAction)
    (hNext : action.next.val <= used) :
    action ∈ canonicalActions used := by
  simp [canonicalActions, BB4.action_mem_actionList, hNext]

/-- Increase the named prefix exactly far enough to include an action target. -/
def grow (used : Nat) (action : GoAction) : Nat :=
  max used (action.next.val + 1)

theorem used_le_grow (used : Nat) (action : GoAction) :
    used <= grow used action :=
  Nat.le_max_left _ _

theorem next_lt_grow (used : Nat) (action : GoAction) :
    action.next.val < grow used action := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)

theorem grow_le_four {used : Nat} (action : GoAction) (hUsed : used <= 4) :
    grow used action <= 4 := by
  exact Nat.max_le_of_le_of_le hUsed (by omega)

/-- The explicit invariant trusted by the TNF reduction.  Every assigned
domain, assigned target, and active current state lies in the named prefix. -/
structure PrefixInvariant (used : Nat) (table : PTable) (cfg : Config 4) : Prop where
  positive : 0 < used
  bounded : used <= 4
  table_prefix : forall state bit action,
    table state bit = some action ->
      state.val < used ∧ action.next.val < used
  state_prefix : forall state, cfg.state = some state -> state.val < used

theorem PrefixInvariant.step_known {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {state : Fin 4} {bit : Bool} {action : GoAction}
    (hLookup : table state bit = some action) :
    PrefixInvariant used table (stepGo cfg action) := by
  refine
    { positive := hInv.positive
      bounded := hInv.bounded
      table_prefix := hInv.table_prefix
      state_prefix := ?_ }
  intro next hState
  have hNext := (hInv.table_prefix state bit action hLookup).2
  have hEq : action.next = next := by
    simpa [stepGo, stepAction, GoAction.toAction] using hState
  simpa [← hEq] using hNext

theorem PrefixInvariant.step_fresh {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {state : Fin 4} {bit : Bool} {action : GoAction}
    (hState : cfg.state = some state) :
    PrefixInvariant (grow used action) (table.set state bit action)
      (stepGo cfg action) := by
  refine
    { positive := Nat.lt_of_lt_of_le hInv.positive (used_le_grow used action)
      bounded := grow_le_four action hInv.bounded
      table_prefix := ?_
      state_prefix := ?_ }
  · intro state' bit' action' hLookup
    by_cases hStateEq : state' = state
    · subst state'
      by_cases hBitEq : bit' = bit
      · subst bit'
        have hActionEq : action = action' := by
          simpa [PTable.set] using hLookup
        subst action'
        exact
          ⟨Nat.lt_of_lt_of_le (hInv.state_prefix state hState)
              (used_le_grow used action),
            next_lt_grow used action⟩
      · have hOld : table state bit' = some action' := by
          simpa [PTable.set, hBitEq] using hLookup
        have hPrefix := hInv.table_prefix state bit' action' hOld
        exact
          ⟨Nat.lt_of_lt_of_le hPrefix.1 (used_le_grow used action),
            Nat.lt_of_lt_of_le hPrefix.2 (used_le_grow used action)⟩
    · have hOld : table state' bit' = some action' := by
        simpa [PTable.set, hStateEq] using hLookup
      have hPrefix := hInv.table_prefix state' bit' action' hOld
      exact
        ⟨Nat.lt_of_lt_of_le hPrefix.1 (used_le_grow used action),
          Nat.lt_of_lt_of_le hPrefix.2 (used_le_grow used action)⟩
  · intro next hNextState
    have hEq : action.next = next := by
      simpa [stepGo, stepAction, GoAction.toAction] using hNextState
    simpa [← hEq] using next_lt_grow used action

theorem rename_action_eq_of_fixed {equiv : Perm} {action : GoAction}
    (hNext : equiv action.next = action.next) :
    Rename.action equiv action.toAction = action.toAction := by
  cases action
  simp [Rename.action, GoAction.toAction, hNext]

theorem rename_config_eq_of_prefix {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {equiv : Perm} (hFix : Rename.FixesPrefix used equiv) :
    Rename.config equiv cfg = cfg := by
  cases cfg with
  | mk state head tape =>
      cases state with
      | none => rfl
      | some state =>
          have hState : equiv state = state :=
            hFix state (hInv.state_prefix state rfl)
          simp [Rename.config, hState]

theorem agrees_rename_of_prefix {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {machine : Machine 4} (hAgree : table.Agrees machine)
    {equiv : Perm} (hFix : Rename.FixesPrefix used equiv) :
    table.Agrees (Rename.machine equiv machine) := by
  intro state bit action hLookup
  have hPrefix := hInv.table_prefix state bit action hLookup
  have hState : equiv state = state := hFix state hPrefix.1
  have hStateSymm : equiv.symm state = state := by
    have hRoundTrip := Perm.symm_apply_apply equiv state
    simpa [hState] using hRoundTrip
  have hAction := hAgree state bit action hLookup
  change action.toAction =
    Rename.action equiv (machine.transition (equiv.symm state) bit)
  rw [hStateSymm, ← hAction]
  exact (rename_action_eq_of_fixed (hFix action.next hPrefix.2)).symm

theorem reachable_rename_of_prefix {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {machine : Machine 4} (hReach : Reachable machine cfg)
    {equiv : Perm} (hFix : Rename.FixesPrefix used equiv) :
    Reachable (Rename.machine equiv machine) cfg := by
  rcases hReach with ⟨start, hCfg⟩
  refine ⟨start, ?_⟩
  rw [Rename.run equiv machine
    (Rename.fixesPrefix_zero hInv.positive hFix) start]
  rw [← hCfg]
  exact (rename_config_eq_of_prefix hInv hFix).symm

/-- TNF lazy search.  Its only difference from `BB4.checkFrom` is the reduced
continuing-action list and the explicit named-prefix parameter. -/
def checkFrom (leaf : PTable -> Config 4 -> Bool) :
    Nat -> Nat -> PTable -> Config 4 -> Bool
  | 0, _used, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 13)
      | some _ => leaf table cfg
  | fuel + 1, used, table, cfg =>
      match cfg.state with
      | none => decide (cfg.tape.length <= 13)
      | some state =>
          let bit := Tape.read cfg.tape cfg.head
          match table state bit with
          | some action => checkFrom leaf fuel used table (stepGo cfg action)
          | none =>
              haltWritesSafe cfg &&
                (canonicalActions used).all fun action =>
                  checkFrom leaf fuel (grow used action)
                    (table.set state bit action) (stepGo cfg action)

def check (leaf : PTable -> Config 4 -> Bool) : Bool :=
  checkFrom leaf 107 1 PTable.empty (initial 4)

theorem runFrom_rename_of_prefix {used : Nat} {table : PTable}
    {cfg : Config 4} (hInv : PrefixInvariant used table cfg)
    {machine : Machine 4} {equiv : Perm}
    (hFix : Rename.FixesPrefix used equiv) (steps : Nat) :
    (Rename.machine equiv machine).runFrom cfg steps =
      Rename.config equiv (machine.runFrom cfg steps) := by
  calc
    (Rename.machine equiv machine).runFrom cfg steps =
        (Rename.machine equiv machine).runFrom
          (Rename.config equiv cfg) steps :=
      congrArg (fun start =>
        (Rename.machine equiv machine).runFrom start steps)
        (rename_config_eq_of_prefix hInv hFix).symm
    _ = Rename.config equiv (machine.runFrom cfg steps) :=
      Rename.runFrom equiv machine cfg steps

/-- Soundness of the TNF-reduced tree for arbitrary four-state machines.
The proof itself performs any required fresh-state permutation; callers do not
assume that the input machine was already in tree normal form. -/
theorem checkFrom_sound {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) :
    forall fuel used table cfg machine,
      checkFrom leaf fuel used table cfg = true ->
      PrefixInvariant used table cfg ->
      table.Agrees machine ->
      Reachable machine cfg ->
      forall steps,
        (machine.runFrom cfg steps).state = none ->
        (machine.runFrom cfg steps).tape.length <= 13 := by
  intro fuel
  induction fuel with
  | zero =>
      intro used table cfg machine hCheck hInv hAgree hReach steps hHalted
      cases hState : cfg.state with
      | none =>
          have hRun := runFrom_of_halted machine cfg hState steps
          have hBound : cfg.tape.length <= 13 :=
            of_decide_eq_true (by
              simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some state =>
          have hLeafCheck : leaf table cfg = true := by
            simpa [checkFrom, hState] using hCheck
          rcases hReach with ⟨start, hCfg⟩
          have hRun : machine.run (start + steps) =
              machine.runFrom cfg steps := by
            rw [hCfg, Machine.run_add_eq_runFrom]
          have hGlobalHalted :
              (machine.run (start + steps)).state = none :=
            (congrArg Config.state hRun).trans hHalted
          exact False.elim
            (hLeaf table cfg machine hAgree hLeafCheck (start + steps)
              hGlobalHalted)
  | succ fuel ih =>
      intro used table cfg machine hCheck hInv hAgree hReach steps hHalted
      cases hState : cfg.state with
      | none =>
          have hRun := runFrom_of_halted machine cfg hState steps
          have hBound : cfg.tape.length <= 13 :=
            of_decide_eq_true (by
              simpa [checkFrom, hState] using hCheck)
          simpa [hRun] using hBound
      | some state =>
          cases steps with
          | zero => simp [Machine.runFrom, hState] at hHalted
          | succ steps =>
              let bit := Tape.read cfg.tape cfg.head
              cases hLookup : table state bit with
              | some assigned =>
                  have hAction := hAgree state bit assigned hLookup
                  have hStep :=
                    stepGo_eq_step machine cfg state assigned hState hAction
                  have hReach' : Reachable machine (stepGo cfg assigned) := by
                    rw [hStep]
                    exact hReach.step
                  have hInv' :
                      PrefixInvariant used table (stepGo cfg assigned) :=
                    hInv.step_known hLookup
                  have hBranch :
                      checkFrom leaf fuel used table
                        (stepGo cfg assigned) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  rw [runFrom_succ_start, ← hStep] at hHalted
                  rw [runFrom_succ_start, ← hStep]
                  exact ih used table (stepGo cfg assigned) machine hBranch
                    hInv' hAgree hReach' steps hHalted
              | none =>
                  have hNode :
                      (haltWritesSafe cfg &&
                        (canonicalActions used).all fun action =>
                          checkFrom leaf fuel (grow used action)
                            (table.set state bit action)
                            (stepGo cfg action)) = true := by
                    simpa [checkFrom, hState, bit, hLookup] using hCheck
                  have hParts := Bool.and_eq_true_iff.mp hNode
                  cases hTransition : machine.transition state bit with
                  | mk write move next =>
                      cases next with
                      | none =>
                          have hStepState : (machine.step cfg).state = none := by
                            simp [Machine.step, hState, bit, hTransition]
                          rw [runFrom_succ_start]
                          rw [runFrom_of_halted machine (machine.step cfg)
                            hStepState steps]
                          simpa [Machine.step, hState, bit, hTransition] using
                            haltWritesSafe_sound hParts.1 write
                      | some next =>
                          by_cases hCanonical : next.val <= used
                          · let action : GoAction := { write, move, next }
                            have hAction :
                                action.toAction =
                                  machine.transition state bit := by
                              simp [action, GoAction.toAction, hTransition]
                            have hMember : action ∈ canonicalActions used :=
                              mem_canonicalActions action hCanonical
                            have hBranch :
                                checkFrom leaf fuel (grow used action)
                                  (table.set state bit action)
                                  (stepGo cfg action) = true :=
                              (List.all_eq_true.mp hParts.2) action hMember
                            have hInv' :
                                PrefixInvariant (grow used action)
                                  (table.set state bit action)
                                  (stepGo cfg action) :=
                              hInv.step_fresh hState
                            have hAgree' :
                                (table.set state bit action).Agrees machine :=
                              PTable.set_agrees hAgree hAction
                            have hStep := stepGo_eq_step machine cfg state
                              action hState hAction
                            have hReach' :
                                Reachable machine (stepGo cfg action) := by
                              rw [hStep]
                              exact hReach.step
                            rw [runFrom_succ_start, ← hStep] at hHalted
                            rw [runFrom_succ_start, ← hStep]
                            exact ih (grow used action)
                              (table.set state bit action) (stepGo cfg action)
                              machine hBranch hInv' hAgree' hReach' steps
                              hHalted
                          · have hUsedNext : used < next.val :=
                              Nat.lt_of_not_ge hCanonical
                            have hUsedFour : used < 4 := by omega
                            let fresh : Fin 4 := ⟨used, hUsedFour⟩
                            let equiv : Perm := Perm.swap next fresh
                            let renamed : Machine 4 :=
                              Rename.machine equiv machine
                            let action : GoAction := { write, move, next := fresh }
                            have hFix : Rename.FixesPrefix used equiv := by
                              apply Rename.swap_fixesPrefix
                              · exact Nat.le_of_lt hUsedNext
                              · simp [fresh]
                            have hStateFix : equiv state = state :=
                              hFix state (hInv.state_prefix state hState)
                            have hStateSymm : equiv.symm state = state := by
                              have hRoundTrip :=
                                Perm.symm_apply_apply equiv state
                              simpa [hStateFix] using hRoundTrip
                            have hAction : action.toAction =
                                renamed.transition state bit := by
                              change action.toAction =
                                Rename.action equiv
                                  (machine.transition (equiv.symm state) bit)
                              rw [hStateSymm, hTransition]
                              simp [action, fresh, equiv, Rename.action,
                                GoAction.toAction, Perm.swap_apply_left]
                            have hMember : action ∈ canonicalActions used := by
                              apply mem_canonicalActions
                              simp [action, fresh]
                            have hBranch :
                                checkFrom leaf fuel (grow used action)
                                  (table.set state bit action)
                                  (stepGo cfg action) = true :=
                              (List.all_eq_true.mp hParts.2) action hMember
                            have hInv' :
                                PrefixInvariant (grow used action)
                                  (table.set state bit action)
                                  (stepGo cfg action) :=
                              hInv.step_fresh hState
                            have hAgreeRenamed : table.Agrees renamed :=
                              agrees_rename_of_prefix hInv hAgree hFix
                            have hAgree' :
                                (table.set state bit action).Agrees renamed :=
                              PTable.set_agrees hAgreeRenamed hAction
                            have hReachRenamed : Reachable renamed cfg :=
                              reachable_rename_of_prefix hInv hReach hFix
                            have hStep := stepGo_eq_step renamed cfg state
                              action hState hAction
                            have hReach' :
                                Reachable renamed (stepGo cfg action) := by
                              rw [hStep]
                              exact hReachRenamed.step
                            have hRunRename :
                                renamed.runFrom cfg (steps + 1) =
                                  Rename.config equiv
                                    (machine.runFrom cfg (steps + 1)) :=
                              runFrom_rename_of_prefix hInv hFix (steps + 1)
                            have hHaltedRenamed :
                                (renamed.runFrom cfg (steps + 1)).state = none := by
                              rw [hRunRename]
                              simp [Rename.config, hHalted]
                            rw [runFrom_succ_start, ← hStep] at hHaltedRenamed
                            have hBound :
                                (renamed.runFrom (stepGo cfg action) steps).tape.length
                                  <= 13 :=
                              ih (grow used action)
                                (table.set state bit action) (stepGo cfg action)
                                renamed hBranch hInv' hAgree' hReach' steps
                                hHaltedRenamed
                            have hBoundFull :
                                (renamed.runFrom cfg (steps + 1)).tape.length
                                  <= 13 := by
                              rw [runFrom_succ_start, ← hStep]
                              exact hBound
                            rw [hRunRename] at hBoundFull
                            simpa [Rename.config] using hBoundFull

theorem rootInvariant :
    PrefixInvariant 1 PTable.empty (initial 4) := by
  refine
    { positive := by decide
      bounded := by decide
      table_prefix := ?_
      state_prefix := ?_ }
  · intro state bit action hLookup
    cases hLookup
  · intro state hState
    simp [initial, startState] at hState
    subst state
    decide

/-- Conditional score bound exported in the same style as the unreduced
search: any independently proved `LeafSound` implementation may be plugged in. -/
theorem upperBound_of_check {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) (hCheck : check leaf = true) {score : Nat} :
    AttainableScore 4 score -> score <= 13 := by
  rintro ⟨machine, steps, hState, hScore⟩
  have hBound := checkFrom_sound hLeaf 107 1 PTable.empty (initial 4)
    machine hCheck rootInvariant (PTable.empty_agrees machine) ⟨0, rfl⟩
    steps
  have hRun : machine.runFrom (initial 4) steps = machine.run steps := by
    simpa [Machine.run] using
      (Machine.run_add_eq_runFrom machine 0 steps).symm
  rw [hRun] at hBound
  calc
    score = (machine.run steps).tape.length := hScore.symm
    _ <= 13 := hBound hState

end TNF
end BB4
end BusyBeaver
end SetTheory
