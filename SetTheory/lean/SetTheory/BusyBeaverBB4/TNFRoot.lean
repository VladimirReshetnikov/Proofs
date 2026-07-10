/-
  BusyBeaverBB4/TNFRoot.lean

  Root left/right reduction on top of canonical fresh-state introduction.
  Only right-moving continuing transitions are enumerated at `A0`; an
  arbitrary witness machine is state-canonicalized and reflected in the proof.
-/

import SetTheory.BusyBeaverBB4.TNFReflection

namespace SetTheory
namespace BusyBeaver
namespace BB4
namespace TNF

private abbrev A : Fin 4 := 0
private abbrev B : Fin 4 := 1

def rootActions : List GoAction :=
  (canonicalActions 1).filter fun action => decide (action.move = Move.right)

theorem rootActions_length : rootActions.length = 4 := by
  decide

theorem mem_rootActions (action : GoAction) (hNext : action.next.val <= 1)
    (hMove : action.move = Move.right) : action ∈ rootActions := by
  simp [rootActions, canonicalActions, BB4.action_mem_actionList, hNext, hMove]

/-- The root-specialized executable checker.  The halting writes are retained;
continuing branches use canonical targets and one representative direction. -/
def checkRoot (leaf : PTable -> Config 4 -> Bool) : Bool :=
  haltWritesSafe (initial 4) &&
    rootActions.all fun action =>
      checkFrom leaf 106 (grow 1 action)
        (PTable.empty.set A false action) (stepGo (initial 4) action)

theorem initial_state_A : (initial 4).state = some A :=
  rfl

theorem score_le_of_root_action {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) {machine : Machine 4} {action : GoAction}
    {score : Nat}
    (hBranch : checkFrom leaf 106 (grow 1 action)
      (PTable.empty.set A false action) (stepGo (initial 4) action) = true)
    (hAction : action.toAction = machine.transition A false)
    (hHalts : machine.HaltsWithScore score) : score <= 13 := by
  rcases hHalts with ⟨steps, hHalted, hScore⟩
  cases steps with
  | zero => simp [Machine.run, initial, startState] at hHalted
  | succ steps =>
      have hInv : PrefixInvariant (grow 1 action)
          (PTable.empty.set A false action)
          (stepGo (initial 4) action) :=
        rootInvariant.step_fresh initial_state_A
      have hAgree :
          (PTable.empty.set A false action).Agrees machine :=
        PTable.set_agrees (PTable.empty_agrees machine) hAction
      have hStep := stepGo_eq_step machine (initial 4) A action
        initial_state_A hAction
      have hReach : Reachable machine (stepGo (initial 4) action) := by
        refine ⟨1, ?_⟩
        simpa [Machine.run] using hStep
      have hRun : machine.run (steps + 1) =
          machine.runFrom (stepGo (initial 4) action) steps := by
        rw [show steps + 1 = 1 + steps by omega,
          Machine.run_add_eq_runFrom]
        simp only [Machine.run]
        rw [← hStep]
      rw [hRun] at hHalted hScore
      have hBound := checkFrom_sound hLeaf 106 (grow 1 action)
        (PTable.empty.set A false action) (stepGo (initial 4) action)
        machine hBranch hInv hAgree hReach steps hHalted
      exact hScore ▸ hBound

theorem score_le_of_root_halt {machine : Machine 4} {score : Nat}
    {write : Bool} {move : Move}
    (hSafe : haltWritesSafe (initial 4) = true)
    (hTransition : machine.transition A false =
      { write, move, next := none })
    (hHalts : machine.HaltsWithScore score) : score <= 13 := by
  rcases hHalts with ⟨steps, hHalted, hScore⟩
  cases steps with
  | zero => simp [Machine.run, initial, startState] at hHalted
  | succ steps =>
      have hStepState : (machine.step (initial 4)).state = none := by
        simp [Machine.step, initial, startState, Tape.read, hTransition]
      have hRun : machine.run (steps + 1) = machine.step (initial 4) := by
        rw [show steps + 1 = 1 + steps by omega,
          Machine.run_add_eq_runFrom]
        simp only [Machine.run]
        exact runFrom_of_halted machine (machine.step (initial 4))
          hStepState steps
      rw [hRun] at hScore
      have hBound := haltWritesSafe_sound hSafe write
      calc
        score = (machine.step (initial 4)).tape.length := hScore.symm
        _ <= 13 := by
          simpa [Machine.step, initial, startState, Tape.read, hTransition] using
            hBound

/-- Canonicalize the target of a continuing root transition.  If it is `C` or
`D`, swapping it with `B` fixes `A` and preserves the exact halting score. -/
theorem canonicalize_root_target {machine : Machine 4} {score : Nat}
    {write : Bool} {move : Move} {next : Fin 4}
    (hTransition : machine.transition A false =
      { write, move, next := some next })
    (hHalts : machine.HaltsWithScore score) :
    ∃ canonical : Machine 4, ∃ action : GoAction,
      canonical.HaltsWithScore score ∧
      action.toAction = canonical.transition A false ∧
      action.next.val <= 1 := by
  by_cases hNext : next.val <= 1
  · let action : GoAction := { write, move, next }
    refine ⟨machine, action, hHalts, ?_, hNext⟩
    simp [action, GoAction.toAction, hTransition]
  · have hNextLarge : 1 < next.val := Nat.lt_of_not_ge hNext
    let equiv : Perm := Perm.swap next B
    let canonical : Machine 4 := Rename.machine equiv machine
    let action : GoAction := { write, move, next := B }
    have hFix : Rename.FixesPrefix 1 equiv := by
      apply Rename.swap_fixesPrefix
      · exact Nat.le_of_lt hNextLarge
      · decide
    have hStart : equiv A = A := hFix A (by decide)
    have hStartSymm : equiv.symm A = A := by
      have hRoundTrip := Perm.symm_apply_apply equiv A
      simpa [hStart] using hRoundTrip
    have hCanonicalHalts : canonical.HaltsWithScore score :=
      (Rename.haltsWithScore_iff equiv machine hStart score).2 hHalts
    have hActionNext : action.next.val <= 1 := by
      simp [action, B]
    refine ⟨canonical, action, hCanonicalHalts, ?_, hActionNext⟩
    change action.toAction =
      Rename.action equiv (machine.transition (equiv.symm A) false)
    rw [hStartSymm, hTransition]
    simp [action, equiv, Rename.action, GoAction.toAction,
      Perm.swap_apply_left]

/-- Reflect a canonical-root machine when necessary so its representative
root transition moves right. -/
theorem orient_root {machine : Machine 4} {action : GoAction} {score : Nat}
    (hHalts : machine.HaltsWithScore score)
    (hAction : action.toAction = machine.transition A false)
    (hNext : action.next.val <= 1) :
    ∃ oriented : Machine 4, ∃ orientedAction : GoAction,
      oriented.HaltsWithScore score ∧
      orientedAction.toAction = oriented.transition A false ∧
      orientedAction.next.val <= 1 ∧
      orientedAction.move = Move.right := by
  cases hMove : action.move with
  | right =>
      exact ⟨machine, action, hHalts, hAction, hNext, hMove⟩
  | left =>
      let oriented := Reflect.machine machine
      let orientedAction := Reflect.goAction action
      have hOrientedHalts : oriented.HaltsWithScore score :=
        (Reflect.haltsWithScore_iff machine score).2 hHalts
      refine ⟨oriented, orientedAction, hOrientedHalts, ?_, ?_, ?_⟩
      · rw [Reflect.goAction_toAction, hAction]
        rfl
      · exact hNext
      · simp [orientedAction, Reflect.goAction, Reflect.move, hMove]

/-- A successful root-reflection TNF search proves the global score bound for
all machines; the witness machine is normalized semantically in this proof. -/
theorem upperBound_of_checkRoot {leaf : PTable -> Config 4 -> Bool}
    (hLeaf : LeafSound leaf) (hCheck : checkRoot leaf = true) {score : Nat} :
    AttainableScore 4 score -> score <= 13 := by
  rintro ⟨machine, hHalts⟩
  have hParts := Bool.and_eq_true_iff.mp hCheck
  cases hTransition : machine.transition A false with
  | mk write move next =>
      cases next with
      | none =>
          exact score_le_of_root_halt hParts.1 hTransition hHalts
      | some next =>
          rcases canonicalize_root_target hTransition hHalts with
            ⟨canonical, action, hCanonicalHalts, hAction, hNext⟩
          rcases orient_root hCanonicalHalts hAction hNext with
            ⟨oriented, orientedAction, hOrientedHalts,
              hOrientedAction, hOrientedNext, hOrientedMove⟩
          have hMember : orientedAction ∈ rootActions :=
            mem_rootActions orientedAction hOrientedNext hOrientedMove
          have hBranch :
              checkFrom leaf 106 (grow 1 orientedAction)
                (PTable.empty.set A false orientedAction)
                (stepGo (initial 4) orientedAction) = true :=
            (List.all_eq_true.mp hParts.2) orientedAction hMember
          exact score_le_of_root_action hLeaf hBranch hOrientedAction
            hOrientedHalts

end TNF
end BB4
end BusyBeaver
end SetTheory
