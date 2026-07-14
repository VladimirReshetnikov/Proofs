/-
  BusyBeaverBB4/Partial.lean

  Four-state specialization of the generic relative-head partial-machine
  semantics and its bridge to local finite-support Rado machines.
-/

import BusyBeaver.BB4.Search
import BusyBeaver.BB3.Partial

namespace SetTheory
namespace BusyBeaver
namespace BB4

open BB3

theorem initial_four_toPConfig? :
    LocalConfig.toPConfig? (initial 4) =
      some (PConfig.blank (0 : Fin 4) false) := by
  rfl

/-- Nonhalting of the partial view implies nonhalting in the repository's
four-state total-machine semantics. -/
theorem ofMachine_nonhalts_run_four {machine : Machine 4}
    (h : (BB3.PTM.ofMachine machine).Nonhalts (0 : Fin 4) false) :
    forall steps, (machine.run steps).state ≠ none := by
  intro steps hHalted
  rcases h steps with ⟨result, hRun⟩
  have hBridge := BB3.PTM.ofMachine_runFrom_toPConfig? machine
    initial_four_toPConfig? steps
  have hRunFrom : machine.runFrom (initial 4) steps = machine.run steps := by
    simpa [Machine.run] using
      (Machine.run_add_eq_runFrom machine 0 steps).symm
  rw [hRunFrom] at hBridge
  simp [LocalConfig.toPConfig?, hHalted] at hBridge
  rw [hBridge] at hRun
  contradiction

namespace PTable

/-- Interpret every assigned continuing action as a generic PTM transition. -/
def toPTM (table : PTable) : BB3.PTM (Fin 4) Bool :=
  fun state symbol =>
    (table state symbol).map fun action =>
      { write := action.write, move := action.move, next := action.next }

@[simp]
theorem toPTM_apply (table : PTable) (state : Fin 4) (symbol : Bool) :
    table.toPTM state symbol =
      (table state symbol).map fun action =>
        ({ write := action.write, move := action.move, next := action.next } :
          BB3.PAction (Fin 4) Bool) :=
  rfl

theorem ofMachine_extends {table : PTable} {machine : Machine 4}
    (hAgree : table.Agrees machine) :
    (BB3.PTM.ofMachine machine).Extends table.toPTM := by
  intro state symbol action hAction
  cases hLookup : table state symbol with
  | none => simp [toPTM, hLookup] at hAction
  | some goAction =>
      have hEq :
          ({ write := goAction.write, move := goAction.move,
             next := goAction.next } : BB3.PAction (Fin 4) Bool) = action := by
        simpa [toPTM, hLookup] using hAction
      subst action
      have hTransition := hAgree state symbol goAction hLookup
      unfold BB3.PTM.ofMachine
      rw [← hTransition]
      rfl

theorem nonhalts_machine_of_agrees {table : PTable} {machine : Machine 4}
    (hTable : table.toPTM.Nonhalts (0 : Fin 4) false)
    (hAgree : table.Agrees machine) :
    forall steps, (machine.run steps).state ≠ none := by
  apply ofMachine_nonhalts_run_four
  exact (ofMachine_extends hAgree).nonhalts hTable

end PTable

end BB4
end BusyBeaver
end SetTheory
