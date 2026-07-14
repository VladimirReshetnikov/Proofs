/-
  BusyBeaver/BB4/Complete.lean

  Fast nonhalting certificate for partial tables with all eight continuing
  transitions assigned.
-/

import BusyBeaver.BB4.Partial

namespace SetTheory
namespace BusyBeaver
namespace BB4

private abbrev A : Fin 4 := 0
private abbrev B : Fin 4 := 1
private abbrev C : Fin 4 := 2
private abbrev D : Fin 4 := 3

def tableComplete (table : PTable) : Bool :=
  (table A false).isSome && ((table A true).isSome &&
  ((table B false).isSome && ((table B true).isSome &&
  ((table C false).isSome && ((table C true).isSome &&
  ((table D false).isSome && (table D true).isSome))))))

theorem tableComplete_assigned {table : PTable}
    (h : tableComplete table = true) (q : Fin 4) (bit : Bool) :
    ∃ action, table q bit = some action := by
  have hParts :
      (table A false).isSome = true ∧ (table A true).isSome = true ∧
      (table B false).isSome = true ∧ (table B true).isSome = true ∧
      (table C false).isSome = true ∧ (table C true).isSome = true ∧
      (table D false).isSome = true ∧ (table D true).isSome = true := by
    simpa [tableComplete, Bool.and_eq_true] using h
  rcases q with ⟨q, hq⟩
  have hCases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl <;> cases bit
  · exact Option.isSome_iff_exists.mp hParts.1
  · exact Option.isSome_iff_exists.mp hParts.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.2.2.2

theorem tableComplete_run_active {table : PTable} {machine : Machine 4}
    (hComplete : tableComplete table = true)
    (hAgree : table.Agrees machine) :
    forall t, (machine.run t).state ≠ none
  | 0 => by simp [Machine.run, initial, startState]
  | t + 1 => by
      have hPrevious := tableComplete_run_active hComplete hAgree t
      cases hState : (machine.run t).state with
      | none => exact False.elim (hPrevious hState)
      | some q =>
          let bit := Tape.read (machine.run t).tape (machine.run t).head
          obtain ⟨action, hLookup⟩ :=
            tableComplete_assigned hComplete q bit
          have hAction := hAgree q bit action hLookup
          simp [Machine.run, Machine.step, hState, bit, ← hAction,
            GoAction.toAction]

def completeLeaf (table : PTable) (_cfg : Config 4) : Bool :=
  tableComplete table

theorem completeLeaf_sound : LeafSound completeLeaf := by
  intro table _cfg machine hAgree hComplete t
  exact tableComplete_run_active hComplete hAgree t

end BB4
end BusyBeaver
end SetTheory
