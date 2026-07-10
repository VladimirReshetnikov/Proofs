/-
  BusyBeaverBB3/Complete.lean

  The cheapest nonhalting leaf certificate: a partial table in which all six
  entries are assigned.  Since partial tables store only continuing actions,
  any agreeing total machine then has no halting transition at all.
-/

import SetTheory.BusyBeaverBB3.Search

namespace SetTheory
namespace BusyBeaver
namespace BB3

private abbrev A : Fin 3 := 0
private abbrev B : Fin 3 := 1
private abbrev C : Fin 3 := 2

/-- Executable test that all six state/symbol slots contain continuing
transitions. -/
def tableComplete (table : PTable) : Bool :=
  (table A false).isSome && ((table A true).isSome &&
  ((table B false).isSome && ((table B true).isSome &&
  ((table C false).isSome && (table C true).isSome))))

theorem tableComplete_assigned {table : PTable} (h : tableComplete table = true)
    (q : Fin 3) (bit : Bool) : ∃ action, table q bit = some action := by
  have hParts :
      (table A false).isSome = true ∧ (table A true).isSome = true ∧
      (table B false).isSome = true ∧ (table B true).isSome = true ∧
      (table C false).isSome = true ∧ (table C true).isSome = true := by
    simpa [tableComplete, Bool.and_eq_true] using h
  rcases q with ⟨q, hq⟩
  have hCases : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hCases with rfl | rfl | rfl <;> cases bit
  · exact Option.isSome_iff_exists.mp hParts.1
  · exact Option.isSome_iff_exists.mp hParts.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.1
  · exact Option.isSome_iff_exists.mp hParts.2.2.2.2.2

/-- A total machine agreeing with a complete continuing table stays active at
every time. -/
theorem tableComplete_run_active {table : PTable} {M : Machine 3}
    (hComplete : tableComplete table = true) (hAgree : table.Agrees M) :
    forall t, (M.run t).state ≠ none
  | 0 => by simp [Machine.run, initial, startState]
  | t + 1 => by
      have hPrevious := tableComplete_run_active hComplete hAgree t
      cases hState : (M.run t).state with
      | none => exact False.elim (hPrevious hState)
      | some q =>
          let bit := Tape.read (M.run t).tape (M.run t).head
          obtain ⟨action, hLookup⟩ := tableComplete_assigned hComplete q bit
          have hAction := hAgree q bit action hLookup
          simp [Machine.run, Machine.step, hState, bit, ← hAction,
            GoAction.toAction]

/-- Leaf wrapper used as the first, very fast stage of the BB(3) pipeline. -/
def completeLeaf (table : PTable) (_cfg : Config 3) : Bool :=
  tableComplete table

theorem completeLeaf_sound : LeafSound completeLeaf := by
  intro table _cfg M hAgree hComplete t
  exact tableComplete_run_active hComplete hAgree t

end BB3
end BusyBeaver
end SetTheory
