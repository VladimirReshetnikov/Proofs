/-
  BusyBeaverBB4/SporadicLeaf.lean

  Executable recognition of the two RepWL-only nonhalting partial tables.
-/

import BusyBeaver.BB4.Complete
import BusyBeaver.BB4.Sporadic

namespace SetTheory
namespace BusyBeaver
namespace BB4

open BB3

private abbrev A : Fin 4 := 0
private abbrev B : Fin 4 := 1
private abbrev C : Fin 4 := 2
private abbrev D : Fin 4 := 3

private def slotEq (table : PTable) (target : PTM (Fin 4) Bool)
    (state : Fin 4) (symbol : Bool) : Bool :=
  decide (table.toPTM state symbol = target state symbol)

/-- Extensional equality with a fixed eight-slot partial machine. -/
def tableMatches (table : PTable) (target : PTM (Fin 4) Bool) : Bool :=
  slotEq table target A false && (slotEq table target A true &&
  (slotEq table target B false && (slotEq table target B true &&
  (slotEq table target C false && (slotEq table target C true &&
  (slotEq table target D false && slotEq table target D true))))))

theorem tableMatches_eq {table : PTable} {target : PTM (Fin 4) Bool}
    (h : tableMatches table target = true) : table.toPTM = target := by
  have hParts :
      slotEq table target A false = true ∧
      slotEq table target A true = true ∧
      slotEq table target B false = true ∧
      slotEq table target B true = true ∧
      slotEq table target C false = true ∧
      slotEq table target C true = true ∧
      slotEq table target D false = true ∧
      slotEq table target D true = true := by
    simpa [tableMatches, Bool.and_eq_true] using h
  funext state symbol
  rcases state with ⟨state, hState⟩
  have hCases : state = 0 ∨ state = 1 ∨ state = 2 ∨ state = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl <;> cases symbol
  · exact of_decide_eq_true hParts.1
  · exact of_decide_eq_true hParts.2.1
  · exact of_decide_eq_true hParts.2.2.1
  · exact of_decide_eq_true hParts.2.2.2.1
  · exact of_decide_eq_true hParts.2.2.2.2.1
  · exact of_decide_eq_true hParts.2.2.2.2.2.1
  · exact of_decide_eq_true hParts.2.2.2.2.2.2.1
  · exact of_decide_eq_true hParts.2.2.2.2.2.2.2

def sporadicLeaf (table : PTable) (_cfg : Config 4) : Bool :=
  tableMatches table Sporadic.machine1Fin ||
  tableMatches table Sporadic.machine2Fin

theorem sporadicLeaf_sound : LeafSound sporadicLeaf := by
  intro table _cfg machine hAgree hMatch steps
  have hCases := Bool.or_eq_true_iff.mp hMatch
  rcases hCases with hFirst | hSecond
  · have hEq := tableMatches_eq hFirst
    apply PTable.nonhalts_machine_of_agrees _ hAgree steps
    rw [hEq]
    exact Sporadic.machine1Fin_nonhalts
  · have hEq := tableMatches_eq hSecond
    apply PTable.nonhalts_machine_of_agrees _ hAgree steps
    rw [hEq]
    exact Sporadic.machine2Fin_nonhalts

end BB4
end BusyBeaver
end SetTheory
