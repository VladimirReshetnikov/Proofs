import FiniteMatrixNoncharacterizability.Matrix
import FiniteMatrixNoncharacterizability.Kripke

/-!
# No finite characteristic matrix for intuitionistic propositional logic

The matrix and Kripke halves meet here.  The result assumes only that all IPC
theorems are matrix-valid; a fortiori it applies to matrices that preserve all
natural-deduction sequents.
-/

namespace LeanProofs
namespace FiniteMatrixNoncharacterizability

open NaturalDeduction

/-- A finite matrix sound for IPC theorems cannot be complete for IPC
theorems. -/
theorem finite_sound_matrix_not_complete (m : LogicalMatrix V)
    (e : FiniteEncoding V n) (hs : SoundForIPCTheorems m) :
    ¬ CompleteForIPCTheorems m := by
  intro hc
  exact dugundji_not_intuitionistically_derivable n
    (hc (finite_sound_matrix_validates_dugundji m e hs))

/-- Therefore no finite deterministic truth-functional matrix characterizes
intuitionistic propositional logic. -/
theorem no_finite_characteristic_matrix (m : LogicalMatrix V)
    (e : FiniteEncoding V n) : ¬ CharacteristicForIPC m := by
  intro hc
  exact finite_sound_matrix_not_complete m e (characteristic_sound m hc)
    (characteristic_complete m hc)

/-- Headline spelling: no finitely encoded matrix characterizes IPC. -/
theorem no_finite_matrix_characterizes_IPC (m : LogicalMatrix V)
    (e : FiniteEncoding V n) : ¬ CharacteristicForIPC m :=
  no_finite_characteristic_matrix m e

/-- The same result stated with full preservation of intuitionistic
natural-deduction sequents as its soundness premise. -/
theorem finite_rule_sound_matrix_not_complete (m : LogicalMatrix V)
    (e : FiniteEncoding V n) (hs : SoundForIPCSequents m) :
    ¬ CompleteForIPCTheorems m :=
  finite_sound_matrix_not_complete m e (sequent_sound_implies_theorem_sound m hs)

/-- The identity finite encoding for an actual `Fin n` carrier. -/
def finEncoding (n : Nat) : FiniteEncoding (Fin n) n where
  encode := fun x => x
  injective := fun {_ _} h => h

/-- In particular, no deterministic three-valued truth table—regardless of
its designated set and truth functions—has exactly the IPC theorems. -/
theorem no_three_valued_characteristic_matrix (m : LogicalMatrix (Fin 3)) :
    ¬ CharacteristicForIPC m :=
  no_finite_characteristic_matrix m (finEncoding 3)

/-- Headline three-valued corollary. -/
theorem no_three_valued_matrix_characterizes_IPC
    (m : LogicalMatrix (Fin 3)) : ¬ CharacteristicForIPC m :=
  no_three_valued_characteristic_matrix m

/-- Even assuming all IPC theorems valid, a three-valued matrix necessarily
validates a non-theorem (specifically `dugundji 3`). -/
theorem sound_three_valued_matrix_incomplete (m : LogicalMatrix (Fin 3))
    (hs : SoundForIPCTheorems m) : ¬ CompleteForIPCTheorems m :=
  finite_sound_matrix_not_complete m (finEncoding 3) hs

end FiniteMatrixNoncharacterizability
end LeanProofs
