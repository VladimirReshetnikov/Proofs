import PAFiniteBasisReduction.ProgramTrace
import PAFiniteBasisReduction.HullTraceTransport

/-!
# Standard program codes inside a bounded-rank hull

Closed polynomial program-code terms normalize in the hull by projecting to
the ambient PA model.  No PA satisfaction hypothesis is placed on the hull.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

universe u

namespace FiniteSkolemCut
namespace ProgramTrace

/-- Hull numerals project to the corresponding ambient numerals. -/
@[simp] theorem hull_numeralValue_val {alpha : Type u}
    (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) :
    ∀ n,
      (PA.Term.numeralValue (preModel M S rank star) n).val =
        PA.Term.numeralValue M n
  | 0 => rfl
  | n + 1 => by
      simp only [PA.Term.numeralValue, preModel_succ_val,
        hull_numeralValue_val M S rank star n]

/-- Every structural program-code term denotes its standard numeral in the
hull.  Soundness is used only for the ambient PA model; equality in the hull
then follows by subtype extensionality. -/
theorem hull_eval_programCodeTerm_eq_numeral {alpha : Type u}
    {M : PA.PreModel alpha} (S : CanonicalSelectors M)
    (rank : Nat) (star : alpha) (hPA : RawPASatisfies M)
    (p : Program rank) (e : Nat → Carrier M S rank star) :
    PA.Term.eval (preModel M S rank star) e (programCodeTerm p) =
      PA.Term.numeralValue (preModel M S rank star) (Program.code p) := by
  apply Subtype.ext
  rw [termEval_val]
  rw [eval_programCodeTerm_eq_numeral hPA p (fun i => (e i).val)]
  exact (hull_numeralValue_val M S rank star (Program.code p)).symm

end ProgramTrace
end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
