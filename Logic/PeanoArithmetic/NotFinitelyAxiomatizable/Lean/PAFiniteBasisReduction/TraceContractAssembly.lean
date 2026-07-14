import PAFiniteBasisReduction.TotalTraceEvaluator

/-!
# Assembling evaluator-cut countermodels

This module packages the compactness model, bounded-rank Skolem hull, and
trace-evaluator totality.  Its sole input is standard-code functionality of
that evaluator; `StandardTraceFunctionality` discharges it in the final
realization module.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

namespace FiniteSkolemCut
namespace ProgramTrace

/-- The one remaining interface needed when assembling the already-proved
trace-evaluator totality into `EvaluatorCutContract.Contract`. -/
def TraceEvaluatorStandardCodeFunctional : Prop :=
  ∀ (alpha : Type) (M : PA.PreModel alpha) (S : CanonicalSelectors M)
    (rank : Nat) (generator : alpha),
    RawPASatisfies M →
    formulaRank traceLtFormula ≤ rank →
    formulaRank traceBetaFormula ≤ rank →
    ∀ (target : Nat) {x y : Carrier M S rank generator},
      EvaluatorCutContract.Evaluates
          (preModel M S rank generator) (traceEvaluator rank)
          (⟨generator, Hull.star⟩ : Carrier M S rank generator)
          (PA.Term.numeralValue (preModel M S rank generator) target) x →
      EvaluatorCutContract.Evaluates
          (preModel M S rank generator) (traceEvaluator rank)
          (⟨generator, Hull.star⟩ : Carrier M S rank generator)
          (PA.Term.numeralValue (preModel M S rank generator) target) y →
      x = y

/-- Standard-code functionality, together with the canonical total trace,
produces evaluator-cut countermodels for all finite PA rank fragments. -/
theorem trace_contractCountermodels_of_functionality
    (hFunctional : TraceEvaluatorStandardCodeFunctional) :
    EvaluatorCutContract.ContractCountermodels.{0} := by
  intro n
  rcases NonstandardHFFin.nonstandardHFFin_fofam_exists with
    ⟨V, ambient, generator, hgenerator⟩
  let M : PA.PreModel (AckermannHF.PAInHF.FOFAMOrdinal ambient) :=
    AckermannHF.PAInHF.fofamPAPreModel ambient
  let S : CanonicalSelectors M := fofamCanonicalSelectors ambient
  let rank : Nat := traceConstructionRank n
  let KM := preModel M S rank generator
  let seed : Carrier M S rank generator := ⟨generator, Hull.star⟩
  let e : Nat → Carrier M S rank generator := fun _ => KM.zero
  have hPA : RawPASatisfies M := by
    intro env f hf
    exact AckermannHF.PAInHF.fofam_PA_Ax_s_valid ambient f env hf
  have hgenerator' : ∀ k,
      RawLt M (PA.Term.numeralValue M k) generator := by
    simpa [M] using
      (fofam_star_above_all_numerals ambient generator hgenerator)
  have hSupport : ProgramBetaCoding.supportRank ≤ rank := by
    simpa [rank] using programBetaSupport_le_traceConstructionRank n
  have hLtRank : formulaRank traceLtFormula ≤ rank := by
    simpa [rank] using traceLtFormula_rank_le_traceConstructionRank n
  have hBetaRank : formulaRank traceBetaFormula ≤ rank := by
    simpa [rank] using traceBetaFormula_rank_le_traceConstructionRank n
  have hContractLtRank :
      formulaRank EvaluatorCutContract.hullLtFormula ≤ rank := by
    simpa [EvaluatorCutContract.hullLtFormula, traceLtFormula] using hLtRank
  have hFragmentRank : fragmentSemanticRank n ≤ rank := by
    simpa [rank] using fragmentSemanticRank_le_traceConstructionRank n
  refine ⟨Carrier M S rank generator, KM, traceEvaluator rank, seed, e,
    ?_, ?_⟩
  · dsimp only [KM, seed]
    apply EvaluatorCutContract.hull_contract_of_ambient_pa
      M S rank generator hPA hContractLtRank hgenerator'
      (traceEvaluator rank)
    · exact traceEvaluator_standardCode_total M S rank generator hPA
        hSupport hLtRank hBetaRank
    · exact hFunctional _ M S rank generator hPA hLtRank hBetaRank
  · dsimp only [KM] at e ⊢
    exact EvaluatorCutContract.hull_sat_rankFragment_of_le
      M S rank generator n hFragmentRank hPA e

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
