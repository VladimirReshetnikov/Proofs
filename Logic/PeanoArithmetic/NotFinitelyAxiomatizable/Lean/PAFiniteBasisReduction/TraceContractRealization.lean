import PAFiniteBasisReduction.TraceContractAssembly
import PAFiniteBasisReduction.StandardTraceFunctionality

/-!
# Realizing the evaluator-cut contract

Strong-induction functionality of arbitrary standard trace tables discharges
the last interface in `TraceContractAssembly`.  This yields the unconditional
countermodel family and hence the unconditional non-finite-axiomatizability
theorem for first-order Peano Arithmetic.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

namespace FiniteSkolemCut
namespace ProgramTrace

/-- The fixed trace evaluator satisfies the standard-code functionality
interface required by the countermodel assembly. -/
theorem traceEvaluator_standardCode_functionality :
    TraceEvaluatorStandardCodeFunctional := by
  intro alpha M S rank generator hPA hLtRank hBetaRank target x y hx hy
  exact traceEvaluator_standardCode_functional M S rank generator hPA
    hLtRank hBetaRank target hx hy

/-- At every finite syntactic rank there is a Skolem-hull countermodel whose
fixed trace evaluator realizes the proper-cut contract. -/
theorem trace_contractCountermodels :
    EvaluatorCutContract.ContractCountermodels.{0} :=
  trace_contractCountermodels_of_functionality
    traceEvaluator_standardCode_functionality

/-- First-order Peano Arithmetic in its original language has no finite
sentence axiomatization. -/
theorem pa_not_finitely_axiomatizable :
    ¬FiniteAxiomatization PA.Formula.Ax_s :=
  EvaluatorCutContract.pa_not_finitely_axiomatizable_of_contracts
    trace_contractCountermodels

end ProgramTrace
end FiniteSkolemCut

end PAFiniteBasisReduction
end LeanProofs
