import PAFiniteBasisReduction.ProgramBetaCoding
import PAFiniteBasisReduction.HullTraceTransport

/-!
# Fixed support rank for the program evaluator construction

The hull rank must dominate the requested PA fragment, the two canonical
beta-prepend helper programs, and the fixed order/beta formulas transported
between the hull and the ambient PA model.  It must not depend on the rank of
the full evaluator formula, which itself dispatches over rank-bounded syntax.
-/

namespace LeanProofs
namespace PAFiniteBasisReduction

open SetTheory PA

namespace FiniteSkolemCut
namespace ProgramTrace

/-- The fixed strict-order formula used for child bounds and selector
trichotomy. -/
def traceLtFormula : PA.Formula :=
  PA.Formula.ltTermAt (PA.Term.var 0) (PA.Term.var 1)

/-- The fixed beta-entry formula used to transport table entries and their
functionality. -/
def traceBetaFormula : PA.Formula :=
  PA.Formula.betaTermTermAt
    (PA.Term.var 0) (PA.Term.var 1)
    (PA.Term.var 2) (PA.Term.var 3)

/-- Rank support independent of the requested PA fragment. -/
def traceSupportRank : Nat :=
  max ProgramBetaCoding.supportRank
    (max (formulaRank traceLtFormula) (formulaRank traceBetaFormula))

/-- The closure rank used for the countermodel to rank fragment `n`. -/
def traceConstructionRank (n : Nat) : Nat :=
  max (fragmentSemanticRank n) traceSupportRank

theorem programBetaSupport_le_traceSupportRank :
    ProgramBetaCoding.supportRank ≤ traceSupportRank :=
  Nat.le_max_left _ _

theorem traceLtFormula_rank_le_traceSupportRank :
    formulaRank traceLtFormula ≤ traceSupportRank := by
  exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem traceBetaFormula_rank_le_traceSupportRank :
    formulaRank traceBetaFormula ≤ traceSupportRank := by
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

theorem fragmentSemanticRank_le_traceConstructionRank (n : Nat) :
    fragmentSemanticRank n ≤ traceConstructionRank n :=
  Nat.le_max_left _ _

theorem traceSupportRank_le_traceConstructionRank (n : Nat) :
    traceSupportRank ≤ traceConstructionRank n :=
  Nat.le_max_right _ _

theorem programBetaSupport_le_traceConstructionRank (n : Nat) :
    ProgramBetaCoding.supportRank ≤ traceConstructionRank n :=
  Nat.le_trans programBetaSupport_le_traceSupportRank
    (traceSupportRank_le_traceConstructionRank n)

theorem traceLtFormula_rank_le_traceConstructionRank (n : Nat) :
    formulaRank traceLtFormula ≤ traceConstructionRank n :=
  Nat.le_trans traceLtFormula_rank_le_traceSupportRank
    (traceSupportRank_le_traceConstructionRank n)

theorem traceBetaFormula_rank_le_traceConstructionRank (n : Nat) :
    formulaRank traceBetaFormula ≤ traceConstructionRank n :=
  Nat.le_trans traceBetaFormula_rank_le_traceSupportRank
    (traceSupportRank_le_traceConstructionRank n)

end ProgramTrace
end FiniteSkolemCut
end PAFiniteBasisReduction
end LeanProofs
