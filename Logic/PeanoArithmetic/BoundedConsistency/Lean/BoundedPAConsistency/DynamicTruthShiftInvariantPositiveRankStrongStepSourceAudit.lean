import BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource

/-!
# Audit: congruence-safe fixed-source shift-invariance strong step

The source theorem exposes coordinatewise congruence for both opaque ternary
predicates as an antecedent.  Its completeness argument runs only after the
interpreted equality quotient has produced a canonical expanded model.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSourceAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSource

#check sourcePlaceholderCongruenceContext
#check sourceCongruentStrongStepSentence
#check sourceCongruentStrongStepProof

#print axioms sourceCongruentStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantPositiveRankStrongStepSourceAudit
