import BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof

/-!
# Audit: fixed-source positive substitution strong step

This file keeps the equality boundary visible in the public theorem surface.
The source derivation assumes exactly one coordinatewise-congruence sentence
for the ternary placeholder; it does not assume full equality for an
arbitrary expanded prestructure.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProofAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProof

#check lowerPlaceholderRelation
#check sourceLowerCongruenceSentence
#check sourceCongruentStrongStepSentence
#check sourceCongruentStrongStepProof

#print axioms sourceCongruentStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantPositiveRankStrongStepProofAudit
