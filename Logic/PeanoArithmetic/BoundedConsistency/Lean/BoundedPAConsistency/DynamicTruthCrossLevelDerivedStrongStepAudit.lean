import BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep

/-!
# Audit: congruence-safe derived cross-level strong step

The public source theorem keeps coordinatewise congruence for both opaque
ternary predicates as an explicit antecedent.  Completeness is used only
after quotienting a model by its interpreted equality relation.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStep

#check sourcePlaceholderCongruenceContext
#check sourceCongruentDerivedStrongStepSentence
#check sourceCongruentDerivedStrongStepProof

#print axioms sourceCongruentDerivedStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelDerivedStrongStepAudit
