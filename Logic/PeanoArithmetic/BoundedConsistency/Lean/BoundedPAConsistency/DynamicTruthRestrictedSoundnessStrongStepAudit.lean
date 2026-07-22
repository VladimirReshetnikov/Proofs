import BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep

/-!
# Audit: the compiled restricted-soundness strong step

The fixed source context contains exactly the five semantic ingredients
consumed by the local restricted-calculus rule theorem.  The final proof is
kept behind an explicit congruence antecedent, so source completeness may
normalize the opaque lower predicate without postulating extensionality for
its arbitrary interpretation.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStepAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStep

#check sourceAdjacentLevels
#check sourceSoundnessLawContext
#check sourceRestrictedSoundnessStrongStepSentence
#check sourceCongruentRestrictedSoundnessStrongStepSentence
#check eval_sourceAdjacentLevels
#check eval_sourceSoundnessLawContext
#check sourceCongruentRestrictedSoundnessStrongStepProof

#print axioms eval_sourceSoundnessLawContext
#print axioms sourceCongruentRestrictedSoundnessStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessStrongStepAudit
