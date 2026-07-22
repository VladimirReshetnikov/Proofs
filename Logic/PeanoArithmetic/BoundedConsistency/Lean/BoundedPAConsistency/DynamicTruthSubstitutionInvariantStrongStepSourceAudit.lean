import BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource

/-!
# Audit for the fixed-source substitution-invariance strong step

The audit distinguishes the completed off-domain derivation and translation
from the still-explicit constructor-wise valid-domain proof object.  In
particular, `SourceValidDomainStep` contains a lifted-PA derivation; it is not
an axiom, semantic hypothesis, or host-level truth callback.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSourceAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSource

#check sourceAvailableContext
#check sourceStrongPrefix
#check sourceStrongStepSentence
#check sourceValidDomainStrongStepSentence
#check sourceOffDomainStrongStepSentence
#check sourceOffDomainStrongStepProof
#check SourceValidDomainStep
#check SourceValidDomainStep.proveStrongStep
#check availableContextFormula
#check translate_sourceAvailableContext
#check translate_sourceStrongPrefix
#check translate_sourceStrongStepSentence
#check compiledStrongStepProof

#print axioms sourceOffDomainStrongStepProof
#print axioms SourceValidDomainStep.proveStrongStep
#print axioms translate_sourceAvailableContext
#print axioms translate_sourceStrongPrefix
#print axioms translate_sourceStrongStepSentence
#print axioms compiledStrongStepProof

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStrongStepSourceAudit
