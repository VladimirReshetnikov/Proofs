import BoundedPAConsistency.DynamicTruthCertificateSemantics

/-!
# Kernel audit for dynamic truth-certificate source semantics

The four realization theorems below are the semantic boundary used by the
final restricted-soundness source proof.  Auditing them together makes an
accidental admission in any represented graph reduction visible.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemanticsAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics

#check eval_sourceCrossLevelSentence
#check eval_sourceShiftInvariantSentence
#check eval_sourceSubstitutionInvariantSentence
#check eval_sourceAxiomSoundnessSentence

#print axioms eval_sourceCrossLevelSentence
#print axioms eval_sourceShiftInvariantSentence
#print axioms eval_sourceSubstitutionInvariantSentence
#print axioms eval_sourceAxiomSoundnessSentence

end LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemanticsAudit
