import BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof

/-!
# Audit: fixed-source existential laws for a successor truth predicate

The source sentence computes the successor's upper level as
`lowerLevel + 1`.  Its only non-arithmetic assumption is coordinatewise
congruence for the opaque lower truth predicate; the completeness argument
therefore passes through the equality quotient before interpreting the
source sentence.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProofAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProof

#check sourceDerivedSuccessorTruthFormula
#check sourceSuccessorExistentialLawsSentence
#check sourceCongruentSuccessorExistentialLawsSentence
#check sourceCongruentSuccessorExistentialLawsProof
#check compiledSuccessorExistentialLawsProof
#check orbitSuccessorExistentialLawsProof

#print axioms sourceCongruentSuccessorExistentialLawsProof
#print axioms orbitSuccessorExistentialLawsProof

end LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialLawsProofAudit
