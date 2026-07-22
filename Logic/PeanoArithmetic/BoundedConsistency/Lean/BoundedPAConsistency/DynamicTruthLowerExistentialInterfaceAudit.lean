import BoundedPAConsistency.DynamicTruthLowerExistentialInterface

/-!
# Axiom audit for the direct lower-existential interface

This small boundary records that both the source semantics and the compiled
positive-orbit proof remain kernel checked.  In particular, the production
theorem is a typed PA proof object, not a metatheoretic truth assertion.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterfaceAudit

open LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterface

#check lowerExistentialLawsFormula
#check eval_sourceLowerExistentialLawsSentence
#check successorExistentialLawsFormula_eq_lowerExistentialLawsFormula
#check orbitLowerExistentialLawsProof

#print axioms eval_sourceLowerExistentialLawsSentence
#print axioms successorExistentialLawsFormula_eq_lowerExistentialLawsFormula
#print axioms orbitLowerExistentialLawsProof

end LeanProofs.BoundedPAConsistency.DynamicTruthLowerExistentialInterfaceAudit
