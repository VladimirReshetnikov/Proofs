import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Kernel audit for truth-certificate context projection

The declarations checked here must remain proof-producing Hilbert-system
combinators.  In particular, context projection must not be replaced by a
semantic implication or by an assumption about the ambient model.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateContextProjectionAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

#check TruthCertificateFields.proveLocalStep
#check TruthCertificateFields.proveCrossLevel
#check TruthCertificateFields.proveShiftInvariant
#check TruthCertificateFields.proveSubstitutionInvariant
#check TruthCertificateFields.proveAxiomSound
#check TruthCertificateFields.proveFinalConsistency
#check PAInductionKernel.recontextualize
#check PAInductionKernel.underCrossLevel
#check PAInductionKernel.underSubstitutionInvariant

#print axioms TruthCertificateFields.proveLocalStep
#print axioms TruthCertificateFields.proveCrossLevel
#print axioms TruthCertificateFields.proveShiftInvariant
#print axioms TruthCertificateFields.proveSubstitutionInvariant
#print axioms TruthCertificateFields.proveAxiomSound
#print axioms TruthCertificateFields.proveFinalConsistency
#print axioms PAInductionKernel.recontextualize
#print axioms PAInductionKernel.underCrossLevel
#print axioms PAInductionKernel.underSubstitutionInvariant

end LeanProofs.BoundedPAConsistency.TruthCertificateContextProjectionAudit
