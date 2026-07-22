import BoundedPAConsistency.StagedTruthCertificateProofCompiler

/-!
# Kernel audit for staged truth-certificate compilation

The audit fixes the dependency-aware interface and verifies that compilation
still produces an ordinary represented PA proof without project axioms.
-/

namespace LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompilerAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler

#check localContext
#check crossContext
#check shiftContext
#check substitutionContext
#check soundnessContext
#check PAStagedTruthCertificateStep
#check PAStagedTruthCertificateStep.target
#check PAStagedTruthCertificateStep.compile
#check PAStagedTruthCertificateStep.compile_isProof
#check PAStagedTruthCertificateStep.compile_isPAProof

#print axioms PAStagedTruthCertificateStep.compile
#print axioms PAStagedTruthCertificateStep.compile_isProof
#print axioms PAStagedTruthCertificateStep.compile_isPAProof

end LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompilerAudit
