(** Public surface and kernel-assumption audit for the canonical checker
    trace.  In particular, [CanonicalRestrictedPAProofFormula] is a
    transparent syntax tree and does not use [ClassicalEpsilon.epsilon]. *)

From BoundedPAConsistency Require Import CanonicalCheckerTrace.

Import PABoundedCanonicalCheckerTrace.

Check canonicalRestrictedProofFlag.
Check canonicalCheckerLProgram.
Check canonicalCheckerMMAProgram.
Check canonicalCheckerMMAEnd_eq_length.
Check canonicalMachineTransition.
Check canonicalRestrictedPAProofTermAt.
Check CanonicalRestrictedPAProofFormula.
Check CanonicalRestrictedPAProofFormula_unfold.
Check raw_CanonicalRestrictedPAProofFormula_certificate.
Check canonicalCheckerLProgram_eval.
Check canonicalCheckerMMAProgram_computes.

Print Assumptions CanonicalRestrictedPAProofFormula_unfold.
Print Assumptions raw_CanonicalRestrictedPAProofFormula_certificate.
Print Assumptions canonicalCheckerLProgram_eval.
Print Assumptions canonicalCheckerMMAProgram_computes.
