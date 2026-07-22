(** Assumption audit for the standard-natural compiler agreement theorem. *)

From BoundedPAConsistency Require Import
  CanonicalCheckerStandardAgreement.

Import PABoundedCanonicalCheckerStandardAgreement.

Check canonicalCheckerMMAEnd_out_code.
Check canonicalCheckerMMAProgram_computes_named.
Check canonicalCheckerAccepts_iff.

Print Assumptions canonicalCheckerMMAEnd_out_code.
Print Assumptions canonicalCheckerMMAProgram_computes_named.
Print Assumptions canonicalCheckerAccepts_iff.
