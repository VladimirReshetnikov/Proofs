(** Exact-interface and assumption audit for unary coverage composition. *)

From BoundedPAConsistency Require Import RawCodedProofUnaryCoverage.

Import PABoundedRawCodedProofUnaryCoverage.

Check raw_proofUnary_ruleCoverage.

Print Assumptions raw_proofUnary_ruleCoverage.
