(** Exact-interface and assumption audit for binary coverage composition. *)

From BoundedPAConsistency Require Import RawCodedProofBinaryCoverage.

Import PABoundedRawCodedProofBinaryCoverage.

Check raw_proofBinary_ruleCoverage.

Print Assumptions raw_proofBinary_ruleCoverage.
