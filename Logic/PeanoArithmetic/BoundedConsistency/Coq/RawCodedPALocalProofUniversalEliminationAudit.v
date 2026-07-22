(** Exact-interface and assumption audit for local universal elimination. *)

From BoundedPAConsistency Require Import
  RawCodedPALocalProofUniversalElimination.

Import PABoundedRawCodedPALocalProofUniversalElimination.

Check raw_codedPALocalProofOf_allE.

Print Assumptions raw_codedPALocalProofOf_allE.
