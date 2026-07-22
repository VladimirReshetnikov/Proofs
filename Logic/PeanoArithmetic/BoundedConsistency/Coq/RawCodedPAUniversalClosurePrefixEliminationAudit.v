(** Assumption audit for the exact universal-closure prefix step. *)

From BoundedPAConsistency Require Import
  RawCodedPAUniversalClosurePrefixElimination.

Import PABoundedRawCodedPAUniversalClosurePrefixElimination.

Check raw_codedPALocalProofOf_universalClosure_prefix_step.

Print Assumptions
  raw_codedPALocalProofOf_universalClosure_prefix_step.
