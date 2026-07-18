(** Assumption audit for coverage-wide eigenvariable context truth. *)

From BoundedPAConsistency Require Import
  RawCodedRestrictedProofEigenContextTruth.

Import PABoundedRawCodedRestrictedProofEigenContextTruth.

Check raw_contextAllCodesBelow_member.
Check raw_eigenContext_assignment_defined_of_below.
Check raw_eigenContextShift_sigma_true.

Print Assumptions raw_contextAllCodesBelow_member.
Print Assumptions raw_eigenContext_assignment_defined_of_below.
Print Assumptions raw_eigenContextShift_sigma_true.
