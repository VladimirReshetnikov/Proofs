(** Exact-interface and assumption audit for raw conjunction introduction. *)

From BoundedPAConsistency Require Import RawCodedProofAndIConstructor.

Import PABoundedRawCodedProofAndIConstructor.

Check rawProofAndIRoot.
Check raw_proofAndIRoot_left_child_lt.
Check raw_proofAndIRoot_right_child_lt.
Check raw_proofAndI_syntax_step.
Check raw_proofAndI_endpoint_rule_complete.
Check raw_proofAndI_endpoint.
Check raw_proofAndI_ruleCoverage.

Print Assumptions raw_proofAndI_ruleCoverage.
