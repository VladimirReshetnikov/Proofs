(** Exact-interface and assumption audit for raw universal elimination. *)

From BoundedPAConsistency Require Import RawCodedProofAllEConstructor.

Import PABoundedRawCodedProofAllEConstructor.

Check rawProofAllERoot.
Check raw_proofAllERoot_child_lt.
Check raw_proofAllE_syntax_step.
Check raw_proofAllE_endpoint_rule_complete.
Check raw_proofAllE_endpoint.
Check raw_proofAllE_ruleCoverage.

Print Assumptions raw_proofAllE_endpoint_rule_complete.
Print Assumptions raw_proofAllE_ruleCoverage.
