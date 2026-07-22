(** Public surface and assumption audit for universal introduction. *)

From BoundedPAConsistency Require Import RawCodedProofAllIConstructor.

Import PABoundedRawCodedProofAllIConstructor.

Check rawProofAllIRoot.
Check raw_proofAllIRoot_child_lt.
Check raw_proofAllIRoot_list_view.
Check raw_proofAllIRoot_recursive_children.
Check raw_proofAllI_syntax_step.
Check raw_proofAllI_endpoint_rule_complete.
Check raw_proofAllI_endpoint.
Check raw_proofAllI_ruleCoverage.

Print Assumptions raw_proofAllIRoot_list_view.
Print Assumptions raw_proofAllIRoot_recursive_children.
Print Assumptions raw_proofAllI_syntax_step.
Print Assumptions raw_proofAllI_endpoint_rule_complete.
Print Assumptions raw_proofAllI_endpoint.
Print Assumptions raw_proofAllI_ruleCoverage.
