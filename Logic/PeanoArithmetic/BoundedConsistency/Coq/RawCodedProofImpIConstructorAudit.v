(** Public surface and assumption audit for implication introduction. *)

From BoundedPAConsistency Require Import RawCodedProofImpIConstructor.

Import PABoundedRawCodedProofImpIConstructor.

Check rawProofImpIRoot.
Check raw_proofImpIRoot_child_lt.
Check raw_proofImpIRoot_list_view.
Check raw_proofImpIRoot_recursive_children.
Check raw_proofImpI_syntax_step.
Check raw_proofImpI_endpoint_rule_complete.
Check raw_proofImpI_endpoint.
Check raw_proofImpI_ruleCoverage.

Print Assumptions raw_proofImpIRoot_list_view.
Print Assumptions raw_proofImpIRoot_recursive_children.
Print Assumptions raw_proofImpI_syntax_step.
Print Assumptions raw_proofImpI_endpoint_rule_complete.
Print Assumptions raw_proofImpI_endpoint.
Print Assumptions raw_proofImpI_ruleCoverage.
