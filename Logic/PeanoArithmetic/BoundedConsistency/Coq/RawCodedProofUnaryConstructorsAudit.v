(** Public surface and assumption audit for unary raw-proof constructors. *)

From BoundedPAConsistency Require Import RawCodedProofUnaryConstructors.

Import PABoundedRawCodedProofUnaryConstructors.

Check rawProofBotERoot.
Check raw_proofBotERoot_child_lt.
Check raw_proofBotERoot_list_view.
Check raw_proofBotERoot_recursive_children.
Check raw_proofBotE_syntax_step.
Check raw_proofBotE_endpoint_rule_complete.
Check raw_proofBotE_endpoint.
Check raw_proofBotE_ruleCoverage.

Print Assumptions raw_proofBotERoot_child_lt.
Print Assumptions raw_proofBotERoot_list_view.
Print Assumptions raw_proofBotERoot_recursive_children.
Print Assumptions raw_proofBotE_syntax_step.
Print Assumptions raw_proofBotE_endpoint_rule_complete.
Print Assumptions raw_proofBotE_endpoint.
Print Assumptions raw_proofBotE_ruleCoverage.
