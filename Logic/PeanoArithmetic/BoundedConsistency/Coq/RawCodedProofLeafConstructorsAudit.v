(** Public surface and assumption audit for raw proof leaves. *)

From BoundedPAConsistency Require Import RawCodedProofLeafConstructors.

Import PABoundedRawCodedProofLeafConstructors.

Check rawProofLemRoot.
Check rawProofLemConclusion.
Check raw_proofLemRoot_list_view.
Check raw_proofLemRoot_not_recursive_case.
Check raw_singleProofRoot_supported_eq.
Check raw_proofLem_syntax_step.
Check raw_proofLem_endpoint_rule_complete.
Check raw_proofLem_ruleCoverage.
Check raw_proofLem_endpoint.

Print Assumptions raw_proofLemRoot_list_view.
Print Assumptions raw_singleProofRoot_supported_eq.
Print Assumptions raw_proofLem_syntax_step.
Print Assumptions raw_proofLem_endpoint_rule_complete.
Print Assumptions raw_proofLem_ruleCoverage.
Print Assumptions raw_proofLem_endpoint.
