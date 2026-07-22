(** Assumption audit for standard proof-wide rule coverage. *)
From BoundedPAConsistency Require Import
  RawCodedProofRuleCoverageStandard.

Import PABoundedRawCodedProofRuleCoverageStandard.

Check raw_quotedValidProof_endpoint_rule_complete.
Check raw_quotedValidProof_rule_coverage.

Print Assumptions raw_quotedValidProof_endpoint_rule_complete.
Print Assumptions raw_quotedValidProof_rule_coverage.
