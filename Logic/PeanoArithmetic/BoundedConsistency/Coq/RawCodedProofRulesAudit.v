(** Assumption audit for local arithmetic natural-deduction validity. *)

From BoundedPAConsistency Require Import RawCodedProofRules.

Import PABoundedRawCodedProofRules.

Check proofRuleValidCasesTermAt.
Check RawProofRuleValidCases.
Check raw_sat_proofRuleValidCasesTermAt_iff.

Check proofRuleValidTermAt.
Check RawProofRuleValid.
Check raw_sat_proofRuleValidTermAt_iff.
Check raw_proofRuleValid_endpoint.

Print Assumptions raw_sat_proofRuleValidCasesTermAt_iff.
Print Assumptions raw_sat_proofRuleValidTermAt_iff.
Print Assumptions raw_proofRuleValid_endpoint.
