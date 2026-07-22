(** Assumption audit for transparent raw-proof code constructors. *)

From BoundedPAConsistency Require Import RawCodedProofConstructors.

Import PABoundedRawCodedProofConstructors.

Check proofCodeFieldsTerm.
Check raw_eval_proofCodeFieldsTerm.
Check proofCodeFieldsTermAt.
Check raw_sat_proofCodeFieldsTermAt_iff.

Check proofAssCodeTerm.
Check proofImpICodeTerm.
Check proofImpECodeTerm.
Check proofBotECodeTerm.
Check proofLemCodeTerm.
Check proofAndICodeTerm.
Check proofAndE1CodeTerm.
Check proofAndE2CodeTerm.
Check proofOrI1CodeTerm.
Check proofOrI2CodeTerm.
Check proofOrECodeTerm.
Check proofAllICodeTerm.
Check proofAllECodeTerm.
Check proofExICodeTerm.
Check proofExECodeTerm.
Check proofEqReflCodeTerm.
Check proofEqElimCodeTerm.

Check rawProofConstructorCodeTermAt.
Check RawProofConstructorCode.
Check raw_sat_rawProofConstructorCodeTermAt_iff.
Check rawQuotedProofCode.
Check rawQuotedProofCode_standard.

Print Assumptions raw_eval_proofCodeFieldsTerm.
Print Assumptions raw_sat_proofCodeFieldsTermAt_iff.
Print Assumptions raw_sat_rawProofConstructorCodeTermAt_iff.
Print Assumptions rawQuotedProofCode_standard.
