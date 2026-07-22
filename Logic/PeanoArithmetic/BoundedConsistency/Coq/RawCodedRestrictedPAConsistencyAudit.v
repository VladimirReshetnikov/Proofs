(** Assumption audit for the transparent fixed-level PA consistency sentence. *)

From BoundedPAConsistency Require Import RawCodedRestrictedPAConsistency.

Import PABoundedRawCodedRestrictedPAConsistency.

(** Assignment independence and the generic semantic interface for sealing. *)
Check raw_term_eval_free_ext.
Check raw_formula_sat_free_ext.
Check raw_formula_sat_sentence_ext.
Check raw_formula_sat_sealPA_iff_valid.

(** The closed sentence and its exact carrier-level meaning. *)
Check restrictedPAConsistencyBodyFormula.
Check restrictedPAConsistencyFormula.
Check restrictedPAConsistencyFormula_sentence.
Check raw_sat_restrictedPAConsistencyBodyFormula_iff.
Check raw_sat_restrictedPAConsistencyFormula_iff.

(** Consequences for standard quoted derivations. *)
Check raw_restrictedPAConsistency_excludes_standard_rawProof.
Check raw_restrictedPAConsistency_excludes_standard_provTree.

(** The nonstandard-model boundary is an explicit theorem premise. *)
Check RawCodedRestrictedPAProofExclusion.
Check PA_BProv_restrictedPAConsistencyFormula_of_raw_exclusion.

Print Assumptions raw_term_eval_free_ext.
Print Assumptions raw_formula_sat_free_ext.
Print Assumptions raw_formula_sat_sentence_ext.
Print Assumptions raw_formula_sat_sealPA_iff_valid.
Print Assumptions restrictedPAConsistencyFormula_sentence.
Print Assumptions raw_sat_restrictedPAConsistencyBodyFormula_iff.
Print Assumptions raw_sat_restrictedPAConsistencyFormula_iff.
Print Assumptions raw_restrictedPAConsistency_excludes_standard_rawProof.
Print Assumptions raw_restrictedPAConsistency_excludes_standard_provTree.
Print Assumptions PA_BProv_restrictedPAConsistencyFormula_of_raw_exclusion.
