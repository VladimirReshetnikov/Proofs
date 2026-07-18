(** Assumption audit for atomic adequacy of standard PA quotations. *)

From BoundedPAConsistency Require Import
  RawCodedProofAtomicAdequacyStandard.

Import PABoundedRawCodedProofAtomicAdequacyStandard.

(** Quoted terms have syntax traversals whenever the supplied coded
    assignment is defined through the successor of the quoted term code. *)
Check raw_termEvaluationClosedStep_forget_to_syntax.
Check raw_termEvaluationTraversal_forget_to_syntax.
Check raw_codedAssignmentDefinedThrough_weaken.
Check raw_quotedTerm_syntax_realizable_of_assignment.

(** Atomic adequacy is available for every externally quoted formula and
    for every externally quoted finite context. *)
Check raw_quotedFormulaCode_eq_code_inv.
Check raw_quotedFormula_atomically_adequate.
Check raw_contextAllAtomicallyAdequate_empty.
Check raw_contextAllAtomicallyAdequate_cons.
Check raw_quotedContext_all_atomically_adequate.

(** Arbitrary internal operation witnesses on standard inputs have their
    intended standard endpoints.  This is the nontrivial bridge needed by
    proof rules whose endpoint formula is obtained by substitution. *)
Check raw_codedTermOperation_quoted_sound_generic.
Check raw_codedTermShift_quoted_sound.
Check raw_codedTermOpening_quoted_sound.
Check raw_codedFormulaSubstitutionAtom_quoted_sound.
Check raw_codedFormulaSingleSubstitution_at_quoted_sound.
Check raw_codedFormulaSingleSubstitution_quoted_sound.

(** Endpoint adequacy and its proof-wide support-table consequence are
    deliberately stated only for externally quoted valid derivations. *)
Check raw_quotedProof_endpoint_atomically_adequate.
Check raw_proofAtomicallyAdequate_quoted.

Print Assumptions raw_quotedTerm_syntax_realizable_of_assignment.
Print Assumptions raw_quotedFormula_atomically_adequate.
Print Assumptions raw_quotedContext_all_atomically_adequate.
Print Assumptions raw_codedTermShift_quoted_sound.
Print Assumptions raw_codedTermOpening_quoted_sound.
Print Assumptions raw_codedFormulaSingleSubstitution_quoted_sound.
Print Assumptions raw_quotedProof_endpoint_atomically_adequate.
Print Assumptions raw_proofAtomicallyAdequate_quoted.
