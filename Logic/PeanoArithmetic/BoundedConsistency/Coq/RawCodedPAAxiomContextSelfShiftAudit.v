(** Assumption audit for PA-axiom context self-shift.

    The exported endpoint is intentionally checked together with the two
    nonstandard syntax lemmas on which it depends.  [Print Assumptions]
    makes accidental admission or an extra logical axiom visible in CI. *)

From BoundedPAConsistency Require Import
  RawCodedPAAxiomContextSelfShift.

Import PABoundedRawCodedPAAxiomContextSelfShift.

Check raw_codedTermShift_identity_above_bound.
Check raw_codedFormulaDiagonalShift_identity_above_bound.
Check raw_codedFormulaShift_identity_above_bound.
Check raw_codedUniversalClosure_shift_identity.
Check raw_codedPAAxiomWitness_axiom_selfShift.
Check raw_codedPAAxiomWitnessContextWithTables_selfShift.
Check raw_codedPAAxiomWitnessContext_selfShift.

Print Assumptions raw_codedTermShift_identity_above_bound.
Print Assumptions raw_codedFormulaShift_identity_above_bound.
Print Assumptions raw_codedUniversalClosure_shift_identity.
Print Assumptions raw_codedPAAxiomWitness_axiom_selfShift.
Print Assumptions raw_codedPAAxiomWitnessContext_selfShift.
