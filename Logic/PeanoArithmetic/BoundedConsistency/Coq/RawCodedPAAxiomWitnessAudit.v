(** Assumption audit for transparent PA-axiom witnesses. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import RawCodedPAAxiomWitness.

Import PA.
Import PABoundedRawCodedPAAxiomWitness.

(** Transparent syntax-bound graphs used to seal arbitrary, including
    nonstandard, induction bodies. *)
Check codedTermBoundTermAt.
Check RawCodedTermBound.
Check raw_sat_codedTermBoundTermAt_iff.
Check raw_codedTermBound_standard.

Check codedFormulaBoundTermAt.
Check RawCodedFormulaBound.
Check raw_sat_codedFormulaBoundTermAt_iff.
Check raw_codedFormulaBound_standard.

(** Closure and the capture-avoiding successor-instance identity. *)
Check formula_closeN_succ_outside.
Check raw_codedUniversalClosure_standard.
Check standardFormulaShift_one_one_then_substitute_succ.

(** The induction branch and the complete seven-way witness graph. *)
Check codedPAAxiomInductionTermAt.
Check RawCodedPAAxiomInduction.
Check raw_sat_codedPAAxiomInductionTermAt_iff.
Check standardPAAxiomInductionBody_eq.
Check raw_codedPAAxiomInduction_standard.

Check codedPAAxiomFiniteWitnessTermAt.
Check RawCodedPAAxiomFiniteWitness.
Check raw_sat_codedPAAxiomFiniteWitnessTermAt_iff.
Check codedPAAxiomWitnessTermAt.
Check RawCodedPAAxiomWitness.
Check raw_sat_codedPAAxiomWitnessTermAt_iff.
Check raw_codedPAAxiomWitness_standard.
Check raw_sat_codedPAAxiomWitnessTermAt_standard.

Print Assumptions raw_sat_codedTermBoundTermAt_iff.
Print Assumptions raw_codedTermBound_standard.
Print Assumptions raw_sat_codedFormulaBoundTermAt_iff.
Print Assumptions raw_codedFormulaBound_standard.
Print Assumptions raw_codedUniversalClosure_standard.
Print Assumptions standardFormulaShift_one_one_then_substitute_succ.
Print Assumptions raw_sat_codedPAAxiomInductionTermAt_iff.
Print Assumptions standardPAAxiomInductionBody_eq.
Print Assumptions raw_codedPAAxiomInduction_standard.
Print Assumptions raw_sat_codedPAAxiomWitnessTermAt_iff.
Print Assumptions raw_codedPAAxiomWitness_standard.
Print Assumptions raw_sat_codedPAAxiomWitnessTermAt_standard.
