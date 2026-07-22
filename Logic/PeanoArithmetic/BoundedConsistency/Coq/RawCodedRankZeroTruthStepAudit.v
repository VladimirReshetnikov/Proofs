(** Public-surface and assumption audit for local rank-zero truth. *)

From BoundedPAConsistency Require Import RawCodedRankZeroTruthStep.

Import PABoundedRawCodedRankZeroTruthStep.

Check RawTruthBit.
Check RawEqualityTruth.
Check RawImpTruth.
Check RawAndTruth.
Check RawOrTruth.

Check RawFormulaEqTruthRow.
Check RawFormulaBotTruthRow.
Check RawFormulaImpTruthRow.
Check RawFormulaAndTruthRow.
Check RawFormulaOrTruthRow.
Check RawRankZeroTruthStep.

Check truthBitTermAt.
Check equalityTruthTermAt.
Check impTruthTermAt.
Check andTruthTermAt.
Check orTruthTermAt.
Check rankZeroTruthStepTermAt.

Check raw_sat_equalityTruthTermAt_iff.
Check raw_sat_impTruthTermAt_iff.
Check raw_sat_formulaEqTruthRowTermAt_iff.
Check raw_sat_formulaImpTruthRowTermAt_iff.
Check raw_sat_rankZeroTruthStepTermAt_iff.
Check raw_rankZeroTruthStep_output_bit.

Print Assumptions raw_sat_equalityTruthTermAt_iff.
Print Assumptions raw_sat_impTruthTermAt_iff.
Print Assumptions raw_sat_formulaEqTruthRowTermAt_iff.
Print Assumptions raw_sat_formulaImpTruthRowTermAt_iff.
Print Assumptions raw_sat_rankZeroTruthStepTermAt_iff.
Print Assumptions raw_rankZeroTruthStep_output_bit.
