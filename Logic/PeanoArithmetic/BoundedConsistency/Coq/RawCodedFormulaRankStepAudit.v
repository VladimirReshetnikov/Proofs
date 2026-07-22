(** Assumption audit for constructor-local coded formula rank rows. *)

From BoundedPAConsistency Require Import RawCodedFormulaRankStep.

Import PABoundedRawCodedFormulaRankStep.

Check raw_sat_maxTermAt_iff.
Check raw_sat_formulaRankImpTermAt_iff.
Check raw_sat_formulaRankAllTermAt_iff.
Check raw_sat_formulaRankExTermAt_iff.
Check raw_sat_formulaImpRankStepTermAt_iff.
Check raw_sat_formulaAllRankStepTermAt_iff.
Check RawMax_numerals.

Print Assumptions raw_sat_maxTermAt_iff.
Print Assumptions raw_sat_formulaRankImpTermAt_iff.
Print Assumptions raw_sat_formulaRankAllTermAt_iff.
Print Assumptions raw_sat_formulaRankExTermAt_iff.
Print Assumptions raw_sat_formulaImpRankStepTermAt_iff.
Print Assumptions raw_sat_formulaAllRankStepTermAt_iff.
Print Assumptions RawMax_numerals.
