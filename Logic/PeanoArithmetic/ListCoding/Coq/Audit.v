(**
  Kernel audit for the PA finite-list coding development.

  The list below is intentionally explicit: it records the canonical coding
  boundary, every public PA formula, and every standard-model correctness
  theorem.  [Print Assumptions] makes any future addition to the trusted base
  visible in build output.
*)

From PAListCoding Require Import ListCode ListFormulas.

Check PAListCode.listCode.
Check PAListCode.decode.
Check PAListCode.decode_listCode.
Check PAListCode.listCode_decode.
Check PAListCode.listCode_injective.
Check PAListCode.decode_functional.
Check PAListCode.ValidCode_unique_list.

Check PAListFormulas.validCodeFormula.
Check PAListFormulas.hasLengthFormula.
Check PAListFormulas.nthElementFormula.
Check PAListFormulas.singletonFormula.
Check PAListFormulas.concatenationFormula.
Check PAListFormulas.flattenFormula.
Check PAListFormulas.occurrencesFormula.
Check PAListFormulas.permutationFormula.
Check PAListFormulas.contiguousSubstringFormula.
Check PAListFormulas.subsequenceFormula.
Check PAListFormulas.noDuplicatesFormula.
Check PAListFormulas.sortedFormula.
Check PAListFormulas.lexSortedFormula.
Check PAListFormulas.allPermutationsFormula.

Check PAListFormulas.validCodeFormula_correct.
Check PAListFormulas.hasLengthFormula_correct.
Check PAListFormulas.nthElementFormula_correct.
Check PAListFormulas.singletonFormula_correct.
Check PAListFormulas.concatenationFormula_correct.
Check PAListFormulas.flattenFormula_correct.
Check PAListFormulas.occurrencesFormula_correct.
Check PAListFormulas.permutationFormula_correct.
Check PAListFormulas.contiguousSubstringFormula_correct.
Check PAListFormulas.subsequenceFormula_correct.
Check PAListFormulas.noDuplicatesFormula_correct.
Check PAListFormulas.sortedFormula_correct.
Check PAListFormulas.lexSortedFormula_correct.
Check PAListFormulas.allPermutationsFormula_correct.

Print Assumptions PAListCode.decode_listCode.
Print Assumptions PAListCode.listCode_decode.
Print Assumptions PAListCode.listCode_injective.
Print Assumptions PAListCode.decode_functional.
Print Assumptions PAListCode.ValidCode_unique_list.

Print Assumptions PAListFormulas.validCodeFormula_correct.
Print Assumptions PAListFormulas.hasLengthFormula_correct.
Print Assumptions PAListFormulas.nthElementFormula_correct.
Print Assumptions PAListFormulas.singletonFormula_correct.
Print Assumptions PAListFormulas.concatenationFormula_correct.
Print Assumptions PAListFormulas.flattenFormula_correct.
Print Assumptions PAListFormulas.occurrencesFormula_correct.
Print Assumptions PAListFormulas.permutationFormula_correct.
Print Assumptions PAListFormulas.contiguousSubstringFormula_correct.
Print Assumptions PAListFormulas.subsequenceFormula_correct.
Print Assumptions PAListFormulas.noDuplicatesFormula_correct.
Print Assumptions PAListFormulas.sortedFormula_correct.
Print Assumptions PAListFormulas.lexSortedFormula_correct.
Print Assumptions PAListFormulas.allPermutationsFormula_correct.

(* Audit the non-obvious semantic bridges separately from their wrappers. *)
Print Assumptions PAListFormulas.ListTrace_complete.
Print Assumptions PAListFormulas.FlattenPosition_iff.
Print Assumptions PAListFormulas.SubsequenceByChunks_iff.
Print Assumptions PAListFormulas.LexSortedPosition_iff.
Print Assumptions PAListFormulas.AllPermutationsPosition_iff.
