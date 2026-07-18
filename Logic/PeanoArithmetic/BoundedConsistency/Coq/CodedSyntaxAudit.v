(** Public surface and kernel-assumption audit for [CodedSyntax]. *)

From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import BoundedConsistency CodedSyntax.

Import PA.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.

Check termCode.
Check formulaCode.
Check decodeTerm.
Check decodeFormula.
Check decodeTerm_termCode.
Check decodeFormula_formulaCode.
Check termCode_injective.
Check formulaCode_injective.
Check validTermCodeb_spec.
Check validFormulaCodeb_spec.
Check codedQuantifierGroups_formulaCode.
Check CodeQuantifierBounded_formulaCode_iff.
Check codedRename_formulaCode.
Check codedInstantiate_formulaCode.
Check codedQuantifierGroups_rename.
Check codedQuantifierGroups_instantiate.

Print Assumptions decodeTerm_termCode.
Print Assumptions decodeFormula_formulaCode.
Print Assumptions termCode_injective.
Print Assumptions formulaCode_injective.
Print Assumptions validTermCodeb_spec.
Print Assumptions validFormulaCodeb_spec.
Print Assumptions codedQuantifierGroups_formulaCode.
Print Assumptions CodeQuantifierBounded_formulaCode_iff.
Print Assumptions codedQuantifierGroups_rename.
Print Assumptions codedQuantifierGroups_instantiate.
