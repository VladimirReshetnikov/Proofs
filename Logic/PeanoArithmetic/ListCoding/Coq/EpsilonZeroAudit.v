(**
  Focused kernel audit for the epsilon-zero ordinal coding development.

  This file deliberately imports only the executable coding layer, its
  semantic laws, the general computable-function-to-formula bridge, and the
  five public ordinal formulae.  Keeping the audit independent of the larger
  list-coding audit makes accidental dependencies (in particular MathComp)
  visible in the focused build.
*)

From PAListCoding Require Import
  EpsilonZero EpsilonZeroLaws ComputableFormula EpsilonZeroFormulas.

(** * Pairing and ordinal-code bijections *)

Check PAEpsilonZero.squareUnpair_pair.
Check PAEpsilonZero.squarePair_unpair.
Check PAEpsilonZero.squarePair_injective.
Check PAEpsilonZero.decode_encode.
Check PAEpsilonZero.encode_decode.
Check PAEpsilonZero.encode_injective.
Check PAEpsilonZero.decode_injective.
Check PAEpsilonZero.valid_encode_iff.

(** * Normal-form closure and graph functionality *)

Check PAEpsilonZero.onoteAdd_nf.
Check PAEpsilonZeroLaws.onoteSub_nf.
Check PAEpsilonZeroLaws.onoteSplit_nf.
Check PAEpsilonZeroLaws.onoteSplit'_nf.
Check PAEpsilonZeroLaws.onoteMulNat_nf.
Check PAEpsilonZeroLaws.onoteScale_nf.
Check PAEpsilonZeroLaws.onoteMul_nf.
Check PAEpsilonZeroLaws.onotePowAux_nf.
Check PAEpsilonZeroLaws.onotePowAux2_nf.
Check PAEpsilonZeroLaws.onotePow_nf.

Check PAEpsilonZeroLaws.addCode_valid.
Check PAEpsilonZeroLaws.mulCode_valid.
Check PAEpsilonZeroLaws.powCode_valid.
Check PAEpsilonZeroLaws.ordinalAdd_result_valid.
Check PAEpsilonZeroLaws.ordinalMul_result_valid.
Check PAEpsilonZeroLaws.ordinalPow_result_valid.

Check PAEpsilonZero.ordinalAdd_functional.
Check PAEpsilonZero.ordinalMul_functional.
Check PAEpsilonZero.ordinalPow_functional.
Check PAEpsilonZero.ordinalAdd_exists_unique.
Check PAEpsilonZero.ordinalMul_exists_unique.
Check PAEpsilonZero.ordinalPow_exists_unique.

(** * Strict order on raw notations and valid codes *)

Check PAEpsilonZeroLaws.onoteCompare_lt_irrefl.
Check PAEpsilonZeroLaws.onoteCompare_lt_trans.
Check PAEpsilonZeroLaws.onoteCompare_trichotomy.
Check PAEpsilonZeroLaws.ordinalLT_irrefl.
Check PAEpsilonZeroLaws.ordinalLT_trans.
Check PAEpsilonZeroLaws.ordinalLT_trichotomy.

(** * Core algebra and distinguished identities *)

Check PAEpsilonZeroLaws.zeroCode_eq.
Check PAEpsilonZeroLaws.decode_zeroCode.
Check PAEpsilonZeroLaws.decode_oneCode.
Check PAEpsilonZeroLaws.zeroCode_valid.
Check PAEpsilonZeroLaws.oneCode_valid.

Check PAEpsilonZeroLaws.zeroCode_add.
Check PAEpsilonZeroLaws.add_zeroCode.
Check PAEpsilonZeroLaws.addCode_assoc.
Check PAEpsilonZeroLaws.zeroCode_mul.
Check PAEpsilonZeroLaws.mul_zeroCode.
Check PAEpsilonZeroLaws.oneCode_mul.
Check PAEpsilonZeroLaws.mul_oneCode.
Check PAEpsilonZeroLaws.mulCode_assoc.
Check PAEpsilonZeroLaws.mulCode_addCode.

Check PAEpsilonZeroLaws.onoteAdd_assoc.
Check PAEpsilonZeroLaws.onoteMul_add.
Check PAEpsilonZeroLaws.onoteMul_assoc.
Check PAEpsilonZeroLaws.onoteSplit_reconstruct.
Check PAEpsilonZeroLaws.onotePow_zero.
Check PAEpsilonZeroLaws.onotePow_one_nf.
Check PAEpsilonZeroLaws.pow_zeroCode.
Check PAEpsilonZeroLaws.pow_oneCode.
Check PAEpsilonZeroLaws.zeroCode_pow_zeroCode.

Check PAEpsilonZeroLaws.ordinalAdd_zero_l.
Check PAEpsilonZeroLaws.ordinalAdd_zero_r.
Check PAEpsilonZeroLaws.ordinalMul_zero_l.
Check PAEpsilonZeroLaws.ordinalMul_zero_r.
Check PAEpsilonZeroLaws.ordinalMul_one_l.
Check PAEpsilonZeroLaws.ordinalMul_one_r.
Check PAEpsilonZeroLaws.ordinalPow_zero_exponent.
Check PAEpsilonZeroLaws.ordinalPow_one_exponent.

(** * Formula-selection boundary *)

Check computable_unary_graph_has_PA_formula.
Check computable_binary_graph_has_PA_formula.
Check chosenGraphFormula_correct.
Check unaryGraphFormula_correct.
Check binaryGraphFormula_correct.
Check unaryGraphFormula_output_first.
Check binaryGraphFormula_output_first.

(** * The five public formula values *)

Check PAEpsilonZeroFormulas.ValidOrdinalCodeFormula.
Check PAEpsilonZeroFormulas.OrdinalLTFormula.
Check PAEpsilonZeroFormulas.OrdinalAddFormula.
Check PAEpsilonZeroFormulas.OrdinalMulFormula.
Check PAEpsilonZeroFormulas.OrdinalPowFormula.

(** * Arbitrary-environment specifications *)

Check PAEpsilonZeroFormulas.ValidOrdinalCodeFormula_spec.
Check PAEpsilonZeroFormulas.OrdinalLTFormula_spec.
Check PAEpsilonZeroFormulas.OrdinalAddFormula_spec.
Check PAEpsilonZeroFormulas.OrdinalMulFormula_spec.
Check PAEpsilonZeroFormulas.OrdinalPowFormula_spec.

(** * Explicit standard-environment corollaries *)

Check PAEpsilonZeroFormulas.ValidOrdinalCodeFormula_standard.
Check PAEpsilonZeroFormulas.OrdinalLTFormula_standard.
Check PAEpsilonZeroFormulas.OrdinalAddFormula_standard.
Check PAEpsilonZeroFormulas.OrdinalMulFormula_standard.
Check PAEpsilonZeroFormulas.OrdinalPowFormula_standard.

Check PAEpsilonZeroFormulas.OrdinalAddFormula_result_valid.
Check PAEpsilonZeroFormulas.OrdinalMulFormula_result_valid.
Check PAEpsilonZeroFormulas.OrdinalPowFormula_result_valid.

(** * Assumption audit

    The first group covers the two independent coding bijections.  The next
    groups expose the non-obvious recursive normalizers and algebra laws.
    The final group records the intentional classical-choice boundary used
    to select concrete PA formula values and audits every public formula
    specification built on that choice. *)

Print Assumptions PAEpsilonZero.squareUnpair_pair.
Print Assumptions PAEpsilonZero.squarePair_unpair.
Print Assumptions PAEpsilonZero.decode_encode.
Print Assumptions PAEpsilonZero.encode_decode.

Print Assumptions PAEpsilonZeroLaws.onoteSub_nf.
Print Assumptions PAEpsilonZeroLaws.onoteMul_nf.
Print Assumptions PAEpsilonZeroLaws.onotePow_nf.
Print Assumptions PAEpsilonZeroLaws.addCode_valid.
Print Assumptions PAEpsilonZeroLaws.mulCode_valid.
Print Assumptions PAEpsilonZeroLaws.powCode_valid.

Print Assumptions PAEpsilonZeroLaws.ordinalLT_trichotomy.
Print Assumptions PAEpsilonZeroLaws.addCode_assoc.
Print Assumptions PAEpsilonZeroLaws.mulCode_addCode.
Print Assumptions PAEpsilonZeroLaws.mulCode_assoc.
Print Assumptions PAEpsilonZeroLaws.onoteSplit_reconstruct.
Print Assumptions PAEpsilonZeroLaws.onotePow_zero.
Print Assumptions PAEpsilonZeroLaws.onotePow_one_nf.

Print Assumptions computable_unary_graph_has_PA_formula.
Print Assumptions computable_binary_graph_has_PA_formula.
Print Assumptions chosenGraphFormula_correct.
Print Assumptions unaryGraphFormula_correct.
Print Assumptions binaryGraphFormula_correct.

Print Assumptions PAEpsilonZeroFormulas.ValidOrdinalCodeFormula_spec.
Print Assumptions PAEpsilonZeroFormulas.OrdinalLTFormula_spec.
Print Assumptions PAEpsilonZeroFormulas.OrdinalAddFormula_spec.
Print Assumptions PAEpsilonZeroFormulas.OrdinalMulFormula_spec.
Print Assumptions PAEpsilonZeroFormulas.OrdinalPowFormula_spec.

Print Assumptions PAEpsilonZeroFormulas.ValidOrdinalCodeFormula_standard.
Print Assumptions PAEpsilonZeroFormulas.OrdinalLTFormula_standard.
Print Assumptions PAEpsilonZeroFormulas.OrdinalAddFormula_standard.
Print Assumptions PAEpsilonZeroFormulas.OrdinalMulFormula_standard.
Print Assumptions PAEpsilonZeroFormulas.OrdinalPowFormula_standard.

Print Assumptions PAEpsilonZeroFormulas.OrdinalAddFormula_result_valid.
Print Assumptions PAEpsilonZeroFormulas.OrdinalMulFormula_result_valid.
Print Assumptions PAEpsilonZeroFormulas.OrdinalPowFormula_result_valid.
