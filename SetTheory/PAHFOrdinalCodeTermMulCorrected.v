(* ===================================================================== *)
(*  PAHFOrdinalCodeTermMulCorrected.v                                   *)
(*                                                                       *)
(*  Sound structural lifting of multiplication compatibility.           *)
(*                                                                       *)
(*  The generic structural proof now consumes exactly its two sound      *)
(*  arithmetic halves.  This module therefore only adapts the corrected  *)
(*  core record and assembles the downstream round-trip interfaces.      *)
(* ===================================================================== *)

From SetTheory Require Import
  PAHF PAHFDeductiveAssembly PAHFCompositeArithmetic
  PAHFOrdinalCodeTotalInduction PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFRoundTripQuantifiers
  PAHFOrdinalCodeTermCompatibility PAHFOrdinalCodeTermOperations
  PAHFOrdinalCodeTermMul PAHFOrdinalCodeMulCore
  PAHFRoundTripArithmeticAssembly.

Import PA PA.Formula.

(** The corrected record already has exactly the two fields required by the
    common structural multiplication proof; no parallel induction or binder
    plumbing is needed here. *)
Theorem PAOrdinalCodeTermMulCompatibility_of_total_corrected_cores :
  PAOrdinalCodeGraphTotalProof ->
  PAOrdinalCodeMulCoreProofsCorrected ->
  PAOrdinalCodeTermMulCompatibility.
Proof.
  intros htotal hcores.
  exact (PAOrdinalCodeTermMulCompatibility_of_total_core_halves
    htotal
    (pa_mul_open_core_forward hcores)
    (pa_mul_bound_core_exact hcores)).
Qed.

(* --------------------------------------------------------------------- *)
(* Corrected arithmetic round-trip assembly.                             *)

Definition PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs_corrected
    (hadjoin : PAHFAdjoinExistence)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PAOrdinalCodeTermMulCompatibility :=
  PAOrdinalCodeTermMulCompatibility_of_total_corrected_cores
    (PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs hadjoin)
    hmul.

Definition PACompositeTermGraphProof_of_arithmetic_inputs_corrected
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeTermGraphProof :=
  PACompositeTermGraphProof_of_base_add_mul
    (PAOrdinalCodeTermBaseCompatibilityProofs_of_arithmetic_inputs
      hext hadjoin)
    (PAOrdinalCodeTermAddCompatibility_of_arithmetic_inputs
      hadjoin hadd)
    (PAOrdinalCodeTermMulCompatibility_of_arithmetic_inputs_corrected
      hadjoin hmul).

Definition PACompositeEqualityProof_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeEqualityProof :=
  pa_composite_eq_exact_of_adjoin_injective_termGraph
    hadjoin
    (PAOrdinalCodeGraphInjectiveProof_of_arithmetic_inputs P)
    (PACompositeTermGraphProof_of_arithmetic_inputs_corrected
      hext hadjoin hadd hmul).

Definition PACompositeConstructorProofs_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PACompositeConstructorProofs :=
  PACompositeConstructorProofs_of_eq_and_quantifiers
    (PACompositeEqualityProof_of_arithmetic_inputs_corrected
      P hext hadjoin hadd hmul)
    (PAOrdinalCodeQuantifierProofs_of_arithmetic_inputs
      P hext hadjoin).

Definition PARoundTripProof_of_arithmetic_inputs_corrected
    (P : TranslatedHFFinAxiomProofs)
    (hext : PAHFMembershipExtensionalityProof)
    (hadjoin : PAHFAdjoinExistence)
    (hadd : PAOrdinalCodeAddCoreCompatibility)
    (hmul : PAOrdinalCodeMulCoreProofsCorrected) :
  PARoundTripProof :=
  PARoundTripProof_of_constructorProofs
    (PACompositeConstructorProofs_of_arithmetic_inputs_corrected
      P hext hadjoin hadd hmul).
