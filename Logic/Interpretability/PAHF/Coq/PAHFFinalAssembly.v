(* ===================================================================== *)
(*  PAHFFinalAssembly.v                                                 *)
(*                                                                       *)
(*  Single audit surface for the deductive PA/HFFin bi-interpretation.   *)
(*  All semantic and logical plumbing is now concrete; this record names *)
(*  only the remaining internal-PA arithmetic proof objects.             *)
(* ===================================================================== *)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus Completeness.
From PAHF Require Import PAHF
  PAHFOrdinalCodeTotalInduction PAHFMembershipTail
  PAHFInterpretations PAHFProofTranslationSemantic
  PAHFDeductiveAssembly PAHFRoundTripArithmetic
  PAHFRoundTripEquality PAHFRoundTripQuantifiers
  PAHFHFRepresentationFinite PAHFCompositeArithmetic
  PAHFCompositeMemBelow.

Import ListNotations.
Import PA PA.Term PA.Formula.

Record PAHFFinalProofInputs : Prop := {
  final_adjoin_existence : PAHFAdjoinExistence;
  final_ordinal_code_injective : PAOrdinalCodeGraphInjectiveProof;
  final_composite_term_graph : PACompositeTermGraphProof;
  final_ordinal_code_range : PAOrdinalCodeGraphRangeProof;
  final_membership_extensionality : PAHFMembershipExtensionalityProof;
  final_translated_adjoin :
    BProv Ax_s []
      (translateHFFormula (Fol.seal HF_adjoin_form));
  final_translated_finite_induction : forall phi,
    BProv Ax_s []
      (translateHFFormula (Fol.seal (HF_finite_induction_form phi)))
}.

Definition finalPACompositeEqualityProof
    (P : PAHFFinalProofInputs) : PACompositeEqualityProof :=
  pa_composite_eq_exact_of_adjoin_injective_termGraph
    (final_adjoin_existence P)
    (final_ordinal_code_injective P)
    (final_composite_term_graph P).

Definition finalPAOrdinalCodeQuantifierProofs
    (P : PAHFFinalProofInputs) : PAOrdinalCodeQuantifierProofs :=
  PAOrdinalCodeQuantifierProofs_of_adjoinExistence
    (final_adjoin_existence P)
    (final_ordinal_code_range P).

Definition finalPACompositeConstructorProofs
    (P : PAHFFinalProofInputs) : PACompositeConstructorProofs :=
  PACompositeConstructorProofs_of_eq_and_quantifiers
    (finalPACompositeEqualityProof P)
    (finalPAOrdinalCodeQuantifierProofs P).

Definition finalPARoundTripProof
    (P : PAHFFinalProofInputs) : PARoundTripProof :=
  PARoundTripProof_of_constructorProofs
    (finalPACompositeConstructorProofs P).

Definition finalTranslatedHFFinAxiomProofs
    (P : PAHFFinalProofInputs) : TranslatedHFFinAxiomProofs :=
  translatedHFFinAxiomProofs_of_remaining
    (BProv_Ax_s_translated_HF_extensionality_of_member_ext
      (final_membership_extensionality P))
    (final_translated_adjoin P)
    BProv_Ax_s_translated_HF_induction
    (final_translated_finite_induction P).

Definition finalHFFinCompositeExtensionality
    (P : PAHFFinalProofInputs) : HFFinModelCompositeMemExtensionality :=
  HFFinModelCompositeMemExtensionality_of_translation
    HFFinPAProofTranslation_raw_semantic
    (final_membership_extensionality P).

Definition finalHFFinCompositeAdjoinCode
    (P : PAHFFinalProofInputs) : HFFinModelCompositeAdjoinCode :=
  HFFinModelCompositeAdjoinCode_of_translation
    HFFinPAProofTranslation_raw_semantic
    (PAHFCompositeAdjoinExistenceProof_of_total
      (final_adjoin_existence P)).

Definition finalHFRoundTripProof
    (P : PAHFFinalProofInputs) : HFRoundTripProof :=
  HFRoundTripProof_of_translation_composite_arithmetic
    HFFinPAProofTranslation_raw_semantic
    (finalHFFinCompositeExtensionality P)
    (finalHFFinCompositeAdjoinCode P).

Definition paHFFinDeductiveBiInterpretation_of_final_inputs
    (P : PAHFFinalProofInputs) :
  PAHFFinDeductiveBiInterpretationCertificate :=
  paHFFinDeductiveBiInterpretation_of_proofs
    HFFinPAProofTranslation_raw_semantic
    (finalTranslatedHFFinAxiomProofs P)
    (finalPARoundTripProof P)
    (finalHFRoundTripProof P).
