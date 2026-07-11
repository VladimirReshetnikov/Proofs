(* ===================================================================== *)
(*  PAHFConcreteAssembly.v                                              *)
(*                                                                       *)
(*  Concrete deductive PA/HFFin assembly, with the sole remaining       *)
(*  arithmetic argument isolated to term-parametric multiplication.      *)
(* ===================================================================== *)

From Stdlib Require Import List.
From SetTheory Require Import
  Fol Calculus PAHF PAHFDeductiveAssembly
  PAHFProofTranslationSemantic PAHFHFRoundTripSemantic
  PAHFCompositeArithmetic PAHFCompositeMemBelow
  PAHFOrdinalCodeTotalInduction PAHFMembershipTail
  PAHFRoundTripArithmetic PAHFOrdinalCodeTermCompatibility
  PAHFOrdinalCodeRange PAHFOrdinalCodeTermOperations
  PAHFAdjoinTotal PAHFTranslatedAdjoin
  PAHFTranslatedExtensionality PAHFTranslatedFiniteInduction
  PAHFOrdinalCodeFunctional PAHFOrdinalCodeRangeArithmetic
  PAHFOrdinalCodeTermBase PAHFOrdinalCodeAddCore
  PAHFRoundTripArithmeticAssembly
  PAHFOrdinalCodeMulCore PAHFOrdinalCodeTermMulCorrected.

Import ListNotations.
Import PA PA.Term PA.Formula.

(** The five translated finite-HF axioms are now all concrete PA theorems. *)
Definition concreteTranslatedHFFinAxiomProofs :
    TranslatedHFFinAxiomProofs :=
  translatedHFFinAxiomProofs_of_remaining
    BProv_Ax_s_translated_HF_extensionality
    BProv_Ax_s_translated_HF_adjoin
    BProv_Ax_s_translated_HF_induction
    BProv_Ax_s_translated_HF_finite_induction.

Definition concretePAHFMembershipExtensionalityProof :
    PAHFMembershipExtensionalityProof.
Proof.
  unfold PAHFMembershipExtensionalityProof, PAHFCompositeSameMembers.
  exact BProv_Ax_s_membership_extensionality.
Defined.

Definition concretePAHFAdjoinExistence : PAHFAdjoinExistence :=
  PAHFAdjoinExistence_proof.

Definition concretePAOrdinalCodeGraphTotalProof :
    PAOrdinalCodeGraphTotalProof :=
  PAOrdinalCodeGraphTotalProof_of_arithmetic_inputs
    concretePAHFAdjoinExistence.

Definition concretePAOrdinalCodeGraphFunctionalProof :
    PAOrdinalCodeGraphFunctionalProof :=
  PAOrdinalCodeGraphFunctionalProof_of_arithmetic_inputs
    concretePAHFMembershipExtensionalityProof.

Definition concretePAOrdinalCodeGraphSuccClosureProof :
    PAOrdinalCodeGraphSuccClosureProof :=
  PAOrdinalCodeGraphSuccClosureProof_of_arithmetic_inputs
    concretePAHFMembershipExtensionalityProof
    concretePAHFAdjoinExistence.

Definition concretePAOrdinalCodeSuccAdjoinCompatibility :
    PAOrdinalCodeSuccAdjoinCompatibility.
Proof.
  intros G raw pred out hgraph.
  exact
    (BProv_Ax_s_hfAdjoinGraphTermAt_iff_ordinalCodeGraphTermAt_succ_base
      concretePAOrdinalCodeGraphSuccClosureProof
      concretePAOrdinalCodeGraphFunctionalProof
      concretePAHFAdjoinExistence
      G raw pred out hgraph).
Defined.

Definition concretePAOrdinalCodeGraphCodomainProof :
    PAOrdinalCodeGraphCodomainProof :=
  PAOrdinalCodeGraphCodomainProof_of_TranslatedHFFinAxiomProofs
    concreteTranslatedHFFinAxiomProofs.

Definition concretePAOrdinalCodeAddCoreCompatibility :
    PAOrdinalCodeAddCoreCompatibility :=
  PAOrdinalCodeAddCoreCompatibility_of_interfaces
    concreteTranslatedHFFinAxiomProofs
    concretePAOrdinalCodeGraphCodomainProof
    concretePAOrdinalCodeGraphFunctionalProof
    concretePAOrdinalCodeSuccAdjoinCompatibility
    concretePAOrdinalCodeGraphTotalProof.

(** The HF-side round trip no longer has any residual arithmetic input. *)
Definition concreteHFRoundTripProof : HFRoundTripProof :=
  HFRoundTripProof_of_translation_composite_arithmetic
    HFFinPAProofTranslation_raw_semantic
    (HFFinModelCompositeMemExtensionality_of_translation
      HFFinPAProofTranslation_raw_semantic
      concretePAHFMembershipExtensionalityProof)
    (HFFinModelCompositeAdjoinCode_of_translation
      HFFinPAProofTranslation_raw_semantic
      (PAHFCompositeAdjoinExistenceProof_of_total
        concretePAHFAdjoinExistence)).

(** Sound final assembly from the exact multiplication compatibility theorem.
    The corrected multiplication bridge never assumes the invalid reverse
    direction for a core with an unbound local output slot. *)
Definition concretePARoundTripProof_of_mulTerm
    (hmulTerm : PAOrdinalCodeMulTermCompatibility) :
    PARoundTripProof :=
  PARoundTripProof_of_arithmetic_inputs_corrected
    concreteTranslatedHFFinAxiomProofs
    concretePAHFMembershipExtensionalityProof
    concretePAHFAdjoinExistence
    concretePAOrdinalCodeAddCoreCompatibility
    (PAOrdinalCodeMulCoreProofsCorrected_of_term hmulTerm).

Definition paHFFinDeductiveBiInterpretation_of_mulTerm
    (hmulTerm : PAOrdinalCodeMulTermCompatibility) :
    PAHFFinDeductiveBiInterpretationCertificate :=
  paHFFinDeductiveBiInterpretation_of_proofs
    HFFinPAProofTranslation_raw_semantic
    concreteTranslatedHFFinAxiomProofs
    (concretePARoundTripProof_of_mulTerm hmulTerm)
    concreteHFRoundTripProof.
