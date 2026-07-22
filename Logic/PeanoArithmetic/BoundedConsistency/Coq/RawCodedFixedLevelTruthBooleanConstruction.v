(**
  Boolean constructor laws for positive fixed-level truth certificates.

  Every premise below is already a globally closed certificate.  Unary
  short-circuit cases append one parent row to one child traversal.  Cases
  which inspect both children first concatenate their independent traversals,
  then append the parent.  Thus these lemmas are valid for arbitrary
  nonstandard formula and assignment codes; no external syntax recursion is
  used here.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthConstruction.

Module PABoundedRawCodedFixedLevelTruthBooleanConstruction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthConstruction.

Definition RawFixedLevelSuccessorTruthDecision (M : RawPAModel)
    (lower : nat) (root assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelSigmaTruthCertificate M (S lower)
      root assignmentCode assignmentStep \/
  RawFixedLevelPiFalsityCertificate M (S lower)
      root assignmentCode assignmentStep.

Arguments RawFixedLevelSuccessorTruthDecision
  M lower root assignmentCode assignmentStep : clear implicits.

(** Implication is Sigma-true as soon as its antecedent is Pi-false. *)
Lemma raw_fixedLevelImp_sigma_of_left_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaImpCode M left right) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaImpCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with M hPA
    lower (rawFixedLevelPiMode M) left assignmentCode assignmentStep
    (rawFormulaImpCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    left. split; [reflexivity |].
    exists rootIndex, left, (raw_zero M), right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. left. split; [reflexivity |]. split.
    + split; [exact hrootBelow |]. exact hrootLookup.
    + reflexivity.
Qed.

(** Dually, a Sigma-true consequent makes the implication Sigma-true. *)
Lemma raw_fixedLevelImp_sigma_of_right_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaImpCode M left right) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaImpCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hright.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with M hPA
    lower (rawFixedLevelSigmaMode M) right assignmentCode assignmentStep
    (rawFormulaImpCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    left. split; [reflexivity |].
    exists (raw_zero M), left, rootIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. left. split; [reflexivity |]. split.
    + split; [exact hrootBelow |]. exact hrootLookup.
    + reflexivity.
Qed.

(** The only false implication case consults both child certificates. *)
Lemma raw_fixedLevelImp_pi_of_left_sigma_right_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaImpCode M left right) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaImpCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft hright.
  apply (raw_fixedLevelSuccessorCertificateTraversals_append_pi_with M hPA
    lower
    (rawFixedLevelSigmaMode M) left assignmentCode assignmentStep
    (rawFixedLevelPiMode M) right assignmentCode assignmentStep
    (rawFormulaImpCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rightIndex
      _ hrightEarlier (leftIndex & hleftEarlier).
    right. split; [reflexivity |].
    exists leftIndex, left, rightIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. left. split; [reflexivity |]. split.
    + exact hleftEarlier.
    + split; [exact hrightEarlier | reflexivity].
Qed.

Theorem raw_fixedLevelImp_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaImpCode M left right) ->
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaImpCode M left right) ->
  RawFixedLevelSuccessorTruthDecision M lower
    left assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    right assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaImpCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hsigmaDomain hpiDomain [hleftSigma | hleftPi]
    [hrightSigma | hrightPi].
  - left. exact (raw_fixedLevelImp_sigma_of_right_sigma M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hrightSigma).
  - right. exact (raw_fixedLevelImp_pi_of_left_sigma_right_pi M hPA lower
      left right assignmentCode assignmentStep hpiDomain
      hleftSigma hrightPi).
  - left. exact (raw_fixedLevelImp_sigma_of_left_pi M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hleftPi).
  - left. exact (raw_fixedLevelImp_sigma_of_left_pi M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hleftPi).
Qed.

(** ------------------------------------------------------------------
    Conjunction. *)

Lemma raw_fixedLevelAnd_sigma_of_both : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaAndCode M left right) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaAndCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft hright.
  apply (raw_fixedLevelSuccessorCertificateTraversals_append_sigma_with M hPA
    lower
    (rawFixedLevelSigmaMode M) left assignmentCode assignmentStep
    (rawFixedLevelSigmaMode M) right assignmentCode assignmentStep
    (rawFormulaAndCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rightIndex
      _ hrightEarlier (leftIndex & hleftEarlier).
    left. split; [reflexivity |].
    exists leftIndex, left, rightIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. left. split; [reflexivity |].
    split; assumption.
Qed.

Lemma raw_fixedLevelAnd_pi_of_left_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaAndCode M left right) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaAndCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_pi_with M hPA
    lower (rawFixedLevelPiMode M) left assignmentCode assignmentStep
    (rawFormulaAndCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    right. split; [reflexivity |].
    exists rootIndex, left, (raw_zero M), right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. left. split; [reflexivity |]. left.
    split; [exact hrootBelow | exact hrootLookup].
Qed.

Lemma raw_fixedLevelAnd_pi_of_right_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaAndCode M left right) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaAndCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hright.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_pi_with M hPA
    lower (rawFixedLevelPiMode M) right assignmentCode assignmentStep
    (rawFormulaAndCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    right. split; [reflexivity |].
    exists (raw_zero M), left, rootIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. left. split; [reflexivity |]. right.
    split; [exact hrootBelow | exact hrootLookup].
Qed.

Theorem raw_fixedLevelAnd_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaAndCode M left right) ->
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaAndCode M left right) ->
  RawFixedLevelSuccessorTruthDecision M lower
    left assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    right assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaAndCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hsigmaDomain hpiDomain [hleftSigma | hleftPi]
    [hrightSigma | hrightPi].
  - left. exact (raw_fixedLevelAnd_sigma_of_both M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain
      hleftSigma hrightSigma).
  - right. exact (raw_fixedLevelAnd_pi_of_right_pi M hPA lower
      left right assignmentCode assignmentStep hpiDomain hrightPi).
  - right. exact (raw_fixedLevelAnd_pi_of_left_pi M hPA lower
      left right assignmentCode assignmentStep hpiDomain hleftPi).
  - right. exact (raw_fixedLevelAnd_pi_of_left_pi M hPA lower
      left right assignmentCode assignmentStep hpiDomain hleftPi).
Qed.

(** ------------------------------------------------------------------
    Disjunction. *)

Lemma raw_fixedLevelOr_sigma_of_left_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaOrCode M left right) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaOrCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with M hPA
    lower (rawFixedLevelSigmaMode M) left assignmentCode assignmentStep
    (rawFormulaOrCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    left. split; [reflexivity |].
    exists rootIndex, left, (raw_zero M), right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. left. split; [reflexivity |]. left.
    split; [exact hrootBelow | exact hrootLookup].
Qed.

Lemma raw_fixedLevelOr_sigma_of_right_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaOrCode M left right) ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawFormulaOrCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hright.
  apply (raw_fixedLevelSuccessorCertificateTraversal_append_sigma_with M hPA
    lower (rawFixedLevelSigmaMode M) right assignmentCode assignmentStep
    (rawFormulaOrCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_sigma_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex htraversal.
    destruct htraversal as
      [_ [_ [_ [_ [hrootBelow [hrootLookup _]]]]]].
    left. split; [reflexivity |].
    exists (raw_zero M), left, rootIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. right. left. split; [reflexivity |]. right.
    split; [exact hrootBelow | exact hrootLookup].
Qed.

Lemma raw_fixedLevelOr_pi_of_both : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaOrCode M left right) ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    left assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    right assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawFormulaOrCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hdomain hleft hright.
  apply (raw_fixedLevelSuccessorCertificateTraversals_append_pi_with M hPA
    lower
    (rawFixedLevelPiMode M) left assignmentCode assignmentStep
    (rawFixedLevelPiMode M) right assignmentCode assignmentStep
    (rawFormulaOrCode M left right) assignmentCode assignmentStep).
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower left assignmentCode assignmentStep)). exact hleft.
  - apply (proj2 (raw_fixedLevelSuccessorCertificateTraversal_pi_iff
      M lower right assignmentCode assignmentStep)). exact hright.
  - intros modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rightIndex
      _ hrightEarlier (leftIndex & hleftEarlier).
    right. split; [reflexivity |].
    exists leftIndex, left, rightIndex, right, (raw_zero M),
      assignmentCode, assignmentStep, (raw_zero M).
    split; [exact hdomain |].
    right. right. right. left. split; [reflexivity |].
    split; assumption.
Qed.

Theorem raw_fixedLevelOr_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S lower)
    (rawFormulaOrCode M left right) ->
  RawFixedLevelPiDomain M (S lower)
    (rawFormulaOrCode M left right) ->
  RawFixedLevelSuccessorTruthDecision M lower
    left assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    right assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaOrCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep
    hsigmaDomain hpiDomain [hleftSigma | hleftPi]
    [hrightSigma | hrightPi].
  - left. exact (raw_fixedLevelOr_sigma_of_left_sigma M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hleftSigma).
  - left. exact (raw_fixedLevelOr_sigma_of_left_sigma M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hleftSigma).
  - left. exact (raw_fixedLevelOr_sigma_of_right_sigma M hPA lower
      left right assignmentCode assignmentStep hsigmaDomain hrightSigma).
  - right. exact (raw_fixedLevelOr_pi_of_both M hPA lower
      left right assignmentCode assignmentStep hpiDomain hleftPi hrightPi).
Qed.

End PABoundedRawCodedFixedLevelTruthBooleanConstruction.
