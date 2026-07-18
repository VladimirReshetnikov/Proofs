(**
  Falsity is never Sigma-true at a positive fixed truth level.

  The generic restricted-proof induction deliberately leaves its final
  contradiction as an explicit semantic seam.  This file discharges that
  seam directly.  First we inspect the closed root row of an arbitrary
  rank-zero certificate for [Bot] and prove that its output is zero.  Then
  the positive Sigma root view has no possible branch: its rank-zero branch
  asks for output one, and all six recursive branches have a constructor
  shape incompatible with the one-field code of [Bot].

  No standard-code decoder occurs here.  The assignment and every hidden
  beta table may be nonstandard elements of an arbitrary PA model.
*)

From Stdlib Require Import Arith.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedTermEvaluationStepFunctionality
  RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthElimination
  RawCodedRestrictedProofSoundness.

Module PABoundedRawCodedFixedLevelBottomLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthElimination.
Import PABoundedRawCodedRestrictedProofSoundness.

(** The one-field falsity code cannot be any binary logical constructor. *)
Lemma raw_formulaBot_neq_binary : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawFormulaBotCode M <>
    rawCodeList3 M (rawNumeralValue M tag) left right.
Proof.
  intros M hPA tag left right.
  apply (raw_codeList1_neq_codeList3 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M tag) left right).
Qed.

(** Nor can it be a unary quantifier code. *)
Lemma raw_formulaBot_neq_unary : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag child,
  rawFormulaBotCode M <>
    rawCodeList2 M (rawNumeralValue M tag) child.
Proof.
  intros M hPA tag child.
  apply (raw_codeList1_neq_codeList2 M hPA
    (rawListNode_injective M hPA)
    (rawNumeralValue M 1) (rawNumeralValue M tag) child).
Qed.

(** A globally closed rank-zero certificate exposes a closed local root
    step.  Only the falsity row can have the one-field falsity code, and its
    truth-table clause fixes the output to zero. *)
Lemma raw_rankZeroTruthCertificate_bot_output_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      output assignmentCode assignmentStep,
  RawRankZeroTruthCertificate M
    (rawFormulaBotCode M) output assignmentCode assignmentStep ->
  output = raw_zero M.
Proof.
  intros M hPA output assignmentCode assignmentStep
    (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof
    (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
      (rawFormulaBotCode M) output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep htables) as hclosed.
  destruct hclosed as
    (left & leftOutput & right & rightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hcode _].
    exfalso. apply (raw_formulaBot_neq_binary M hPA 0 left right).
    exact hcode.
  - exact (proj2 hbot).
  - destruct himp as [[hcode _] _].
    exfalso. apply (raw_formulaBot_neq_binary M hPA 2 left right).
    exact hcode.
  - destruct hand as [[hcode _] _].
    exfalso. apply (raw_formulaBot_neq_binary M hPA 3 left right).
    exact hcode.
  - destruct hor as [[hcode _] _].
    exfalso. apply (raw_formulaBot_neq_binary M hPA 4 left right).
    exact hcode.
Qed.

(** This is the concrete contradiction required by the generic proof-code
    induction.  It is intentionally unconditional on an admissibility
    premise: any purported positive certificate already contains enough
    closed syntax to expose its impossible root row. *)
Theorem raw_fixedLevelSigmaBottomFalse_successor : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel,
  RawFixedLevelSigmaBottomFalse M (S inputLevel).
Proof.
  intros M hPA inputLevel assignmentCode assignmentStep hsigma.
  pose proof (raw_fixedLevelSigmaTruthCertificate_successor_view M hPA
    inputLevel (rawFormulaBotCode M) assignmentCode assignmentStep hsigma)
    as hview.
  destruct hview as
    [hrankZero |
     [(left & right & hcode & _) |
      [(left & right & hcode & _) |
       [(left & right & hcode & _) |
        [(left & right & hcode & _) |
         [(child & witness & newAssignmentCode & newAssignmentStep &
             hcode & _) |
          (child & hcode & _)]]]]]].
  - pose proof (raw_rankZeroTruthCertificate_bot_output_zero M hPA
      (rawNumeralValue M 1) assignmentCode assignmentStep hrankZero)
      as honeZero.
    apply (raw_zero_neq_truthOne M hPA). symmetry. exact honeZero.
  - apply (raw_formulaBot_neq_binary M hPA 2 left right).
    exact hcode.
  - apply (raw_formulaBot_neq_binary M hPA 2 left right).
    exact hcode.
  - apply (raw_formulaBot_neq_binary M hPA 3 left right).
    exact hcode.
  - apply (raw_formulaBot_neq_binary M hPA 4 left right).
    exact hcode.
  - apply (raw_formulaBot_neq_unary M hPA 6 child).
    exact hcode.
  - apply (raw_formulaBot_neq_unary M hPA 5 child).
    exact hcode.
Qed.

End PABoundedRawCodedFixedLevelBottomLaws.
