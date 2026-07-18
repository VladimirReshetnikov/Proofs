(**
  Base-level laws for globally closed fixed-level truth certificates.

  At external level zero both orientations are wrappers around the one
  functional rank-zero truth graph: Sigma stores output one and Pi stores
  output zero.  The global wrappers hide their beta tables, so the first
  lemmas carefully recover the root row before applying rank-zero
  functionality.  No formula decoder and no standardness assumption is used;
  the root, assignment, and all hidden tables may be nonstandard elements of
  an arbitrary PA model.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRankZeroTruthStepFunctionality RawCodedRankZeroTruthTraversal
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal.

Module PABoundedRawCodedFixedLevelTruthBaseLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.

(** Expose the rank-zero output hidden by a global Sigma certificate. *)
Lemma raw_fixedLevelSigmaTruthCertificate_zero_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M 0
    root assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M root (rawNumeralValue M 1)
    assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal).
  pose proof (raw_fixedLevelZeroTruthTraversal_root_row M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex (rawFixedLevelSigmaMode M)
    root assignmentCode assignmentStep htraversal) as hrow.
  destruct hrow as [[_ [_ htruth]] | [hmodes _]].
  - exact htruth.
  - exfalso. apply (raw_zero_neq_truthOne M hPA). exact hmodes.
Qed.

(** Expose the rank-zero output hidden by a global Pi certificate. *)
Lemma raw_fixedLevelPiFalsityCertificate_zero_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M 0
    root assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M root (raw_zero M)
    assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep hcertificate.
  cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
  destruct hcertificate as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex &
     htraversal).
  pose proof (raw_fixedLevelZeroTruthTraversal_root_row M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex (rawFixedLevelPiMode M)
    root assignmentCode assignmentStep htraversal) as hrow.
  destruct hrow as [[hmodes _] | [_ [_ hfalse]]].
  - exfalso. apply (raw_zero_neq_truthOne M hPA). symmetry. exact hmodes.
  - exact hfalse.
Qed.

(** The global level-zero wrappers are exactly their local domain/output
    pairs.  The reverse directions use the checked singleton-traversal
    construction, not an assumed global assembly principle. *)
Theorem raw_fixedLevelSigmaTruthCertificate_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root assignmentCode assignmentStep,
  (RawFixedLevelSigmaTruthCertificate M 0
      root assignmentCode assignmentStep <->
   RawFixedLevelSigmaDomain M 0 root /\
   RawRankZeroTruthCertificate M root (rawNumeralValue M 1)
      assignmentCode assignmentStep).
Proof.
  intros M hPA root assignmentCode assignmentStep. split.
  - intro hcertificate. split.
    + exact (raw_fixedLevelSigmaTruthCertificate_domain M hPA 0
        root assignmentCode assignmentStep hcertificate).
    + exact (raw_fixedLevelSigmaTruthCertificate_zero_rankZero M hPA
        root assignmentCode assignmentStep hcertificate).
  - intro hlocal.
    exact (raw_fixedLevelSigmaTruthCertificate_zero_of_local M hPA
      root assignmentCode assignmentStep hlocal).
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root assignmentCode assignmentStep,
  (RawFixedLevelPiFalsityCertificate M 0
      root assignmentCode assignmentStep <->
   RawFixedLevelPiDomain M 0 root /\
   RawRankZeroTruthCertificate M root (raw_zero M)
      assignmentCode assignmentStep).
Proof.
  intros M hPA root assignmentCode assignmentStep. split.
  - intro hcertificate. split.
    + exact (raw_fixedLevelPiFalsityCertificate_domain M hPA 0
        root assignmentCode assignmentStep hcertificate).
    + exact (raw_fixedLevelPiFalsityCertificate_zero_rankZero M hPA
        root assignmentCode assignmentStep hcertificate).
  - intro hlocal.
    exact (raw_fixedLevelPiFalsityCertificate_zero_of_local M hPA
      root assignmentCode assignmentStep hlocal).
Qed.

(** Sigma truth and Pi falsity are incompatible at level zero.  Functionality
    identifies their hidden rank-zero outputs; PA's zero/successor separation
    then supplies the contradiction. *)
Theorem raw_fixedLevelTruthCertificate_zero_exclusive : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      root assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M 0
    root assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M 0
    root assignmentCode assignmentStep -> False.
Proof.
  intros M hPA root assignmentCode assignmentStep hsigma hpi.
  pose proof (raw_rankZeroTruthCertificate_output_functional M hPA
    root assignmentCode assignmentStep
    (rawNumeralValue M 1) (raw_zero M)
    (raw_fixedLevelSigmaTruthCertificate_zero_rankZero M hPA
      root assignmentCode assignmentStep hsigma)
    (raw_fixedLevelPiFalsityCertificate_zero_rankZero M hPA
      root assignmentCode assignmentStep hpi)) as honeZero.
  apply (raw_zero_neq_truthOne M hPA). symmetry. exact honeZero.
Qed.

End PABoundedRawCodedFixedLevelTruthBaseLaws.
