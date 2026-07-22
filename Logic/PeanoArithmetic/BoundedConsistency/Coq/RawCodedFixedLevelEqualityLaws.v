(** Fixed-level equality laws needed by natural-deduction soundness. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedTermEvaluationTraversal
  RawCodedFormulaRankTraversal
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthSchedule RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthOperationTarski.

Module PABoundedRawCodedFixedLevelEqualityLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthOperationTarski.

(** Equality reflexivity is true at every positive fixed level.  Totality
    reduces the claim to excluding the Pi branch.  A Pi equality can only be
    a rank-zero output-zero certificate; opening that row evaluates the same
    term twice, and evaluator functionality contradicts its false equality
    bit. *)
Theorem raw_fixedLevelEq_refl_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel
      witness assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaEqCode M witness witness)
    assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaEqCode M witness witness)
    assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel witness assignmentCode assignmentStep
    hadmissible.
  destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
    inputLevel M hPA (rawFormulaEqCode M witness witness)
    assignmentCode assignmentStep hadmissible) as [hsigma | hpi].
  - exact hsigma.
  - pose proof
      (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
        inputLevel (rawShapeEq witness witness)
        assignmentCode assignmentStep hpi) as hview.
    cbn [RawFixedLevelPiSuccessorShapeView] in hview.
    destruct hview as [hrankZero | himpossible]; [| contradiction].
    destruct (raw_rankZeroTruthCertificate_eq_view M hPA
      (rawFormulaEqCode M witness witness) (raw_zero M)
      assignmentCode assignmentStep witness witness eq_refl hrankZero)
      as (leftValue & rightValue & hleft & hright & htruth).
    assert (hvalues : leftValue = rightValue).
    {
      exact (raw_termEvaluationCertificate_value_functional M hPA
        witness assignmentCode assignmentStep
        leftValue rightValue hleft hright).
    }
    unfold RawEqualityTruth in htruth.
    destruct htruth as [[_ hzeroOne] | [hunequal _]].
    + exact (False_rect _
        (raw_zero_neq_truthOne M hPA hzeroOne)).
    + contradiction.
Qed.

End PABoundedRawCodedFixedLevelEqualityLaws.
