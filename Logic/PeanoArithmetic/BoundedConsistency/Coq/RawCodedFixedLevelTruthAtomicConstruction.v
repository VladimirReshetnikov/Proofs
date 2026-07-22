(**
  Rank-zero leaves at every positive fixed-truth level.

  Equality and falsity rows have exact Sigma/Pi rank zero.  Honest atomic
  adequacy therefore supplies the total rank-zero evaluator, whose output bit
  can be installed directly as the atomic alternative of a one-row successor
  certificate at any external level.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal
  RawCodedFormulaRankTotality RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthRealization
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelDomainLaws
  RawCodedFixedLevelTruthBaseLaws
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthConstruction
  RawCodedFixedLevelTruthBooleanConstruction.

Module PABoundedRawCodedFixedLevelTruthAtomicConstruction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthRealization.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthBaseLaws.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthConstruction.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.

Lemma raw_fixedLevelRankZero_sigma_domain : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedFormulaRank M root (raw_zero M) (raw_zero M) ->
  RawFixedLevelSigmaDomain M 0 root.
Proof.
  intros M hPA root hrank.
  exists (raw_zero M), (raw_zero M). split; [exact hrank |].
  change (rawLe M (raw_zero M) (raw_zero M)).
  exact (raw_rank_le_refl M hPA (raw_zero M)).
Qed.

Lemma raw_fixedLevelRankZero_pi_domain : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedFormulaRank M root (raw_zero M) (raw_zero M) ->
  RawFixedLevelPiDomain M 0 root.
Proof.
  intros M hPA root hrank.
  exists (raw_zero M), (raw_zero M). split; [exact hrank |].
  change (rawLe M (raw_zero M) (raw_zero M)).
  exact (raw_rank_le_refl M hPA (raw_zero M)).
Qed.

Theorem raw_fixedLevelRankZero_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M lower
    root assignmentCode assignmentStep ->
  RawCodedFormulaRank M root (raw_zero M) (raw_zero M) ->
  RawFixedLevelSuccessorTruthDecision M lower
    root assignmentCode assignmentStep.
Proof.
  intros M hPA lower root assignmentCode assignmentStep
    hadmissible hrank.
  pose proof hadmissible as
    [hatomic [hassignment _]].
  pose proof (raw_fixedLevelRankZero_sigma_domain M hPA root hrank)
    as hsigmaZero.
  pose proof (raw_fixedLevelRankZero_pi_domain M hPA root hrank)
    as hpiZero.
  assert (hsyntax : RawRankZeroSyntaxRealizable M
      root assignmentCode assignmentStep).
  {
    apply (raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable M hPA).
    split; [exact hatomic |]. split; [exact hassignment |].
    left. exact hsigmaZero.
  }
  destruct (raw_fixedLevelTruthCertificate_zero_decides M hPA
    root assignmentCode assignmentStep)
    as [hsigma | hpi].
  - split; [exact hsigmaZero |]. split; [exact hpiZero | exact hsyntax].
  - left.
    apply (raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero M hPA
      lower root assignmentCode assignmentStep).
    + exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
        lower root assignmentCode assignmentStep hadmissible)).
    + exact (raw_fixedLevelSigmaTruthCertificate_zero_rankZero M hPA
        root assignmentCode assignmentStep hsigma).
  - right.
    apply (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero M hPA
      lower root assignmentCode assignmentStep).
    + exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
        lower root assignmentCode assignmentStep hadmissible)).
    + exact (raw_fixedLevelPiFalsityCertificate_zero_rankZero M hPA
        root assignmentCode assignmentStep hpi).
Qed.

(** Constructor-specialized wrappers recover the exact zero rank from the
    public rank certificate, rather than assuming the input-domain witness
    happened to use canonical rank values. *)
Lemma raw_fixedLevelEq_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower left right
    assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M lower
    (rawFormulaEqCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaEqCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA lower left right assignmentCode assignmentStep hadmissible.
  destruct (raw_codedWellFormedFormula_rank_exists M hPA
    (rawFormulaEqCode M left right)
    (raw_fixedLevelTruthAdmissible_wellFormed M lower
      (rawFormulaEqCode M left right) assignmentCode assignmentStep
      hadmissible)) as [sigma [pi hrank]].
  destruct (raw_codedFormulaRank_shape_at M hPA
    (rawShapeEq left right) sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & _ & hshape).
  cbn [RawCodedFormulaShapeRankRow RawFormulaRankZero] in hshape.
  destruct hshape as [-> ->].
  exact (raw_fixedLevelRankZero_decides M hPA lower
    (rawFormulaEqCode M left right) assignmentCode assignmentStep
    hadmissible hrank).
Qed.

Lemma raw_fixedLevelBot_decides : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower
    assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M lower
    (rawFormulaBotCode M) assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthDecision M lower
    (rawFormulaBotCode M) assignmentCode assignmentStep.
Proof.
  intros M hPA lower assignmentCode assignmentStep hadmissible.
  destruct (raw_codedWellFormedFormula_rank_exists M hPA
    (rawFormulaBotCode M)
    (raw_fixedLevelTruthAdmissible_wellFormed M lower
      (rawFormulaBotCode M) assignmentCode assignmentStep
      hadmissible)) as [sigma [pi hrank]].
  destruct (raw_codedFormulaRank_shape_at M hPA
    rawShapeBot sigma pi hrank) as
    (formulaCode & formulaStep & sigmaCode & sigmaStep &
     piCode & piStep & bound & rootIndex & _ & hshape).
  cbn [RawCodedFormulaShapeRankRow RawFormulaRankZero] in hshape.
  destruct hshape as [-> ->].
  exact (raw_fixedLevelRankZero_decides M hPA lower
    (rawFormulaBotCode M) assignmentCode assignmentStep
    hadmissible hrank).
Qed.

End PABoundedRawCodedFixedLevelTruthAtomicConstruction.
