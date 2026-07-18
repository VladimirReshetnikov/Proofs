(**
  Admissibility-guarded laws for positive fixed-level truth.

  A successor certificate has an intentionally permissive rank-zero branch:
  even a composite quantifier-free formula may be discharged by the closed
  rank-zero evaluator.  Consequently constructor inversion cannot simply
  throw that branch away.  The shape views below retain it explicitly; the
  Boolean laws later inspect its certified child truth bits, while quantified
  shapes rule it out using closed-step syntax separation.

  All semantic laws in this file carry [RawFixedLevelTruthAdmissible].  That
  guard is essential: a rank traversal alone regards the payloads of equality
  codes as opaque numbers and does not provide term syntax or enough of the
  assignment to evaluate them.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedFormulaRankTraversal
  RawCodedRankZeroTruthStep
  RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthTraversal
  RawCodedRankZeroTruthElimination
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelDomainLaws
  RawCodedFixedLevelTruthConstruction
  RawCodedFixedLevelTruthBooleanConstruction
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthElimination
  RawCodedFixedLevelTruthSchedule.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthLaws.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthElimination.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthConstruction.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthElimination.
Import PABoundedRawCodedFixedLevelTruthSchedule.

(** A constructor-indexed version of the public Sigma root view.  Unlike the
    raw traversal view, its recursive alternative already mentions the exact
    children displayed by [shape]. *)
Definition RawFixedLevelSigmaSuccessorShapeView (M : RawPAModel)
    (lower : nat) (shape : RawCodedFormulaShape M)
    (assignmentCode assignmentStep : M) : Prop :=
  RawRankZeroTruthCertificate M (rawCodedFormulaShapeCode M shape)
      (rawNumeralValue M 1) assignmentCode assignmentStep \/
  match shape with
  | rawShapeEq _ _ => False
  | rawShapeBot => False
  | rawShapeImp leftChild rightChild =>
      RawFixedLevelPiFalsityCertificate M (S lower)
        leftChild assignmentCode assignmentStep \/
      RawFixedLevelSigmaTruthCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeAnd leftChild rightChild =>
      RawFixedLevelSigmaTruthCertificate M (S lower)
        leftChild assignmentCode assignmentStep /\
      RawFixedLevelSigmaTruthCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeOr leftChild rightChild =>
      RawFixedLevelSigmaTruthCertificate M (S lower)
        leftChild assignmentCode assignmentStep \/
      RawFixedLevelSigmaTruthCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeAll child =>
      RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower child
            binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep
        (rawFormulaAllCode M child)
  | rawShapeEx child =>
      exists witness newAssignmentCode newAssignmentStep : M,
        RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
          (rawFormulaExCode M child)
          newAssignmentCode newAssignmentStep /\
        RawFixedLevelSigmaTruthCertificate M (S lower)
          child newAssignmentCode newAssignmentStep
  end.

Definition RawFixedLevelPiSuccessorShapeView (M : RawPAModel)
    (lower : nat) (shape : RawCodedFormulaShape M)
    (assignmentCode assignmentStep : M) : Prop :=
  RawRankZeroTruthCertificate M (rawCodedFormulaShapeCode M shape)
      (raw_zero M) assignmentCode assignmentStep \/
  match shape with
  | rawShapeEq _ _ => False
  | rawShapeBot => False
  | rawShapeImp leftChild rightChild =>
      RawFixedLevelSigmaTruthCertificate M (S lower)
        leftChild assignmentCode assignmentStep /\
      RawFixedLevelPiFalsityCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeAnd leftChild rightChild =>
      RawFixedLevelPiFalsityCertificate M (S lower)
        leftChild assignmentCode assignmentStep \/
      RawFixedLevelPiFalsityCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeOr leftChild rightChild =>
      RawFixedLevelPiFalsityCertificate M (S lower)
        leftChild assignmentCode assignmentStep /\
      RawFixedLevelPiFalsityCertificate M (S lower)
        rightChild assignmentCode assignmentStep
  | rawShapeAll child =>
      exists witness newAssignmentCode newAssignmentStep : M,
        RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
          (rawFormulaAllCode M child)
          newAssignmentCode newAssignmentStep /\
        RawFixedLevelPiFalsityCertificate M (S lower)
          child newAssignmentCode newAssignmentStep
  | rawShapeEx child =>
      RawFixedLevelNoBinderCounterexample M
        (fun _ binderAssignmentCode binderAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower child
            binderAssignmentCode binderAssignmentStep)
        assignmentCode assignmentStep
        (rawFormulaExCode M child)
  end.

Arguments RawFixedLevelSigmaSuccessorShapeView
  M lower shape assignmentCode assignmentStep : clear implicits.
Arguments RawFixedLevelPiSuccessorShapeView
  M lower shape assignmentCode assignmentStep : clear implicits.

(** Constructor injectivity identifies the existentially exposed children in
    the generic root view with the children already stored in [shape]. *)
Theorem raw_fixedLevelSigmaTruthCertificate_successor_shape_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower shape
      assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M (S lower)
    (rawCodedFormulaShapeCode M shape) assignmentCode assignmentStep ->
  RawFixedLevelSigmaSuccessorShapeView M lower shape
    assignmentCode assignmentStep.
Proof.
  intros M hPA lower shape assignmentCode assignmentStep hcertificate.
  pose proof (raw_fixedLevelSigmaTruthCertificate_successor_view M hPA
    lower (rawCodedFormulaShapeCode M shape)
    assignmentCode assignmentStep hcertificate) as hview.
  destruct hview as
    [hrankZero |
     [(left & right & hcode & hleft) |
      [(left & right & hcode & hright) |
       [(left & right & hcode & hboth) |
        [(left & right & hcode & hchosen) |
         [(child & witness & newAssignmentCode & newAssignmentStep &
             hcode & hprepend & hchild) |
          (child & hcode & hnone)]]]]]].
  - left. exact hrankZero.
  - assert (hshape : shape = rawShapeImp left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. cbn. now left.
  - assert (hshape : shape = rawShapeImp left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. cbn. now right.
  - assert (hshape : shape = rawShapeAnd left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hboth.
  - assert (hshape : shape = rawShapeOr left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hchosen.
  - assert (hshape : shape = rawShapeEx child).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exists witness, newAssignmentCode, newAssignmentStep.
    now split.
  - assert (hshape : shape = rawShapeAll child).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hnone.
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_successor_shape_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower shape
      assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M (S lower)
    (rawCodedFormulaShapeCode M shape) assignmentCode assignmentStep ->
  RawFixedLevelPiSuccessorShapeView M lower shape
    assignmentCode assignmentStep.
Proof.
  intros M hPA lower shape assignmentCode assignmentStep hcertificate.
  pose proof (raw_fixedLevelPiFalsityCertificate_successor_view M hPA
    lower (rawCodedFormulaShapeCode M shape)
    assignmentCode assignmentStep hcertificate) as hview.
  destruct hview as
    [hrankZero |
     [(left & right & hcode & hboth) |
      [(left & right & hcode & hchosen) |
       [(left & right & hcode & hboth) |
        [(child & witness & newAssignmentCode & newAssignmentStep &
            hcode & hprepend & hchild) |
         (child & hcode & hnone)]]]]].
  - left. exact hrankZero.
  - assert (hshape : shape = rawShapeImp left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hboth.
  - assert (hshape : shape = rawShapeAnd left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hchosen.
  - assert (hshape : shape = rawShapeOr left right).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hboth.
  - assert (hshape : shape = rawShapeAll child).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exists witness, newAssignmentCode, newAssignmentStep.
    now split.
  - assert (hshape : shape = rawShapeEx child).
    {
      apply (rawCodedFormulaShapeCode_injective
        polynomialPairInjectivityProof M hPA).
      cbn [rawCodedFormulaShapeCode]. exact hcode.
    }
    subst shape. right. exact hnone.
Qed.

(** Reverse truth-table projections used only for the retained rank-zero
    branch.  They are phrased with the public numeral [1] so they can feed
    the successor certificate constructors directly. *)
Lemma raw_impTruth_one_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawImpTruth M (rawNumeralValue M 1) left right ->
  left = raw_zero M \/ right = rawNumeralValue M 1.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[[hleft hright] hzero] | [hresult hone]].
  - exfalso. apply (raw_zero_neq_truthOne M hPA).
    exact (eq_sym hzero).
  - exact hresult.
Qed.

Lemma raw_impTruth_zero_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawImpTruth M (raw_zero M) left right ->
  left = rawNumeralValue M 1 /\ right = raw_zero M.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[hresult hzero] | [hresult hone]].
  - exact hresult.
  - exfalso. apply (raw_zero_neq_truthOne M hPA).
    exact hone.
Qed.

Lemma raw_andTruth_one_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawAndTruth M (rawNumeralValue M 1) left right ->
  left = rawNumeralValue M 1 /\ right = rawNumeralValue M 1.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[hresult hone] | [hresult hzero]].
  - exact hresult.
  - exfalso. apply (raw_zero_neq_truthOne M hPA).
    exact (eq_sym hzero).
Qed.

Lemma raw_andTruth_zero_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawAndTruth M (raw_zero M) left right ->
  left = raw_zero M \/ right = raw_zero M.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[hresult hone] | [hresult hzero]].
  - exfalso. apply (raw_zero_neq_truthOne M hPA). exact hone.
  - exact hresult.
Qed.

Lemma raw_orTruth_one_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawOrTruth M (rawNumeralValue M 1) left right ->
  left = rawNumeralValue M 1 \/ right = rawNumeralValue M 1.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[hresult hone] | [hresult hzero]].
  - exact hresult.
  - exfalso. apply (raw_zero_neq_truthOne M hPA).
    exact (eq_sym hzero).
Qed.

Lemma raw_orTruth_zero_elim : forall (M : RawPAModel),
    RawPASatisfies M -> forall left right,
  RawOrTruth M (raw_zero M) left right ->
  left = raw_zero M /\ right = raw_zero M.
Proof.
  intros M hPA left right [_ [_ [_ hcases]]].
  destruct hcases as [[hresult hone] | [hresult hzero]].
  - exfalso. apply (raw_zero_neq_truthOne M hPA). exact hone.
  - exact hresult.
Qed.

(** Quantifiers are not part of the rank-zero closed-step grammar. *)
Lemma raw_rankZeroTruthCertificate_all_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall child output
      assignmentCode assignmentStep,
  RawRankZeroTruthCertificate M (rawFormulaAllCode M child) output
    assignmentCode assignmentStep -> False.
Proof.
  intros M hPA child output assignmentCode assignmentStep
    (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
    (rawFormulaAllCode M child) output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep htables) as hclosed.
  exact (raw_rankZeroTruthClosedStep_all_false M hPA
    (rawFormulaAllCode M child) output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep child eq_refl hclosed).
Qed.

Lemma raw_rankZeroTruthCertificate_ex_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall child output
      assignmentCode assignmentStep,
  RawRankZeroTruthCertificate M (rawFormulaExCode M child) output
    assignmentCode assignmentStep -> False.
Proof.
  intros M hPA child output assignmentCode assignmentStep
    (supportCode & supportStep & truthCode & truthStep & htables).
  pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step M hPA
    (rawFormulaExCode M child) output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep htables) as hclosed.
  exact (raw_rankZeroTruthClosedStep_ex_false M hPA
    (rawFormulaExCode M child) output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep child eq_refl hclosed).
Qed.

(** ------------------------------------------------------------------
    Admissibility inherited by Boolean children. *)

Lemma raw_fixedLevelTruthAdmissible_imp_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthAdmissible M level
      left assignmentCode assignmentStep /\
  RawFixedLevelTruthAdmissible M level
      right assignmentCode assignmentStep.
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  pose proof hadmissible as hfull.
  destruct (raw_fixedLevelTruthAdmissible_imp_children_core M hPA
    level left right assignmentCode assignmentStep hadmissible) as
    [[hleftAtomic hleftAssignment] [hrightAtomic hrightAssignment]].
  destruct hfull as [_ [_ [hsigma | hpi]]].
  - destruct (raw_fixedLevelSigmaDomain_imp M hPA level left right hsigma)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_intror hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_introl hrightDomain))).
  - destruct (raw_fixedLevelPiDomain_imp M hPA level left right hpi)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_introl hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_intror hrightDomain))).
Qed.

Lemma raw_fixedLevelTruthAdmissible_and_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthAdmissible M level
      left assignmentCode assignmentStep /\
  RawFixedLevelTruthAdmissible M level
      right assignmentCode assignmentStep.
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  pose proof hadmissible as hfull.
  destruct (raw_fixedLevelTruthAdmissible_and_children_core M hPA
    level left right assignmentCode assignmentStep hadmissible) as
    [[hleftAtomic hleftAssignment] [hrightAtomic hrightAssignment]].
  destruct hfull as [_ [_ [hsigma | hpi]]].
  - destruct (raw_fixedLevelSigmaDomain_and M hPA level left right hsigma)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_introl hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_introl hrightDomain))).
  - destruct (raw_fixedLevelPiDomain_and M hPA level left right hpi)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_intror hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_intror hrightDomain))).
Qed.

Lemma raw_fixedLevelTruthAdmissible_or_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall level left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthAdmissible M level
      left assignmentCode assignmentStep /\
  RawFixedLevelTruthAdmissible M level
      right assignmentCode assignmentStep.
Proof.
  intros M hPA level left right assignmentCode assignmentStep hadmissible.
  pose proof hadmissible as hfull.
  destruct (raw_fixedLevelTruthAdmissible_or_children_core M hPA
    level left right assignmentCode assignmentStep hadmissible) as
    [[hleftAtomic hleftAssignment] [hrightAtomic hrightAssignment]].
  destruct hfull as [_ [_ [hsigma | hpi]]].
  - destruct (raw_fixedLevelSigmaDomain_or M hPA level left right hsigma)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_introl hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_introl hrightDomain))).
  - destruct (raw_fixedLevelPiDomain_or M hPA level left right hpi)
      as [hleftDomain hrightDomain].
    split.
    + exact (conj hleftAtomic
        (conj hleftAssignment (or_intror hleftDomain))).
    + exact (conj hrightAtomic
        (conj hrightAssignment (or_intror hrightDomain))).
Qed.

(** A rank-zero child bit may be replayed at the scheduled successor level.
    The successor domains come from the full child admissibility guard. *)
Lemma raw_rankZeroTruthCertificate_one_as_successor_sigma : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel code
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    code assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
    assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    code assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel code assignmentCode assignmentStep
    hadmissible hrankZero.
  apply (raw_fixedLevelSigmaTruthCertificate_successor_of_rankZero M hPA
    inputLevel code assignmentCode assignmentStep).
  - exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
      inputLevel code assignmentCode assignmentStep hadmissible)).
  - exact hrankZero.
Qed.

Lemma raw_rankZeroTruthCertificate_zero_as_successor_pi : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel code
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    code assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M code (raw_zero M)
    assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S inputLevel)
    code assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel code assignmentCode assignmentStep
    hadmissible hrankZero.
  apply (raw_fixedLevelPiFalsityCertificate_successor_of_rankZero M hPA
    inputLevel code assignmentCode assignmentStep).
  - exact (proj2 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
      inputLevel code assignmentCode assignmentStep hadmissible)).
  - exact hrankZero.
Qed.

Lemma raw_rankZeroTruthCertificate_one_zero_exclusive : forall
    (M : RawPAModel), RawPASatisfies M -> forall code
      assignmentCode assignmentStep,
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
      assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M code (raw_zero M)
      assignmentCode assignmentStep -> False.
Proof.
  intros M hPA code assignmentCode assignmentStep hone hzero.
  apply (raw_zero_neq_truthOne M hPA).
  symmetry.
  exact (raw_rankZeroTruthCertificate_output_functional M hPA
    code assignmentCode assignmentStep
    (rawNumeralValue M 1) (raw_zero M) hone hzero).
Qed.

(** ------------------------------------------------------------------
    PA-definable prefix exclusivity. *)

Definition fixedLevelTruthCertificateExclusiveBelowTermAt
    (inputLevel : nat) (current : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 current))
      (pImp
        (fixedLevelTruthAdmissibleTermAt inputLevel
          (tVar 2) (tVar 1) (tVar 0))
        (pImp
          (fixedLevelSigmaTruthCertificateTermAt (S inputLevel)
            (tVar 2) (tVar 1) (tVar 0))
          (pImp
            (fixedLevelPiFalsityCertificateTermAt (S inputLevel)
              (tVar 2) (tVar 1) (tVar 0))
            pBot)))))).

Definition RawFixedLevelTruthCertificateExclusiveBelow (M : RawPAModel)
    (inputLevel : nat) (current : M) : Prop :=
  forall root assignmentCode assignmentStep : M,
    rawLt M root current ->
    RawFixedLevelTruthAdmissible M inputLevel
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M (S inputLevel)
      root assignmentCode assignmentStep -> False.

Arguments RawFixedLevelTruthCertificateExclusiveBelow
  M inputLevel current : clear implicits.

Lemma raw_sat_fixedLevelTruthCertificateExclusiveBelowTermAt_iff : forall
    (M : RawPAModel) e inputLevel current,
  raw_formula_sat M e
    (fixedLevelTruthCertificateExclusiveBelowTermAt inputLevel current) <->
  RawFixedLevelTruthCertificateExclusiveBelow M inputLevel
    (raw_term_eval M e current).
Proof.
  intros M e inputLevel current.
  unfold fixedLevelTruthCertificateExclusiveBelowTermAt,
    RawFixedLevelTruthCertificateExclusiveBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_fixedLevelTruthCertificateExclusiveBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel,
  RawFixedLevelTruthCertificateExclusiveBelow M inputLevel (raw_zero M).
Proof.
  intros M hPA inputLevel root assignmentCode assignmentStep hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

Definition RawFixedLevelTruthCertificateExclusiveAt (M : RawPAModel)
    (inputLevel : nat) (code assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      code assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S inputLevel)
      code assignmentCode assignmentStep -> False.

Arguments RawFixedLevelTruthCertificateExclusiveAt
  M inputLevel code assignmentCode assignmentStep : clear implicits.

(** Implication is the one Boolean constructor where the child polarity is
    reversed.  In the rank-zero/structural mixed cases the Boolean table
    identifies exactly the child on which the supplied exclusivity premise
    must be used. *)
Lemma raw_fixedLevelImp_exclusive_from_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    left assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    right assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    (rawFormulaImpCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible hleftExclusive hrightExclusive hsigma hpi.
  destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeImp left right) assignmentCode assignmentStep
      hsigma) as hsigmaView.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeImp left right) assignmentCode assignmentStep
      hpi) as hpiView.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
  cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
  destruct hsigmaView as [hsigmaZero | [hleftPi | hrightSigma]].
  - destruct hpiView as [hpiZero | [hleftSigma hrightPi]].
    + exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
        (rawFormulaImpCode M left right) assignmentCode assignmentStep
        hsigmaZero hpiZero).
    + destruct (raw_rankZeroTruthCertificate_imp_view M hPA
        (rawFormulaImpCode M left right) (rawNumeralValue M 1)
        assignmentCode assignmentStep left right eq_refl hsigmaZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_impTruth_one_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput | hrightOutput].
      * subst leftOutput.
        exact (hleftExclusive hleftSigma
          (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
            inputLevel left assignmentCode assignmentStep
            hleftAdmissible hleftZero)).
      * subst rightOutput.
        exact (hrightExclusive
          (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
            inputLevel right assignmentCode assignmentStep
            hrightAdmissible hrightZero)
          hrightPi).
  - destruct hpiView as [hpiZero | [hleftSigma hrightPi]].
    + destruct (raw_rankZeroTruthCertificate_imp_view M hPA
        (rawFormulaImpCode M left right) (raw_zero M)
        assignmentCode assignmentStep left right eq_refl hpiZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_impTruth_zero_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hleftExclusive
        (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
          inputLevel left assignmentCode assignmentStep
          hleftAdmissible hleftZero) hleftPi).
    + exact (hleftExclusive hleftSigma hleftPi).
  - destruct hpiView as [hpiZero | [hleftSigma hrightPi]].
    + destruct (raw_rankZeroTruthCertificate_imp_view M hPA
        (rawFormulaImpCode M left right) (raw_zero M)
        assignmentCode assignmentStep left right eq_refl hpiZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_impTruth_zero_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hrightExclusive hrightSigma
        (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
          inputLevel right assignmentCode assignmentStep
          hrightAdmissible hrightZero)).
    + exact (hrightExclusive hrightSigma hrightPi).
Qed.

Lemma raw_fixedLevelAnd_exclusive_from_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    left assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    right assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    (rawFormulaAndCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible hleftExclusive hrightExclusive hsigma hpi.
  destruct (raw_fixedLevelTruthAdmissible_and_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAnd left right) assignmentCode assignmentStep
      hsigma) as hsigmaView.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAnd left right) assignmentCode assignmentStep
      hpi) as hpiView.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
  cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
  destruct hsigmaView as [hsigmaZero | [hleftSigma hrightSigma]].
  - destruct hpiView as [hpiZero | [hleftPi | hrightPi]].
    + exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
        (rawFormulaAndCode M left right) assignmentCode assignmentStep
        hsigmaZero hpiZero).
    + destruct (raw_rankZeroTruthCertificate_and_view M hPA
        (rawFormulaAndCode M left right) (rawNumeralValue M 1)
        assignmentCode assignmentStep left right eq_refl hsigmaZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_andTruth_one_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hleftExclusive
        (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
          inputLevel left assignmentCode assignmentStep
          hleftAdmissible hleftZero) hleftPi).
    + destruct (raw_rankZeroTruthCertificate_and_view M hPA
        (rawFormulaAndCode M left right) (rawNumeralValue M 1)
        assignmentCode assignmentStep left right eq_refl hsigmaZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_andTruth_one_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hrightExclusive
        (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
          inputLevel right assignmentCode assignmentStep
          hrightAdmissible hrightZero) hrightPi).
  - destruct hpiView as [hpiZero | [hleftPi | hrightPi]].
    + destruct (raw_rankZeroTruthCertificate_and_view M hPA
        (rawFormulaAndCode M left right) (raw_zero M)
        assignmentCode assignmentStep left right eq_refl hpiZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_andTruth_zero_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput | hrightOutput].
      * subst leftOutput.
        exact (hleftExclusive hleftSigma
          (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
            inputLevel left assignmentCode assignmentStep
            hleftAdmissible hleftZero)).
      * subst rightOutput.
        exact (hrightExclusive hrightSigma
          (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
            inputLevel right assignmentCode assignmentStep
            hrightAdmissible hrightZero)).
    + exact (hleftExclusive hleftSigma hleftPi).
    + exact (hrightExclusive hrightSigma hrightPi).
Qed.

Lemma raw_fixedLevelOr_exclusive_from_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    left assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    right assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    (rawFormulaOrCode M left right) assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible hleftExclusive hrightExclusive hsigma hpi.
  destruct (raw_fixedLevelTruthAdmissible_or_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeOr left right) assignmentCode assignmentStep
      hsigma) as hsigmaView.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeOr left right) assignmentCode assignmentStep
      hpi) as hpiView.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
  cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
  destruct hsigmaView as [hsigmaZero | [hleftSigma | hrightSigma]].
  - destruct hpiView as [hpiZero | [hleftPi hrightPi]].
    + exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
        (rawFormulaOrCode M left right) assignmentCode assignmentStep
        hsigmaZero hpiZero).
    + destruct (raw_rankZeroTruthCertificate_or_view M hPA
        (rawFormulaOrCode M left right) (rawNumeralValue M 1)
        assignmentCode assignmentStep left right eq_refl hsigmaZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_orTruth_one_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput | hrightOutput].
      * subst leftOutput.
        exact (hleftExclusive
          (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
            inputLevel left assignmentCode assignmentStep
            hleftAdmissible hleftZero) hleftPi).
      * subst rightOutput.
        exact (hrightExclusive
          (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
            inputLevel right assignmentCode assignmentStep
            hrightAdmissible hrightZero) hrightPi).
  - destruct hpiView as [hpiZero | [hleftPi hrightPi]].
    + destruct (raw_rankZeroTruthCertificate_or_view M hPA
        (rawFormulaOrCode M left right) (raw_zero M)
        assignmentCode assignmentStep left right eq_refl hpiZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_orTruth_zero_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hleftExclusive hleftSigma
        (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
          inputLevel left assignmentCode assignmentStep
          hleftAdmissible hleftZero)).
    + exact (hleftExclusive hleftSigma hleftPi).
  - destruct hpiView as [hpiZero | [hleftPi hrightPi]].
    + destruct (raw_rankZeroTruthCertificate_or_view M hPA
        (rawFormulaOrCode M left right) (raw_zero M)
        assignmentCode assignmentStep left right eq_refl hpiZero) as
        (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
      destruct (raw_orTruth_zero_elim M hPA leftOutput rightOutput htruth)
        as [hleftOutput hrightOutput].
      subst leftOutput. subst rightOutput.
      exact (hrightExclusive hrightSigma
        (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
          inputLevel right assignmentCode assignmentStep
          hrightAdmissible hrightZero)).
    + exact (hrightExclusive hrightSigma hrightPi).
Qed.

(** Under a represented binder extension, an admissible universal child has
    the Pi domain needed to lower its falsity certificate.  At level zero the
    parent quantifier itself has no domain; at a successor level the polarity
    switch is exactly the constructor rank law. *)
Lemma raw_fixedLevelTruthAdmissible_all_binder_pi_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child /\
  RawCodedAssignmentDefinedThrough M
    newAssignmentCode newAssignmentStep child /\
  RawFixedLevelPiDomain M inputLevel child.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hadmissible hprepend.
  destruct (raw_fixedLevelTruthAdmissible_all_child_core M hPA
    inputLevel child assignmentCode assignmentStep hadmissible) as
    [hchildAtomic _].
  pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
  assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
      newAssignmentCode newAssignmentStep child).
  {
    apply (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep child
      hparentAssignment hprepend).
    exact (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 5) child).
  }
  assert (hchildDomain : RawFixedLevelPiDomain M inputLevel child).
  {
    destruct inputLevel as [|lower].
    - exfalso. apply (raw_fixedLevelZeroDomain_all_false M hPA child).
      exact (proj2 (proj2 hadmissible)).
    - destruct (proj2 (proj2 hadmissible)) as [hsigma | hpi].
      + exact (raw_fixedLevelPiDomain_mono M hPA lower child
          (raw_fixedLevelSigmaDomain_all_successor M hPA lower child
            hsigma)).
      + exact (raw_fixedLevelPiDomain_all M hPA (S lower) child hpi).
  }
  repeat split; assumption.
Qed.

Lemma raw_fixedLevelTruthAdmissible_ex_binder_sigma_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaExCode M child) newAssignmentCode newAssignmentStep ->
  RawCodedFormulaAtomicallyAdequate M child /\
  RawCodedAssignmentDefinedThrough M
    newAssignmentCode newAssignmentStep child /\
  RawFixedLevelSigmaDomain M inputLevel child.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hadmissible hprepend.
  destruct (raw_fixedLevelTruthAdmissible_ex_child_core M hPA
    inputLevel child assignmentCode assignmentStep hadmissible) as
    [hchildAtomic _].
  pose proof (proj1 (proj2 hadmissible)) as hparentAssignment.
  assert (hchildAssignment : RawCodedAssignmentDefinedThrough M
      newAssignmentCode newAssignmentStep child).
  {
    apply (raw_codedAssignmentPrepend_child_defined M hPA
      assignmentCode assignmentStep witness
      (rawFormulaExCode M child) newAssignmentCode newAssignmentStep child
      hparentAssignment hprepend).
    exact (raw_formulaCodeList2_child_lt M hPA
      (rawNumeralValue M 6) child).
  }
  assert (hchildDomain : RawFixedLevelSigmaDomain M inputLevel child).
  {
    destruct inputLevel as [|lower].
    - exfalso. apply (raw_fixedLevelZeroDomain_ex_false M hPA child).
      exact (proj2 (proj2 hadmissible)).
    - destruct (proj2 (proj2 hadmissible)) as [hsigma | hpi].
      + exact (raw_fixedLevelSigmaDomain_ex M hPA (S lower) child hsigma).
      + exact (raw_fixedLevelSigmaDomain_mono M hPA lower child
          (raw_fixedLevelPiDomain_ex_successor M hPA lower child hpi)).
  }
  repeat split; assumption.
Qed.

Lemma raw_fixedLevelAll_exclusive : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    (rawFormulaAllCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep
    hadmissible hsigma hpi.
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAll child) assignmentCode assignmentStep
      hsigma) as hsigmaView.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAll child) assignmentCode assignmentStep
      hpi) as hpiView.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
  cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
  destruct hsigmaView as [hrankZero | hnone].
  - exact (raw_rankZeroTruthCertificate_all_false M hPA child
      (rawNumeralValue M 1) assignmentCode assignmentStep hrankZero).
  - destruct hpiView as
      [hrankZero |
       (witness & newAssignmentCode & newAssignmentStep &
        hprepend & hchildUpper)].
    + exact (raw_rankZeroTruthCertificate_all_false M hPA child
        (raw_zero M) assignmentCode assignmentStep hrankZero).
    + destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
        inputLevel child assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep hadmissible hprepend) as
        [hchildAtomic [hchildAssignment hchildDomain]].
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          inputLevel M hPA) as hcoherence.
      destruct (hcoherence child newAssignmentCode newAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_intror hchildDomain)))) as [_ hpiChild].
      apply hnone. exists witness, newAssignmentCode, newAssignmentStep.
      split; [exact hprepend |].
      exact (proj2 (hpiChild hchildDomain) hchildUpper).
Qed.

Lemma raw_fixedLevelEx_exclusive : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawFixedLevelTruthCertificateExclusiveAt M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep
    hadmissible hsigma hpi.
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeEx child) assignmentCode assignmentStep
      hsigma) as hsigmaView.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeEx child) assignmentCode assignmentStep
      hpi) as hpiView.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
  cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
  destruct hpiView as [hrankZero | hnone].
  - exact (raw_rankZeroTruthCertificate_ex_false M hPA child
      (raw_zero M) assignmentCode assignmentStep hrankZero).
  - destruct hsigmaView as
      [hrankZero |
       (witness & newAssignmentCode & newAssignmentStep &
        hprepend & hchildUpper)].
    + exact (raw_rankZeroTruthCertificate_ex_false M hPA child
        (rawNumeralValue M 1) assignmentCode assignmentStep hrankZero).
    + destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
        inputLevel child assignmentCode assignmentStep witness
        newAssignmentCode newAssignmentStep hadmissible hprepend) as
        [hchildAtomic [hchildAssignment hchildDomain]].
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          inputLevel M hPA) as hcoherence.
      destruct (hcoherence child newAssignmentCode newAssignmentStep
        (conj hchildAtomic
          (conj hchildAssignment (or_introl hchildDomain)))) as
        [hsigmaChild _].
      apply hnone. exists witness, newAssignmentCode, newAssignmentStep.
      split; [exact hprepend |].
      exact (proj2 (hsigmaChild hchildDomain) hchildUpper).
Qed.

(** The induction step inspects the honest syntax row at the fresh code.
    Boolean payloads are numerically smaller than their parent list code, so
    their two certificates contradict the prefix hypothesis.  Quantifiers do
    not recurse on the child code here: their opposite-polarity root clauses
    meet directly after adjacent-level coherence under the binder extension. *)
Lemma raw_fixedLevelTruthCertificateExclusiveBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel current,
  RawFixedLevelTruthCertificateExclusiveBelow M inputLevel current ->
  RawFixedLevelTruthCertificateExclusiveBelow M inputLevel
    (raw_succ M current).
Proof.
  intros M hPA inputLevel current hbelow
    root assignmentCode assignmentStep hrootSucc hadmissible hsigma hpi.
  destruct (raw_lt_succ_cases M hPA root current hrootSucc)
    as [hrootCurrent | hrootCurrent].
  - exact (hbelow root assignmentCode assignmentStep hrootCurrent
      hadmissible hsigma hpi).
  - subst root.
    pose proof hadmissible as hadmissibleFull.
    destruct hadmissible as
      [hatomic [hassignment hinputDomain]].
    destruct hatomic as
      (formulaCode & formulaStep & formulaBound & rootIndex &
       hsyntax & hatomicTerms).
    pose proof hsyntax as hsyntaxParts.
    destruct hsyntaxParts as
      [_ [hrootBelow [hrootLookup hsyntaxRows]]].
    pose proof (hsyntaxRows rootIndex current
      hrootBelow hrootLookup) as hrootRow.
    destruct (raw_codedFormulaSyntaxTraversalRow_shape M
      formulaCode formulaStep rootIndex current hrootRow) as
      (shape & hcurrentCode & hshape).
    destruct shape as
      [eqLeft eqRight
      | (* bottom *)
      | impLeft impRight
      | andLeft andRight
      | orLeft orRight
      | allChild
      | exChild];
      cbn [rawCodedFormulaShapeCode] in hcurrentCode;
      subst current.
    + pose proof
      (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
        inputLevel (rawShapeEq eqLeft eqRight)
        assignmentCode assignmentStep hsigma) as hsigmaView.
    pose proof
      (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
        inputLevel (rawShapeEq eqLeft eqRight)
        assignmentCode assignmentStep hpi) as hpiView.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
    cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
    destruct hsigmaView as [hsigmaZero | []].
    destruct hpiView as [hpiZero | []].
    exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
      (rawFormulaEqCode M eqLeft eqRight)
      assignmentCode assignmentStep hsigmaZero hpiZero).
    + pose proof
      (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
        inputLevel rawShapeBot assignmentCode assignmentStep hsigma)
      as hsigmaView.
    pose proof
      (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
        inputLevel rawShapeBot assignmentCode assignmentStep hpi)
      as hpiView.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hsigmaView.
    cbn [RawFixedLevelPiSuccessorShapeView] in hpiView.
    destruct hsigmaView as [hsigmaZero | []].
    destruct hpiView as [hpiZero | []].
    exact (raw_rankZeroTruthCertificate_one_zero_exclusive M hPA
      (rawFormulaBotCode M) assignmentCode assignmentStep
      hsigmaZero hpiZero).
    + destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA
      inputLevel impLeft impRight assignmentCode assignmentStep
      hadmissibleFull) as [hleftAdmissible hrightAdmissible].
    apply (raw_fixedLevelImp_exclusive_from_children M hPA inputLevel
      impLeft impRight assignmentCode assignmentStep hadmissibleFull).
      * intros hleftSigma hleftPi.
      exact (hbelow impLeft assignmentCode assignmentStep
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 2) impLeft impRight)
        hleftAdmissible hleftSigma hleftPi).
      * intros hrightSigma hrightPi.
      exact (hbelow impRight assignmentCode assignmentStep
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 2) impLeft impRight)
        hrightAdmissible hrightSigma hrightPi).
      * exact hsigma.
      * exact hpi.
    + destruct (raw_fixedLevelTruthAdmissible_and_children M hPA
      inputLevel andLeft andRight assignmentCode assignmentStep
      hadmissibleFull) as [hleftAdmissible hrightAdmissible].
    apply (raw_fixedLevelAnd_exclusive_from_children M hPA inputLevel
      andLeft andRight assignmentCode assignmentStep hadmissibleFull).
      * intros hleftSigma hleftPi.
      exact (hbelow andLeft assignmentCode assignmentStep
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 3) andLeft andRight)
        hleftAdmissible hleftSigma hleftPi).
      * intros hrightSigma hrightPi.
      exact (hbelow andRight assignmentCode assignmentStep
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 3) andLeft andRight)
        hrightAdmissible hrightSigma hrightPi).
      * exact hsigma.
      * exact hpi.
    + destruct (raw_fixedLevelTruthAdmissible_or_children M hPA
      inputLevel orLeft orRight assignmentCode assignmentStep
      hadmissibleFull) as [hleftAdmissible hrightAdmissible].
    apply (raw_fixedLevelOr_exclusive_from_children M hPA inputLevel
      orLeft orRight assignmentCode assignmentStep hadmissibleFull).
      * intros hleftSigma hleftPi.
      exact (hbelow orLeft assignmentCode assignmentStep
        (raw_formulaCodeList3_left_lt M hPA
          (rawNumeralValue M 4) orLeft orRight)
        hleftAdmissible hleftSigma hleftPi).
      * intros hrightSigma hrightPi.
      exact (hbelow orRight assignmentCode assignmentStep
        (raw_formulaCodeList3_right_lt M hPA
          (rawNumeralValue M 4) orLeft orRight)
        hrightAdmissible hrightSigma hrightPi).
      * exact hsigma.
      * exact hpi.
    + exact (raw_fixedLevelAll_exclusive M hPA inputLevel allChild
      assignmentCode assignmentStep hadmissibleFull hsigma hpi).
    + exact (raw_fixedLevelEx_exclusive M hPA inputLevel exChild
      assignmentCode assignmentStep hadmissibleFull hsigma hpi).
Qed.

(** PA's represented induction ranges over every carrier element, including
    nonstandard formula codes. *)
Theorem raw_fixedLevelTruthCertificateExclusiveBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel current,
  RawFixedLevelTruthCertificateExclusiveBelow M inputLevel current.
Proof.
  intros M hPA inputLevel.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := fixedLevelTruthCertificateExclusiveBelowTermAt
    inputLevel (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_fixedLevelTruthCertificateExclusiveBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv) inputLevel (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_fixedLevelTruthCertificateExclusiveBelow_zero M hPA
        inputLevel).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelTruthCertificateExclusiveBelowTermAt_iff M
          (scons M current parameterEnv) inputLevel (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_fixedLevelTruthCertificateExclusiveBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          inputLevel (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelTruthCertificateExclusiveBelow_succ M hPA
        inputLevel current hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelTruthCertificateExclusiveBelowTermAt_iff M
      (scons M current parameterEnv) inputLevel (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

Definition RawFixedLevelAdmissibleTruthCertificateExclusiveAt
    (M : RawPAModel) (inputLevel : nat) : Prop :=
  forall code assignmentCode assignmentStep : M,
    RawFixedLevelTruthAdmissible M inputLevel
      code assignmentCode assignmentStep ->
    RawFixedLevelTruthCertificateExclusiveAt M inputLevel
      code assignmentCode assignmentStep.

Arguments RawFixedLevelAdmissibleTruthCertificateExclusiveAt
  M inputLevel : clear implicits.

Theorem raw_fixedLevelAdmissibleTruthCertificate_exclusive : forall
    inputLevel (M : RawPAModel), RawPASatisfies M ->
  RawFixedLevelAdmissibleTruthCertificateExclusiveAt M inputLevel.
Proof.
  intros inputLevel M hPA code assignmentCode assignmentStep
    hadmissible hsigma hpi.
  exact (raw_fixedLevelTruthCertificateExclusiveBelow_all M hPA inputLevel
    (raw_succ M code) code assignmentCode assignmentStep
    (raw_assignment_lt_self_succ M hPA code)
    hadmissible hsigma hpi).
Qed.

(** ------------------------------------------------------------------
    Clean Boolean Tarski laws.

    These eliminators hide the rank-zero shortcut.  For example, modus
    ponens remains valid when the implication was certified by rank-zero
    evaluation: the exposed Boolean child bits either contradict the supplied
    true antecedent or replay as a true consequent. *)

Theorem raw_fixedLevelImp_sigma_modus_ponens : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    left assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    right assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible himp hleftSigma.
  destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeImp left right) assignmentCode assignmentStep
      himp) as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | [hleftPi | hrightSigma]].
  - destruct (raw_rankZeroTruthCertificate_imp_view M hPA
      (rawFormulaImpCode M left right) (rawNumeralValue M 1)
      assignmentCode assignmentStep left right eq_refl hrankZero) as
      (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
    destruct (raw_impTruth_one_elim M hPA leftOutput rightOutput htruth)
      as [hleftOutput | hrightOutput].
    + subst leftOutput. exfalso.
      exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
        inputLevel M hPA left assignmentCode assignmentStep
        hleftAdmissible hleftSigma
        (raw_rankZeroTruthCertificate_zero_as_successor_pi M hPA
          inputLevel left assignmentCode assignmentStep
          hleftAdmissible hleftZero)).
    + subst rightOutput.
      exact (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
        inputLevel right assignmentCode assignmentStep
        hrightAdmissible hrightZero).
  - exfalso.
    exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
      inputLevel M hPA left assignmentCode assignmentStep
      hleftAdmissible hleftSigma hleftPi).
  - exact hrightSigma.
Qed.

Theorem raw_fixedLevelAnd_sigma_elim : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      left assignmentCode assignmentStep /\
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      right assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible hand.
  destruct (raw_fixedLevelTruthAdmissible_and_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAnd left right) assignmentCode assignmentStep
      hand) as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hboth]; [|exact hboth].
  destruct (raw_rankZeroTruthCertificate_and_view M hPA
    (rawFormulaAndCode M left right) (rawNumeralValue M 1)
    assignmentCode assignmentStep left right eq_refl hrankZero) as
    (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
  destruct (raw_andTruth_one_elim M hPA leftOutput rightOutput htruth)
    as [hleftOutput hrightOutput].
  subst leftOutput. subst rightOutput. split.
  - exact (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel left assignmentCode assignmentStep
      hleftAdmissible hleftZero).
  - exact (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel right assignmentCode assignmentStep
      hrightAdmissible hrightZero).
Qed.

Theorem raw_fixedLevelOr_sigma_elim : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      left assignmentCode assignmentStep \/
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      right assignmentCode assignmentStep.
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible hor.
  destruct (raw_fixedLevelTruthAdmissible_or_children M hPA inputLevel
    left right assignmentCode assignmentStep hadmissible) as
    [hleftAdmissible hrightAdmissible].
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeOr left right) assignmentCode assignmentStep
      hor) as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hchosen]; [|exact hchosen].
  destruct (raw_rankZeroTruthCertificate_or_view M hPA
    (rawFormulaOrCode M left right) (rawNumeralValue M 1)
    assignmentCode assignmentStep left right eq_refl hrankZero) as
    (leftOutput & rightOutput & hleftZero & hrightZero & htruth).
  destruct (raw_orTruth_one_elim M hPA leftOutput rightOutput htruth)
    as [hleftOutput | hrightOutput].
  - subst leftOutput. left.
    exact (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel left assignmentCode assignmentStep
      hleftAdmissible hleftZero).
  - subst rightOutput. right.
    exact (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel right assignmentCode assignmentStep
      hrightAdmissible hrightZero).
Qed.

(** Preferred-polarity constructor laws and the eliminators above combine
    into ordinary Tarski equivalences. *)
Theorem raw_fixedLevelImp_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaImpCode M left right) assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      (rawFormulaImpCode M left right) assignmentCode assignmentStep <->
   RawFixedLevelPiFalsityCertificate M (S inputLevel)
      left assignmentCode assignmentStep \/
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      right assignmentCode assignmentStep).
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible. split.
  - intros himp.
    destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA inputLevel
      left right assignmentCode assignmentStep hadmissible) as
      [hleftAdmissible hrightAdmissible].
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA left assignmentCode assignmentStep hleftAdmissible)
      as [hleftSigma | hleftPi].
    + right. exact (raw_fixedLevelImp_sigma_modus_ponens M hPA inputLevel
        left right assignmentCode assignmentStep hadmissible
        himp hleftSigma).
    + now left.
  - intros [hleftPi | hrightSigma].
    + apply (raw_fixedLevelImp_sigma_of_left_pi M hPA inputLevel
        left right assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          inputLevel (rawFormulaImpCode M left right)
          assignmentCode assignmentStep hadmissible)).
      * exact hleftPi.
    + apply (raw_fixedLevelImp_sigma_of_right_sigma M hPA inputLevel
        left right assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          inputLevel (rawFormulaImpCode M left right)
          assignmentCode assignmentStep hadmissible)).
      * exact hrightSigma.
Qed.

Theorem raw_fixedLevelAnd_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAndCode M left right) assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      (rawFormulaAndCode M left right) assignmentCode assignmentStep <->
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      left assignmentCode assignmentStep /\
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      right assignmentCode assignmentStep).
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible. split.
  - exact (raw_fixedLevelAnd_sigma_elim M hPA inputLevel left right
      assignmentCode assignmentStep hadmissible).
  - intros [hleft hright].
    apply (raw_fixedLevelAnd_sigma_of_both M hPA inputLevel
      left right assignmentCode assignmentStep).
    + exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
        inputLevel (rawFormulaAndCode M left right)
        assignmentCode assignmentStep hadmissible)).
    + exact hleft.
    + exact hright.
Qed.

Theorem raw_fixedLevelOr_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel left right
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaOrCode M left right) assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      (rawFormulaOrCode M left right) assignmentCode assignmentStep <->
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      left assignmentCode assignmentStep \/
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      right assignmentCode assignmentStep).
Proof.
  intros M hPA inputLevel left right assignmentCode assignmentStep
    hadmissible. split.
  - exact (raw_fixedLevelOr_sigma_elim M hPA inputLevel left right
      assignmentCode assignmentStep hadmissible).
  - intros [hleft | hright].
    + apply (raw_fixedLevelOr_sigma_of_left_sigma M hPA inputLevel
        left right assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          inputLevel (rawFormulaOrCode M left right)
          assignmentCode assignmentStep hadmissible)).
      * exact hleft.
    + apply (raw_fixedLevelOr_sigma_of_right_sigma M hPA inputLevel
        left right assignmentCode assignmentStep).
      * exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
          inputLevel (rawFormulaOrCode M left right)
          assignmentCode assignmentStep hadmissible)).
      * exact hright.
Qed.

(** ------------------------------------------------------------------
    Quantified witness and instantiation laws. *)

Theorem raw_fixedLevelEx_sigma_witness : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  exists witness newAssignmentCode newAssignmentStep : M,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaExCode M child) newAssignmentCode newAssignmentStep /\
    RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      child newAssignmentCode newAssignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep
    hadmissible hsigma.
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeEx child) assignmentCode assignmentStep
      hsigma) as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hwitness].
  - exact (False_rect _
      (raw_rankZeroTruthCertificate_ex_false M hPA child
        (rawNumeralValue M 1) assignmentCode assignmentStep hrankZero)).
  - exact hwitness.
Qed.

Theorem raw_fixedLevelEx_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      (rawFormulaExCode M child) assignmentCode assignmentStep <->
   exists witness newAssignmentCode newAssignmentStep : M,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaExCode M child) newAssignmentCode newAssignmentStep /\
    RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      child newAssignmentCode newAssignmentStep).
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep
    hadmissible. split.
  - exact (raw_fixedLevelEx_sigma_witness M hPA inputLevel child
      assignmentCode assignmentStep hadmissible).
  - intros (witness & newAssignmentCode & newAssignmentStep &
      hprepend & hchild).
    apply (raw_fixedLevelEx_sigma_of_witness M hPA inputLevel child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep).
    + exact (proj1 (raw_fixedLevelTruthAdmissible_successor_domains M hPA
        inputLevel (rawFormulaExCode M child)
        assignmentCode assignmentStep hadmissible)).
    + exact hprepend.
    + exact hchild.
Qed.

Theorem raw_fixedLevelAll_pi_witness : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S inputLevel)
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  exists witness newAssignmentCode newAssignmentStep : M,
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
      (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep /\
    RawFixedLevelPiFalsityCertificate M (S inputLevel)
      child newAssignmentCode newAssignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep
    hadmissible hpi.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAll child) assignmentCode assignmentStep
      hpi) as hview.
  cbn [RawFixedLevelPiSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hwitness].
  - exact (False_rect _
      (raw_rankZeroTruthCertificate_all_false M hPA child
        (raw_zero M) assignmentCode assignmentStep hrankZero)).
  - exact hwitness.
Qed.

Theorem raw_fixedLevelAll_sigma_instantiate : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawFormulaAllCode M child) assignmentCode assignmentStep ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaAllCode M child) newAssignmentCode newAssignmentStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    child newAssignmentCode newAssignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hadmissible hsigma hprepend.
  pose proof
    (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
      inputLevel (rawShapeAll child) assignmentCode assignmentStep
      hsigma) as hview.
  cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hnone].
  - exact (False_rect _
      (raw_rankZeroTruthCertificate_all_false M hPA child
        (rawNumeralValue M 1) assignmentCode assignmentStep hrankZero)).
  - destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
      inputLevel child assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep hadmissible hprepend) as
      [hchildAtomic [hchildAssignment hchildDomain]].
    assert (hchildAdmissible : RawFixedLevelTruthAdmissible M inputLevel
        child newAssignmentCode newAssignmentStep).
    {
      exact (conj hchildAtomic
        (conj hchildAssignment (or_intror hchildDomain))).
    }
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA child newAssignmentCode newAssignmentStep
      hchildAdmissible) as [hchildSigma | hchildPi].
    + exact hchildSigma.
    + exfalso. apply hnone.
      exists witness, newAssignmentCode, newAssignmentStep.
      split; [exact hprepend |].
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          inputLevel M hPA) as hcoherence.
      destruct (hcoherence child newAssignmentCode newAssignmentStep
        hchildAdmissible) as [_ hpiCoherence].
      exact (proj2 (hpiCoherence hchildDomain) hchildPi).
Qed.

Theorem raw_fixedLevelEx_pi_instantiate : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel child
      assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep,
  RawFixedLevelTruthAdmissible M inputLevel
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S inputLevel)
    (rawFormulaExCode M child) assignmentCode assignmentStep ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness
    (rawFormulaExCode M child) newAssignmentCode newAssignmentStep ->
  RawFixedLevelPiFalsityCertificate M (S inputLevel)
    child newAssignmentCode newAssignmentStep.
Proof.
  intros M hPA inputLevel child assignmentCode assignmentStep witness
    newAssignmentCode newAssignmentStep hadmissible hpi hprepend.
  pose proof
    (raw_fixedLevelPiFalsityCertificate_successor_shape_view M hPA
      inputLevel (rawShapeEx child) assignmentCode assignmentStep
      hpi) as hview.
  cbn [RawFixedLevelPiSuccessorShapeView] in hview.
  destruct hview as [hrankZero | hnone].
  - exact (False_rect _
      (raw_rankZeroTruthCertificate_ex_false M hPA child
        (raw_zero M) assignmentCode assignmentStep hrankZero)).
  - destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
      inputLevel child assignmentCode assignmentStep witness
      newAssignmentCode newAssignmentStep hadmissible hprepend) as
      [hchildAtomic [hchildAssignment hchildDomain]].
    assert (hchildAdmissible : RawFixedLevelTruthAdmissible M inputLevel
        child newAssignmentCode newAssignmentStep).
    {
      exact (conj hchildAtomic
        (conj hchildAssignment (or_introl hchildDomain))).
    }
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA child newAssignmentCode newAssignmentStep
      hchildAdmissible) as [hchildSigma | hchildPi].
    + exfalso. apply hnone.
      exists witness, newAssignmentCode, newAssignmentStep.
      split; [exact hprepend |].
      pose proof
        (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
          inputLevel M hPA) as hcoherence.
      destruct (hcoherence child newAssignmentCode newAssignmentStep
        hchildAdmissible) as [hsigmaCoherence _].
      exact (proj2 (hsigmaCoherence hchildDomain) hchildSigma).
    + exact hchildPi.
Qed.

(** Exact represented statement proved by PA for every external input level. *)
Definition fixedLevelAdmissibleTruthCertificateExclusiveFormula
    (inputLevel : nat) : formula :=
  pAll (pAll (pAll
    (pImp
      (fixedLevelTruthAdmissibleTermAt inputLevel
        (tVar 2) (tVar 1) (tVar 0))
      (pImp
        (fixedLevelSigmaTruthCertificateTermAt (S inputLevel)
          (tVar 2) (tVar 1) (tVar 0))
        (pImp
          (fixedLevelPiFalsityCertificateTermAt (S inputLevel)
            (tVar 2) (tVar 1) (tVar 0))
          pBot))))).

Lemma raw_sat_fixedLevelAdmissibleTruthCertificateExclusiveFormula_iff :
    forall (M : RawPAModel) e inputLevel,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel) <->
  RawFixedLevelAdmissibleTruthCertificateExclusiveAt M inputLevel.
Proof.
  intros M e inputLevel.
  unfold fixedLevelAdmissibleTruthCertificateExclusiveFormula,
    RawFixedLevelAdmissibleTruthCertificateExclusiveAt,
    RawFixedLevelTruthCertificateExclusiveAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem fixedLevelAdmissibleTruthCertificateExclusiveFormula_raw_valid :
    forall inputLevel (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel).
Proof.
  intros inputLevel M hPA e.
  apply (proj2
    (raw_sat_fixedLevelAdmissibleTruthCertificateExclusiveFormula_iff
      M e inputLevel)).
  exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
    inputLevel M hPA).
Qed.

Definition fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed
    (inputLevel : nat) : formula :=
  Formula.sealPA
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel).

Theorem fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed_sentence :
    forall inputLevel,
  Formula.Sentence
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed inputLevel).
Proof.
  intros inputLevel.
  unfold fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem
    fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed_raw_valid :
    forall inputLevel (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed inputLevel).
Proof.
  intros inputLevel M hPA e.
  unfold fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed.
  apply (raw_formula_sat_sealPA_of_valid M).
  intros e'.
  exact (fixedLevelAdmissibleTruthCertificateExclusiveFormula_raw_valid
    inputLevel M hPA e').
Qed.

Theorem PA_proves_fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed :
    forall inputLevel,
  Formula.BProv Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed inputLevel).
Proof.
  intros inputLevel.
  apply PA_BProv_of_raw_valid.
  - exact
      (fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed_sentence
        inputLevel).
  - exact
      (fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed_raw_valid
        inputLevel).
Qed.

Theorem PA_proves_fixedLevelAdmissibleTruthCertificateExclusiveFormula :
    forall inputLevel,
  Formula.BProv Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel).
Proof.
  intros inputLevel.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateExclusiveFormula inputLevel)
    (fun n => n)
    (PA_proves_fixedLevelAdmissibleTruthCertificateExclusiveFormula_closed
      inputLevel)) as hclosed.
  now rewrite Formula.rename_id in hclosed.
Qed.

End PABoundedRawCodedFixedLevelTruthLaws.
