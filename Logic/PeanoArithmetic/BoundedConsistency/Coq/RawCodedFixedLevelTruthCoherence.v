(**
  Adjacent-level transport for globally closed fixed-level truth.

  There are two logically distinct issues in a coherence proof.  Raising a
  certificate is local: its very same beta tables can be replayed one level
  higher.  Lowering is not local, because an upper certificate is permitted
  to contain unrelated high-rank rows before its root; those rows cannot be
  reinterpreted at the lower level.  This file first isolates the completely
  general raising direction.  In the positive-level case only an
  opposite-quantifier leaf changes its recursive predicate, and exactly the
  backward half of coherence at the preceding level is needed there.

  The domain-only coherence proposition originally exposed by
  [RawCodedFixedLevelTruthTotality] is intentionally not asserted here.  At
  level zero it is false without atomic-term adequacy: a level-one Boolean
  certificate may short-circuit around a malformed equality payload, whereas
  the rank-zero evaluator validates the entire quantifier-free formula.  The
  final coherence theorem must consequently be guarded by the honest
  admissibility predicate from the totality module.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality RawCodedFixedLevelDomainLaws.

Module PABoundedRawCodedFixedLevelTruthCoherence.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.

(** ------------------------------------------------------------------
    The corrected coherence boundary.

    The guard is deliberately the *whole* admissibility predicate.  Merely
    conjoining a rank domain is insufficient at level zero, since rank
    traversals regard equality payloads as opaque numbers.  Admissibility
    supplies a genuine formula traversal, assignment definedness, and term
    syntax for every equality payload under every sufficiently defined
    assignment. *)

Definition RawFixedLevelAdmissibleTruthCertificateCoherenceAt
    (M : RawPAModel) (lower : nat) : Prop :=
  forall root assignmentCode assignmentStep : M,
    RawFixedLevelTruthAdmissible M lower
      root assignmentCode assignmentStep ->
    (RawFixedLevelSigmaDomain M lower root ->
      (RawFixedLevelSigmaTruthCertificate M lower
          root assignmentCode assignmentStep <->
       RawFixedLevelSigmaTruthCertificate M (S lower)
          root assignmentCode assignmentStep)) /\
    (RawFixedLevelPiDomain M lower root ->
      (RawFixedLevelPiFalsityCertificate M lower
          root assignmentCode assignmentStep <->
       RawFixedLevelPiFalsityCertificate M (S lower)
          root assignmentCode assignmentStep)).

Arguments RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower
  : clear implicits.

Definition fixedLevelAdmissibleTruthCertificateCoherenceFormula
    (lower : nat) : formula :=
  pAll (pAll (pAll
    (pImp
      (fixedLevelTruthAdmissibleTermAt lower
        (tVar 2) (tVar 1) (tVar 0))
      (pAnd
        (pImp
          (fixedLevelSigmaDomainTermAt lower (tVar 2))
          (pAnd
            (pImp
              (fixedLevelSigmaTruthCertificateTermAt lower
                (tVar 2) (tVar 1) (tVar 0))
              (fixedLevelSigmaTruthCertificateTermAt (S lower)
                (tVar 2) (tVar 1) (tVar 0)))
            (pImp
              (fixedLevelSigmaTruthCertificateTermAt (S lower)
                (tVar 2) (tVar 1) (tVar 0))
              (fixedLevelSigmaTruthCertificateTermAt lower
                (tVar 2) (tVar 1) (tVar 0)))))
        (pImp
          (fixedLevelPiDomainTermAt lower (tVar 2))
          (pAnd
            (pImp
              (fixedLevelPiFalsityCertificateTermAt lower
                (tVar 2) (tVar 1) (tVar 0))
              (fixedLevelPiFalsityCertificateTermAt (S lower)
                (tVar 2) (tVar 1) (tVar 0)))
            (pImp
              (fixedLevelPiFalsityCertificateTermAt (S lower)
                (tVar 2) (tVar 1) (tVar 0))
              (fixedLevelPiFalsityCertificateTermAt lower
                (tVar 2) (tVar 1) (tVar 0))))))))).

Lemma raw_sat_fixedLevelAdmissibleTruthCertificateCoherenceFormula_iff :
  forall (M : RawPAModel) e lower,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula lower) <->
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M lower.
Proof.
  intros M e lower.
  unfold fixedLevelAdmissibleTruthCertificateCoherenceFormula,
    RawFixedLevelAdmissibleTruthCertificateCoherenceAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiDomainTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros hall root assignmentCode assignmentStep hadmissible.
    specialize (hall root assignmentCode assignmentStep hadmissible).
    destruct hall as [hsigma hpi]. split.
    + intros hdomain. specialize (hsigma hdomain). tauto.
    + intros hdomain. specialize (hpi hdomain). tauto.
  - intros hall root assignmentCode assignmentStep hadmissible.
    specialize (hall root assignmentCode assignmentStep hadmissible).
    destruct hall as [hsigma hpi]. split.
    + intros hdomain. specialize (hsigma hdomain). tauto.
    + intros hdomain. specialize (hpi hdomain). tauto.
Qed.

(** ------------------------------------------------------------------
    Raising level-zero rows. *)

Lemma raw_fixedLevelClosedZeroRow_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  RawFixedLevelClosedZeroRow M mode code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M 0
    (RawFixedLevelSigmaTruthCertificate M 0)
    (RawFixedLevelPiFalsityCertificate M 0)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep
    [[hmode [hdomain htruth]] | [hmode [hdomain hfalse]]].
  - left. split; [exact hmode |].
    exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split.
    + exact (raw_fixedLevelSigmaDomain_mono M hPA 0 code hdomain).
    + left. exact htruth.
  - right. split; [exact hmode |].
    exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
    split.
    + exact (raw_fixedLevelPiDomain_mono M hPA 0 code hdomain).
    + left. exact hfalse.
Qed.

Lemma raw_fixedLevelZeroTruthTraversal_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelZeroTruthTraversal M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthTraversal M 0
    (RawFixedLevelSigmaTruthCertificate M 0)
    (RawFixedLevelPiFalsityCertificate M 0)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep
      [hroot [hlookup hrows]]]]]].
  split; [exact hmode |].
  split; [exact hformula |].
  split; [exact hassignmentCode |].
  split; [exact hassignmentStep |].
  split; [exact hroot |].
  split; [exact hlookup |].
  intros index mode code rowAssignmentCode rowAssignmentStep
    hindex hrowLookup.
  apply (raw_fixedLevelClosedZeroRow_raise M hPA
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code rowAssignmentCode rowAssignmentStep).
  exact (hrows index mode code rowAssignmentCode rowAssignmentStep
    hindex hrowLookup).
Qed.

Theorem raw_fixedLevelTruthCertificate_zero_raise : forall
    (M : RawPAModel), RawPASatisfies M ->
  (forall root assignmentCode assignmentStep,
    RawFixedLevelSigmaTruthCertificate M 0
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M 1
      root assignmentCode assignmentStep) /\
  (forall root assignmentCode assignmentStep,
    RawFixedLevelPiFalsityCertificate M 0
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M 1
      root assignmentCode assignmentStep).
Proof.
  intros M hPA. split;
    intros root assignmentCode assignmentStep hcertificate;
    cbn [RawFixedLevelSigmaTruthCertificate
      RawFixedLevelPiFalsityCertificate] in hcertificate |- *;
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       htraversal);
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex;
    exact (raw_fixedLevelZeroTruthTraversal_raise M hPA
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex _ root assignmentCode assignmentStep htraversal).
Qed.

(** ------------------------------------------------------------------
    Raising a positive row.

    Boolean and preferred-quantifier rows keep all their table references.
    A Sigma universal changes its forbidden predicate from lower-level Pi
    falsity to the next Pi predicate.  If such an upper counterexample
    existed, constructor-domain inversion puts its child in the lower Pi
    domain and [piDown] converts it to the forbidden lower counterexample.
    The Pi existential case is dual. *)

Lemma raw_fixedLevelClosedSuccessorRow_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  (forall code assignmentCode assignmentStep,
    RawFixedLevelPiDomain M lower code ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M lower
      code assignmentCode assignmentStep) ->
  (forall code assignmentCode assignmentStep,
    RawFixedLevelSigmaDomain M lower code ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M lower
      code assignmentCode assignmentStep) ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  RawFixedLevelClosedSuccessorRow M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M (S lower)
    (RawFixedLevelSigmaTruthCertificate M (S lower))
    (RawFixedLevelPiFalsityCertificate M (S lower))
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep.
Proof.
  intros M hPA lower piDown sigmaDown
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep hrow.
  destruct hrow as [[hmode hsigma] | [hmode hpi]].
  - left. split; [exact hmode |].
    destruct hsigma as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hsigma).
    exists leftIndex, leftCode, rightIndex, rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelSigmaSuccessorWitnessRow in hsigma |- *.
    destruct hsigma as [hdomain hcases]. split.
    + exact (raw_fixedLevelSigmaDomain_mono M hPA (S lower) code hdomain).
    + destruct hcases as
        [hzero | [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]];
        [now left | now (right; left) | now (right; right; left) |
         now (right; right; right; left) |
         now (right; right; right; right; left) |
         now (right; right; right; right; right; left) |].
      right. right. right. right. right. right.
      destruct hall as [hcode hnone]. split; [exact hcode |].
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hupper).
      apply hnone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      apply (piDown leftCode binderAssignmentCode binderAssignmentStep).
      * apply (raw_fixedLevelSigmaDomain_all_successor M hPA lower leftCode).
        rewrite <- hcode. exact hdomain.
      * exact hupper.
  - right. split; [exact hmode |].
    destruct hpi as
      (leftIndex & leftCode & rightIndex & rightCode & witness &
       newAssignmentCode & newAssignmentStep & spare & hpi).
    exists leftIndex, leftCode, rightIndex, rightCode, witness,
      newAssignmentCode, newAssignmentStep, spare.
    unfold RawFixedLevelPiSuccessorWitnessRow in hpi |- *.
    destruct hpi as [hdomain hcases]. split.
    + exact (raw_fixedLevelPiDomain_mono M hPA (S lower) code hdomain).
    + destruct hcases as
        [hzero | [himp | [hand | [hor | [hall | hex]]]]];
        [now left | now (right; left) | now (right; right; left) |
         now (right; right; right; left) |
         now (right; right; right; right; left) |].
      right. right. right. right. right.
      destruct hex as [hcode hnone]. split; [exact hcode |].
      unfold RawFixedLevelNoBinderCounterexample in *.
      intros (binderWitness & binderAssignmentCode & binderAssignmentStep &
        hprepend & hupper).
      apply hnone.
      exists binderWitness, binderAssignmentCode, binderAssignmentStep.
      split; [exact hprepend |].
      apply (sigmaDown leftCode binderAssignmentCode binderAssignmentStep).
      * apply (raw_fixedLevelPiDomain_ex_successor M hPA lower leftCode).
        rewrite <- hcode. exact hdomain.
      * exact hupper.
Qed.

Lemma raw_fixedLevelSuccessorTruthTraversal_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  (forall code assignmentCode assignmentStep,
    RawFixedLevelPiDomain M lower code ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M lower
      code assignmentCode assignmentStep) ->
  (forall code assignmentCode assignmentStep,
    RawFixedLevelSigmaDomain M lower code ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M lower
      code assignmentCode assignmentStep) ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    (RawFixedLevelSigmaTruthCertificate M lower)
    (RawFixedLevelPiFalsityCertificate M lower)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelSuccessorTruthTraversal M (S lower)
    (RawFixedLevelSigmaTruthCertificate M (S lower))
    (RawFixedLevelPiFalsityCertificate M (S lower))
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep.
Proof.
  intros M hPA lower piDown sigmaDown
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep
      [hroot [hlookup hrows]]]]]].
  split; [exact hmode |].
  split; [exact hformula |].
  split; [exact hassignmentCode |].
  split; [exact hassignmentStep |].
  split; [exact hroot |].
  split; [exact hlookup |].
  intros index mode code rowAssignmentCode rowAssignmentStep
    hindex hrowLookup.
  apply (raw_fixedLevelClosedSuccessorRow_raise M hPA lower
    piDown sigmaDown
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code rowAssignmentCode rowAssignmentStep).
  exact (hrows index mode code rowAssignmentCode rowAssignmentStep
    hindex hrowLookup).
Qed.

Theorem raw_fixedLevelTruthCertificate_successor_raise : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  (forall code assignmentCode assignmentStep,
    RawFixedLevelPiDomain M lower code ->
    RawFixedLevelPiFalsityCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M lower
      code assignmentCode assignmentStep) ->
  (forall code assignmentCode assignmentStep,
    RawFixedLevelSigmaDomain M lower code ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
      code assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M lower
      code assignmentCode assignmentStep) ->
  (forall root assignmentCode assignmentStep,
    RawFixedLevelSigmaTruthCertificate M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S (S lower))
      root assignmentCode assignmentStep) /\
  (forall root assignmentCode assignmentStep,
    RawFixedLevelPiFalsityCertificate M (S lower)
      root assignmentCode assignmentStep ->
    RawFixedLevelPiFalsityCertificate M (S (S lower))
      root assignmentCode assignmentStep).
Proof.
  intros M hPA lower piDown sigmaDown. split;
    intros root assignmentCode assignmentStep hcertificate;
    cbn [RawFixedLevelSigmaTruthCertificate
      RawFixedLevelPiFalsityCertificate] in hcertificate |- *;
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       htraversal);
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex;
    exact (raw_fixedLevelSuccessorTruthTraversal_raise M hPA lower
      piDown sigmaDown
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex _ root assignmentCode assignmentStep htraversal).
Qed.

End PABoundedRawCodedFixedLevelTruthCoherence.
