(**
  Represented induction invariant for positive fixed-level truth totality.

  A model of PA may contain nonstandard formula codes, so totality cannot be
  proved by Rocq recursion over decoded syntax.  Instead PA itself inducts on
  the numeric formula code.  At stage [current], every admissible code below
  [current], under every sufficiently defined assignment, already has a
  globally closed Sigma-truth or Pi-falsity certificate at level [S lower].
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthBooleanConstruction.

Module PABoundedRawCodedFixedLevelTruthScheduleInvariant.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthBooleanConstruction.

Definition fixedLevelSuccessorTruthDecisionTermAt (lower : nat)
    (root assignmentCode assignmentStep : term) : formula :=
  pOr
    (fixedLevelSigmaTruthCertificateTermAt (S lower)
      root assignmentCode assignmentStep)
    (fixedLevelPiFalsityCertificateTermAt (S lower)
      root assignmentCode assignmentStep).

Lemma raw_sat_fixedLevelSuccessorTruthDecisionTermAt_iff : forall
    (M : RawPAModel) e lower root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelSuccessorTruthDecisionTermAt lower
      root assignmentCode assignmentStep) <->
  RawFixedLevelSuccessorTruthDecision M lower
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelSuccessorTruthDecisionTermAt,
    RawFixedLevelSuccessorTruthDecision.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff,
    raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  reflexivity.
Qed.

Lemma raw_fixedTruthSchedule_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Definition fixedLevelPositiveTruthBelowTermAt
    (lower : nat) (current : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 current))
      (pImp
        (fixedLevelTruthAdmissibleTermAt lower
          (tVar 2) (tVar 1) (tVar 0))
        (fixedLevelSuccessorTruthDecisionTermAt lower
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawFixedLevelPositiveTruthBelow (M : RawPAModel)
    (lower : nat) (current : M) : Prop :=
  forall root assignmentCode assignmentStep : M,
    rawLt M root current ->
    RawFixedLevelTruthAdmissible M lower
      root assignmentCode assignmentStep ->
    RawFixedLevelSuccessorTruthDecision M lower
      root assignmentCode assignmentStep.

Arguments RawFixedLevelPositiveTruthBelow M lower current : clear implicits.

Lemma raw_sat_fixedLevelPositiveTruthBelowTermAt_iff : forall
    (M : RawPAModel) e lower current,
  raw_formula_sat M e
    (fixedLevelPositiveTruthBelowTermAt lower current) <->
  RawFixedLevelPositiveTruthBelow M lower
    (raw_term_eval M e current).
Proof.
  intros M e lower current.
  unfold fixedLevelPositiveTruthBelowTermAt,
    RawFixedLevelPositiveTruthBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSuccessorTruthDecisionTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthSchedule_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_fixedLevelPositiveTruthBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall lower,
  RawFixedLevelPositiveTruthBelow M lower (raw_zero M).
Proof.
  intros M hPA lower root assignmentCode assignmentStep hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

(** The public endpoint formula used after the internal induction has crossed
    the chosen root code. *)
Definition fixedLevelInputTruthCertificateTotalityFormula
    (inputLevel : nat) : formula :=
  pAll (pAll (pAll
    (pImp
      (fixedLevelTruthAdmissibleTermAt inputLevel
        (tVar 2) (tVar 1) (tVar 0))
      (fixedLevelSuccessorTruthDecisionTermAt inputLevel
        (tVar 2) (tVar 1) (tVar 0))))).

Definition RawFixedLevelInputTruthCertificateTotalityAt
    (M : RawPAModel) (inputLevel : nat) : Prop :=
  forall root assignmentCode assignmentStep,
    RawFixedLevelTruthAdmissible M inputLevel
      root assignmentCode assignmentStep ->
    RawFixedLevelSuccessorTruthDecision M inputLevel
      root assignmentCode assignmentStep.

Arguments RawFixedLevelInputTruthCertificateTotalityAt M inputLevel
  : clear implicits.

Lemma raw_sat_fixedLevelInputTruthCertificateTotalityFormula_iff : forall
    (M : RawPAModel) e inputLevel,
  raw_formula_sat M e
    (fixedLevelInputTruthCertificateTotalityFormula inputLevel) <->
  RawFixedLevelInputTruthCertificateTotalityAt M inputLevel.
Proof.
  intros M e inputLevel.
  unfold fixedLevelInputTruthCertificateTotalityFormula,
    RawFixedLevelInputTruthCertificateTotalityAt,
    fixedLevelSuccessorTruthDecisionTermAt,
    RawFixedLevelSuccessorTruthDecision.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiFalsityCertificateTermAt_iff.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

End PABoundedRawCodedFixedLevelTruthScheduleInvariant.
