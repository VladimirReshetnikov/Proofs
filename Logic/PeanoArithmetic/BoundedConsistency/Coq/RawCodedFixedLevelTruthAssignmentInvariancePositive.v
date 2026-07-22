(**
  Positive fixed-level truth is local to the represented assignment prefix.

  The rank-zero locality theorem is not by itself enough for quantified
  formulae.  A quantifier creates a fresh beta-coded assignment, and two
  such assignments need not have the same code even when they represent the
  same finite sequence.  We therefore prove locality by PA-definable
  induction on the (possibly nonstandard) formula code.  At a binder the
  induction hypothesis is applied to two independently chosen prepends with
  the same head; the lemma below shows that those prepends agree through the
  child formula.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankTraversal
  RawCodedFixedLevelTruth RawCodedFixedLevelTruthTraversal
  RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelTruthSchedule
  RawCodedFixedLevelTruthAdmissibleLowering
  RawCodedFixedLevelTruthAdmissibleCoherence
  RawCodedFixedLevelTruthQuantifierConstruction
  RawCodedFixedLevelTruthLaws
  RawCodedFixedLevelTruthOperationTransport
  RawCodedFixedLevelTruthAssignmentInvariance.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthAssignmentInvariancePositive.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelTruthSchedule.
Import PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
Import PABoundedRawCodedFixedLevelTruthAdmissibleCoherence.
Import PABoundedRawCodedFixedLevelTruthQuantifierConstruction.
Import PABoundedRawCodedFixedLevelTruthLaws.
Import PABoundedRawCodedFixedLevelTruthOperationTransport.
Import PABoundedRawCodedFixedLevelTruthAssignmentInvariance.

(** Unlike [raw_codedAssignmentPrepends_agree], the two prepends here start
    from different source tables.  Agreement of the source prefixes is
    exactly what is needed at successor indices; index zero is the common
    new head. *)
Lemma raw_codedAssignmentPrepends_agree_of_sources : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftSourceCode leftSourceStep rightSourceCode rightSourceStep
      head bound leftCode leftStep rightCode rightStep,
  RawCodedAssignmentsAgreeThrough M
    leftSourceCode leftSourceStep rightSourceCode rightSourceStep bound ->
  RawCodedAssignmentDefinedThrough M
    leftSourceCode leftSourceStep bound ->
  RawCodedAssignmentDefinedThrough M
    rightSourceCode rightSourceStep bound ->
  RawCodedAssignmentPrepend M
    leftSourceCode leftSourceStep head bound leftCode leftStep ->
  RawCodedAssignmentPrepend M
    rightSourceCode rightSourceStep head bound rightCode rightStep ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep (raw_succ M bound).
Proof.
  intros M hPA leftSourceCode leftSourceStep
    rightSourceCode rightSourceStep head bound
    leftCode leftStep rightCode rightStep
    hagree hleftDefined hrightDefined hleft hright index value hindex.
  destruct (raw_assignment_zero_or_successor M hPA index)
    as [-> | [predecessor ->]].
  - rewrite (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      leftSourceCode leftSourceStep head bound
      leftCode leftStep value hleft).
    rewrite (raw_codedAssignmentPrepend_lookup_zero_iff M hPA
      rightSourceCode rightSourceStep head bound
      rightCode rightStep value hright).
    reflexivity.
  - assert (hpredecessor : rawLt M predecessor bound).
    {
      destruct (raw_lt_succ_cases M hPA
        (raw_succ M predecessor) bound hindex) as [hlt | heq].
      - exact (raw_assignment_lt_trans M hPA predecessor
          (raw_succ M predecessor) bound
          (raw_assignment_lt_self_succ M hPA predecessor) hlt).
      - rewrite <- heq.
        exact (raw_assignment_lt_self_succ M hPA predecessor).
    }
    rewrite (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      leftSourceCode leftSourceStep head bound leftCode leftStep
      hleftDefined hleft predecessor hpredecessor value).
    rewrite (raw_codedAssignmentPrepend_lookup_succ_iff M hPA
      rightSourceCode rightSourceStep head bound rightCode rightStep
      hrightDefined hright predecessor hpredecessor value).
    exact (hagree predecessor value hpredecessor).
Qed.

(** The represented induction predicate.  It says that every formula code
    below [current] has identical positive-level certificates under two
    admissible assignments that agree below that formula code. *)
Definition fixedLevelTruthAssignmentTransportBelowTermAt
    (inputLevel : nat) (current : term) : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 current))
      (pImp
        (codedAssignmentsAgreeThroughTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0) (tVar 4))
        (pImp
          (fixedLevelTruthAdmissibleTermAt inputLevel
            (tVar 4) (tVar 3) (tVar 2))
          (pImp
            (fixedLevelTruthAdmissibleTermAt inputLevel
              (tVar 4) (tVar 1) (tVar 0))
            (fixedLevelTruthCertificateTransportTermAt (S inputLevel)
              (tVar 4) (tVar 4)
              (tVar 3) (tVar 2) (tVar 1) (tVar 0)))))))))).

Definition RawFixedLevelTruthAssignmentTransportBelow
    (M : RawPAModel) (inputLevel : nat) (current : M) : Prop :=
  forall root leftCode leftStep rightCode rightStep : M,
    rawLt M root current ->
    RawCodedAssignmentsAgreeThrough M
      leftCode leftStep rightCode rightStep root ->
    RawFixedLevelTruthAdmissible M inputLevel root leftCode leftStep ->
    RawFixedLevelTruthAdmissible M inputLevel root rightCode rightStep ->
    RawFixedLevelTruthCertificateTransport M (S inputLevel)
      root root leftCode leftStep rightCode rightStep.

Arguments RawFixedLevelTruthAssignmentTransportBelow
  M inputLevel current : clear implicits.

Lemma raw_sat_fixedLevelTruthAssignmentTransportBelowTermAt_iff : forall
    (M : RawPAModel) e inputLevel current,
  raw_formula_sat M e
    (fixedLevelTruthAssignmentTransportBelowTermAt inputLevel current) <->
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel
    (raw_term_eval M e current).
Proof.
  intros M e inputLevel current.
  unfold fixedLevelTruthAssignmentTransportBelowTermAt,
    RawFixedLevelTruthAssignmentTransportBelow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentsAgreeThroughTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthAdmissibleTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelTruthCertificateTransportTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_fixedLevelTruthAssignmentTransportBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel,
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel (raw_zero M).
Proof.
  intros M hPA inputLevel root leftCode leftStep rightCode rightStep hroot.
  exfalso. exact (raw_not_lt_zero M hPA root hroot).
Qed.

(** Once Sigma truth is invariant, Pi falsity follows from totality and the
    already established admissible exclusivity theorem.  This keeps the
    constructor induction below focused on one polarity. *)
Lemma raw_fixedLevelTruthCertificateTransport_of_sigma_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel root
      leftCode leftStep rightCode rightStep,
  RawFixedLevelTruthAdmissible M inputLevel root leftCode leftStep ->
  RawFixedLevelTruthAdmissible M inputLevel root rightCode rightStep ->
  (RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      root leftCode leftStep <->
   RawFixedLevelSigmaTruthCertificate M (S inputLevel)
      root rightCode rightStep) ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    root root leftCode leftStep rightCode rightStep.
Proof.
  intros M hPA inputLevel root leftCode leftStep rightCode rightStep
    hleftAdmissible hrightAdmissible hsigma.
  split; [exact hsigma |]. split.
  - intros hleftPi.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA root rightCode rightStep hrightAdmissible)
      as [hrightSigma | hrightPi].
    + exfalso.
      exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
        inputLevel M hPA root leftCode leftStep hleftAdmissible
        (proj2 hsigma hrightSigma) hleftPi).
    + exact hrightPi.
  - intros hrightPi.
    destruct (raw_fixedLevelInputTruthCertificateTotalityAt_all
      inputLevel M hPA root leftCode leftStep hleftAdmissible)
      as [hleftSigma | hleftPi].
    + exfalso.
      exact (raw_fixedLevelAdmissibleTruthCertificate_exclusive
        inputLevel M hPA root rightCode rightStep hrightAdmissible
        (proj1 hsigma hleftSigma) hrightPi).
    + exact hleftPi.
Qed.

(** Constructor step for Sigma truth.  The prefix hypothesis already gives
    both certificate polarities on every proper child.  The only subtle case
    is [All]: a target-side lower Pi counterexample is raised one level,
    transported to a matching source prepend, and lowered again before it is
    fed to the source no-counterexample clause. *)
Lemma raw_fixedLevelSigmaTruthCertificate_assignment_transport_shape :
  forall (M : RawPAModel), RawPASatisfies M -> forall inputLevel shape
      leftCode leftStep rightCode rightStep,
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel
    (rawCodedFormulaShapeCode M shape) ->
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep
    (rawCodedFormulaShapeCode M shape) ->
  RawFixedLevelTruthAdmissible M inputLevel
    (rawCodedFormulaShapeCode M shape) leftCode leftStep ->
  RawFixedLevelTruthAdmissible M inputLevel
    (rawCodedFormulaShapeCode M shape) rightCode rightStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawCodedFormulaShapeCode M shape) leftCode leftStep ->
  RawFixedLevelSigmaTruthCertificate M (S inputLevel)
    (rawCodedFormulaShapeCode M shape) rightCode rightStep.
Proof.
  intros M hPA inputLevel shape leftCode leftStep rightCode rightStep
    hbelow hagree hleftAdmissible hrightAdmissible hleftSigma.
  destruct shape as
    [eqLeft eqRight
    | (* bottom *)
    | impLeft impRight
    | andLeft andRight
    | orLeft orRight
    | allChild
    | exChild].
  - pose proof
      (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
        inputLevel (rawShapeEq eqLeft eqRight)
        leftCode leftStep hleftSigma) as hview.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
    destruct hview as [hrankZero | []].
    apply (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel (rawFormulaEqCode M eqLeft eqRight)
      rightCode rightStep hrightAdmissible).
    exact (raw_rankZeroTruthCertificate_assignment_transport M hPA
      (rawFormulaEqCode M eqLeft eqRight) (rawNumeralValue M 1)
      leftCode leftStep rightCode rightStep hagree hrankZero).
  - pose proof
      (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
        inputLevel rawShapeBot leftCode leftStep hleftSigma) as hview.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
    destruct hview as [hrankZero | []].
    apply (raw_rankZeroTruthCertificate_one_as_successor_sigma M hPA
      inputLevel (rawFormulaBotCode M)
      rightCode rightStep hrightAdmissible).
    exact (raw_rankZeroTruthCertificate_assignment_transport M hPA
      (rawFormulaBotCode M) (rawNumeralValue M 1)
      leftCode leftStep rightCode rightStep hagree hrankZero).
  - destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA inputLevel
      impLeft impRight leftCode leftStep hleftAdmissible) as
      [hleftSourceAdmissible hrightSourceAdmissible].
    destruct (raw_fixedLevelTruthAdmissible_imp_children M hPA inputLevel
      impLeft impRight rightCode rightStep hrightAdmissible) as
      [hleftTargetAdmissible hrightTargetAdmissible].
    assert (hleftLt : rawLt M impLeft
        (rawFormulaImpCode M impLeft impRight)).
    { exact (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 2) impLeft impRight). }
    assert (hrightLt : rawLt M impRight
        (rawFormulaImpCode M impLeft impRight)).
    { exact (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 2) impLeft impRight). }
    pose proof (hbelow impLeft leftCode leftStep rightCode rightStep
      hleftLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep impLeft
        (rawFormulaImpCode M impLeft impRight) hleftLt hagree)
      hleftSourceAdmissible hleftTargetAdmissible) as hleftTransport.
    pose proof (hbelow impRight leftCode leftStep rightCode rightStep
      hrightLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep impRight
        (rawFormulaImpCode M impLeft impRight) hrightLt hagree)
      hrightSourceAdmissible hrightTargetAdmissible) as hrightTransport.
    apply (proj2 (raw_fixedLevelImp_sigma_iff M hPA inputLevel
      impLeft impRight rightCode rightStep hrightAdmissible)).
    destruct (proj1 (raw_fixedLevelImp_sigma_iff M hPA inputLevel
      impLeft impRight leftCode leftStep hleftAdmissible) hleftSigma)
      as [hleftPi | hrightSigma].
    + left. exact (proj1 (proj2 hleftTransport) hleftPi).
    + right. exact (proj1 (proj1 hrightTransport) hrightSigma).
  - destruct (raw_fixedLevelTruthAdmissible_and_children M hPA inputLevel
      andLeft andRight leftCode leftStep hleftAdmissible) as
      [hleftSourceAdmissible hrightSourceAdmissible].
    destruct (raw_fixedLevelTruthAdmissible_and_children M hPA inputLevel
      andLeft andRight rightCode rightStep hrightAdmissible) as
      [hleftTargetAdmissible hrightTargetAdmissible].
    assert (hleftLt : rawLt M andLeft
        (rawFormulaAndCode M andLeft andRight)).
    { exact (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 3) andLeft andRight). }
    assert (hrightLt : rawLt M andRight
        (rawFormulaAndCode M andLeft andRight)).
    { exact (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 3) andLeft andRight). }
    pose proof (hbelow andLeft leftCode leftStep rightCode rightStep
      hleftLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep andLeft
        (rawFormulaAndCode M andLeft andRight) hleftLt hagree)
      hleftSourceAdmissible hleftTargetAdmissible) as hleftTransport.
    pose proof (hbelow andRight leftCode leftStep rightCode rightStep
      hrightLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep andRight
        (rawFormulaAndCode M andLeft andRight) hrightLt hagree)
      hrightSourceAdmissible hrightTargetAdmissible) as hrightTransport.
    apply (proj2 (raw_fixedLevelAnd_sigma_iff M hPA inputLevel
      andLeft andRight rightCode rightStep hrightAdmissible)).
    destruct (proj1 (raw_fixedLevelAnd_sigma_iff M hPA inputLevel
      andLeft andRight leftCode leftStep hleftAdmissible) hleftSigma)
      as [hleftSigmaChild hrightSigmaChild].
    split.
    + exact (proj1 (proj1 hleftTransport) hleftSigmaChild).
    + exact (proj1 (proj1 hrightTransport) hrightSigmaChild).
  - destruct (raw_fixedLevelTruthAdmissible_or_children M hPA inputLevel
      orLeft orRight leftCode leftStep hleftAdmissible) as
      [hleftSourceAdmissible hrightSourceAdmissible].
    destruct (raw_fixedLevelTruthAdmissible_or_children M hPA inputLevel
      orLeft orRight rightCode rightStep hrightAdmissible) as
      [hleftTargetAdmissible hrightTargetAdmissible].
    assert (hleftLt : rawLt M orLeft
        (rawFormulaOrCode M orLeft orRight)).
    { exact (raw_formulaCodeList3_left_lt M hPA
        (rawNumeralValue M 4) orLeft orRight). }
    assert (hrightLt : rawLt M orRight
        (rawFormulaOrCode M orLeft orRight)).
    { exact (raw_formulaCodeList3_right_lt M hPA
        (rawNumeralValue M 4) orLeft orRight). }
    pose proof (hbelow orLeft leftCode leftStep rightCode rightStep
      hleftLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep orLeft
        (rawFormulaOrCode M orLeft orRight) hleftLt hagree)
      hleftSourceAdmissible hleftTargetAdmissible) as hleftTransport.
    pose proof (hbelow orRight leftCode leftStep rightCode rightStep
      hrightLt
      (raw_codedAssignmentsAgreeThrough_restrict M hPA
        leftCode leftStep rightCode rightStep orRight
        (rawFormulaOrCode M orLeft orRight) hrightLt hagree)
      hrightSourceAdmissible hrightTargetAdmissible) as hrightTransport.
    apply (proj2 (raw_fixedLevelOr_sigma_iff M hPA inputLevel
      orLeft orRight rightCode rightStep hrightAdmissible)).
    destruct (proj1 (raw_fixedLevelOr_sigma_iff M hPA inputLevel
      orLeft orRight leftCode leftStep hleftAdmissible) hleftSigma)
      as [hleftSigmaChild | hrightSigmaChild].
    + left. exact (proj1 (proj1 hleftTransport) hleftSigmaChild).
    + right. exact (proj1 (proj1 hrightTransport) hrightSigmaChild).
  - pose proof
      (raw_fixedLevelSigmaTruthCertificate_successor_shape_view M hPA
        inputLevel (rawShapeAll allChild)
        leftCode leftStep hleftSigma) as hview.
    cbn [RawFixedLevelSigmaSuccessorShapeView] in hview.
    destruct hview as [hrankZero | hnone].
    + exact (False_rect _
        (raw_rankZeroTruthCertificate_all_false M hPA allChild
          (rawNumeralValue M 1) leftCode leftStep hrankZero)).
    + apply (raw_fixedLevelAll_sigma_of_no_lower_pi M hPA inputLevel
        allChild rightCode rightStep).
      * exact (proj1
          (raw_fixedLevelTruthAdmissible_successor_domains M hPA
            inputLevel (rawFormulaAllCode M allChild)
            rightCode rightStep hrightAdmissible)).
      * intros (witness & rightBinderCode & rightBinderStep &
          hrightPrepend & hrightLowerPi).
        destruct (raw_codedAssignmentPrepend_exists M hPA
          leftCode leftStep witness (rawFormulaAllCode M allChild)) as
          (leftBinderCode & leftBinderStep & hleftPrepend).
        pose proof (proj1 (proj2 hleftAdmissible)) as hleftDefined.
        pose proof (proj1 (proj2 hrightAdmissible)) as hrightDefined.
        pose proof
          (raw_codedAssignmentPrepends_agree_of_sources M hPA
            leftCode leftStep rightCode rightStep witness
            (rawFormulaAllCode M allChild)
            leftBinderCode leftBinderStep rightBinderCode rightBinderStep
            hagree hleftDefined hrightDefined
            hleftPrepend hrightPrepend) as hbindersAgreeSucc.
        assert (hchildLt : rawLt M allChild
            (rawFormulaAllCode M allChild)).
        { exact (raw_formulaCodeList2_child_lt M hPA
            (rawNumeralValue M 5) allChild). }
        assert (hchildLtSucc : rawLt M allChild
            (raw_succ M (rawFormulaAllCode M allChild))).
        { exact (raw_assignment_lt_trans M hPA allChild
            (rawFormulaAllCode M allChild)
            (raw_succ M (rawFormulaAllCode M allChild)) hchildLt
            (raw_assignment_lt_self_succ M hPA
              (rawFormulaAllCode M allChild))). }
        pose proof
          (raw_codedAssignmentsAgreeThrough_restrict M hPA
            leftBinderCode leftBinderStep rightBinderCode rightBinderStep
            allChild (raw_succ M (rawFormulaAllCode M allChild))
            hchildLtSucc hbindersAgreeSucc) as hbindersAgree.
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel allChild leftCode leftStep witness
          leftBinderCode leftBinderStep
          hleftAdmissible hleftPrepend) as
          [hleftChildAtomic [hleftChildDefined hleftChildDomain]].
        destruct (raw_fixedLevelTruthAdmissible_all_binder_pi_core M hPA
          inputLevel allChild rightCode rightStep witness
          rightBinderCode rightBinderStep
          hrightAdmissible hrightPrepend) as
          [hrightChildAtomic [hrightChildDefined hrightChildDomain]].
        assert (hleftChildAdmissible :
            RawFixedLevelTruthAdmissible M inputLevel allChild
              leftBinderCode leftBinderStep).
        { exact (conj hleftChildAtomic
            (conj hleftChildDefined (or_intror hleftChildDomain))). }
        assert (hrightChildAdmissible :
            RawFixedLevelTruthAdmissible M inputLevel allChild
              rightBinderCode rightBinderStep).
        { exact (conj hrightChildAtomic
            (conj hrightChildDefined (or_intror hrightChildDomain))). }
        pose proof (hbelow allChild
          leftBinderCode leftBinderStep rightBinderCode rightBinderStep
          hchildLt hbindersAgree
          hleftChildAdmissible hrightChildAdmissible) as hchildTransport.
        pose proof
          (raw_fixedLevelAdmissibleTruthCertificateCoherence_all
            inputLevel M hPA) as hcoherence.
        destruct (hcoherence allChild rightBinderCode rightBinderStep
          hrightChildAdmissible) as [_ hrightPiCoherence].
        pose proof (proj1 (hrightPiCoherence hrightChildDomain)
          hrightLowerPi) as hrightUpperPi.
        pose proof (proj2 (proj2 hchildTransport) hrightUpperPi)
          as hleftUpperPi.
        destruct (hcoherence allChild leftBinderCode leftBinderStep
          hleftChildAdmissible) as [_ hleftPiCoherence].
        pose proof (proj2 (hleftPiCoherence hleftChildDomain)
          hleftUpperPi) as hleftLowerPi.
        apply hnone. exists witness, leftBinderCode, leftBinderStep.
        now split.
  - destruct (proj1 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
      exChild leftCode leftStep hleftAdmissible) hleftSigma) as
      (witness & leftBinderCode & leftBinderStep &
       hleftPrepend & hleftChildSigma).
    destruct (raw_codedAssignmentPrepend_exists M hPA
      rightCode rightStep witness (rawFormulaExCode M exChild)) as
      (rightBinderCode & rightBinderStep & hrightPrepend).
    pose proof (proj1 (proj2 hleftAdmissible)) as hleftDefined.
    pose proof (proj1 (proj2 hrightAdmissible)) as hrightDefined.
    pose proof
      (raw_codedAssignmentPrepends_agree_of_sources M hPA
        leftCode leftStep rightCode rightStep witness
        (rawFormulaExCode M exChild)
        leftBinderCode leftBinderStep rightBinderCode rightBinderStep
        hagree hleftDefined hrightDefined
        hleftPrepend hrightPrepend) as hbindersAgreeSucc.
    assert (hchildLt : rawLt M exChild (rawFormulaExCode M exChild)).
    { exact (raw_formulaCodeList2_child_lt M hPA
        (rawNumeralValue M 6) exChild). }
    assert (hchildLtSucc : rawLt M exChild
        (raw_succ M (rawFormulaExCode M exChild))).
    { exact (raw_assignment_lt_trans M hPA exChild
        (rawFormulaExCode M exChild)
        (raw_succ M (rawFormulaExCode M exChild)) hchildLt
        (raw_assignment_lt_self_succ M hPA
          (rawFormulaExCode M exChild))). }
    pose proof (raw_codedAssignmentsAgreeThrough_restrict M hPA
      leftBinderCode leftBinderStep rightBinderCode rightBinderStep
      exChild (raw_succ M (rawFormulaExCode M exChild))
      hchildLtSucc hbindersAgreeSucc) as hbindersAgree.
    destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
      inputLevel exChild leftCode leftStep witness
      leftBinderCode leftBinderStep hleftAdmissible hleftPrepend) as
      [hleftChildAtomic [hleftChildDefined hleftChildDomain]].
    destruct (raw_fixedLevelTruthAdmissible_ex_binder_sigma_core M hPA
      inputLevel exChild rightCode rightStep witness
      rightBinderCode rightBinderStep hrightAdmissible hrightPrepend) as
      [hrightChildAtomic [hrightChildDefined hrightChildDomain]].
    assert (hleftChildAdmissible :
        RawFixedLevelTruthAdmissible M inputLevel exChild
          leftBinderCode leftBinderStep).
    { exact (conj hleftChildAtomic
        (conj hleftChildDefined (or_introl hleftChildDomain))). }
    assert (hrightChildAdmissible :
        RawFixedLevelTruthAdmissible M inputLevel exChild
          rightBinderCode rightBinderStep).
    { exact (conj hrightChildAtomic
        (conj hrightChildDefined (or_introl hrightChildDomain))). }
    pose proof (hbelow exChild
      leftBinderCode leftBinderStep rightBinderCode rightBinderStep
      hchildLt hbindersAgree
      hleftChildAdmissible hrightChildAdmissible) as hchildTransport.
    apply (proj2 (raw_fixedLevelEx_sigma_iff M hPA inputLevel
      exChild rightCode rightStep hrightAdmissible)).
    exists witness, rightBinderCode, rightBinderStep.
    split; [exact hrightPrepend |].
    exact (proj1 (proj1 hchildTransport) hleftChildSigma).
Qed.

(** The fresh endpoint of the represented code induction.  Atomic
    adequacy supplies an honest syntax row for [current], so every carrier
    element admitted as a formula has one of the seven constructor shapes. *)
Lemma raw_fixedLevelTruthAssignmentTransportBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel current,
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel current ->
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel
    (raw_succ M current).
Proof.
  intros M hPA inputLevel current hbelow
    root leftCode leftStep rightCode rightStep
    hrootSucc hagree hleftAdmissible hrightAdmissible.
  destruct (raw_lt_succ_cases M hPA root current hrootSucc)
    as [hrootCurrent | hrootCurrent].
  - exact (hbelow root leftCode leftStep rightCode rightStep
      hrootCurrent hagree hleftAdmissible hrightAdmissible).
  - subst root.
    pose proof hleftAdmissible as hleftAdmissibleFull.
    destruct hleftAdmissible as
      [hatomic [_ _]].
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
    subst current.
    apply (raw_fixedLevelTruthCertificateTransport_of_sigma_iff M hPA
      inputLevel (rawCodedFormulaShapeCode M shape)
      leftCode leftStep rightCode rightStep
      hleftAdmissibleFull hrightAdmissible).
    split.
    + exact (raw_fixedLevelSigmaTruthCertificate_assignment_transport_shape
        M hPA inputLevel shape leftCode leftStep rightCode rightStep
        hbelow hagree hleftAdmissibleFull hrightAdmissible).
    + exact (raw_fixedLevelSigmaTruthCertificate_assignment_transport_shape
        M hPA inputLevel shape rightCode rightStep leftCode leftStep
        hbelow
        (raw_codedAssignmentsAgreeThrough_sym M
          leftCode leftStep rightCode rightStep
          (rawCodedFormulaShapeCode M shape) hagree)
        hrightAdmissible hleftAdmissibleFull).
Qed.

(** PA's induction axiom, rather than Coq induction over syntax, is essential
    here: [current] and the formula codes quantified by the invariant may be
    nonstandard elements of an arbitrary model of PA. *)
Theorem raw_fixedLevelTruthAssignmentTransportBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel current,
  RawFixedLevelTruthAssignmentTransportBelow M inputLevel current.
Proof.
  intros M hPA inputLevel.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := fixedLevelTruthAssignmentTransportBelowTermAt
    inputLevel (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_fixedLevelTruthAssignmentTransportBelowTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          inputLevel (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_fixedLevelTruthAssignmentTransportBelow_zero M hPA
        inputLevel).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelTruthAssignmentTransportBelowTermAt_iff M
          (scons M current parameterEnv) inputLevel (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_fixedLevelTruthAssignmentTransportBelowTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          inputLevel (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelTruthAssignmentTransportBelow_succ M hPA
        inputLevel current hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelTruthAssignmentTransportBelowTermAt_iff M
      (scons M current parameterEnv) inputLevel (tVar 0))
    (hall current)) as hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Public locality theorem.  This is the exact semantic normalization used
    by All-I and Ex-E: admissible fixed-level truth depends only on assignment
    rows whose indices are below the formula code. *)
Theorem raw_fixedLevelTruthCertificate_assignment_invariance : forall
    (M : RawPAModel), RawPASatisfies M -> forall inputLevel root
      leftCode leftStep rightCode rightStep,
  RawCodedAssignmentsAgreeThrough M
    leftCode leftStep rightCode rightStep root ->
  RawFixedLevelTruthAdmissible M inputLevel root leftCode leftStep ->
  RawFixedLevelTruthAdmissible M inputLevel root rightCode rightStep ->
  RawFixedLevelTruthCertificateTransport M (S inputLevel)
    root root leftCode leftStep rightCode rightStep.
Proof.
  intros M hPA inputLevel root leftCode leftStep rightCode rightStep
    hagree hleftAdmissible hrightAdmissible.
  exact (raw_fixedLevelTruthAssignmentTransportBelow_all M hPA
    inputLevel (raw_succ M root)
    root leftCode leftStep rightCode rightStep
    (raw_assignment_lt_self_succ M hPA root)
    hagree hleftAdmissible hrightAdmissible).
Qed.

End PABoundedRawCodedFixedLevelTruthAssignmentInvariancePositive.
