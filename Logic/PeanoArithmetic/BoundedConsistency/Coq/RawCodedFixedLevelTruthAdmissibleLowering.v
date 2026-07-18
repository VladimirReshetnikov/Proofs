(**
  Admissibility-guarded lowering for fixed-level truth certificates.

  Raising a certificate is a local operation and is proved in
  [RawCodedFixedLevelTruthCoherence].  Lowering has a different shape: an
  upper traversal may contain arbitrary unrelated rows, so its induction
  invariant must be conditional on the current formula being an honest
  descendant of the admissible root.  This file starts by recording the
  hereditary facts needed by that invariant.  In particular, atomic-term
  adequacy is inherited by re-rooting the same occurrence-indexed syntax
  traversal, and assignment definedness is inherited along strict code
  descent (also after a binder prepend).
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedProofDescent
  RawCodedSyntaxConstructors RawCodedSyntaxConstructorSeparation
  RawCodedAssignment
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationStepFunctionality
  RawCodedFormulaRankStep RawCodedFormulaRankTotality
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthRealization
  RawCodedRankZeroTruthTraversal RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthTotality
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTraversal RawCodedFixedLevelTruthTotality
  RawCodedFixedLevelDomainLaws RawCodedFixedLevelTruthCoherence.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthAdmissibleLowering.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationStepFunctionality.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTotality.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.
Import PABoundedRawCodedRankZeroTruthRealization.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthTotality.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTraversal.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFixedLevelDomainLaws.
Import PABoundedRawCodedFixedLevelTruthCoherence.

(** ------------------------------------------------------------------
    A code-indexed support table for the rank-zero evaluator.

    The admissibility witness is occurrence-indexed, whereas rank-zero truth
    expects a flag at the *numeric formula code*.  Marking every occurrence
    would be unsound because an occurrence traversal may contain unrelated
    rows before its root.  We therefore mark exactly those occurrence codes
    which also possess a level-zero hierarchy domain.  Boolean domain
    inversion makes this set child-closed, while the positive rank forced by
    either quantifier excludes quantified junk rows. *)

Definition RawFixedLevelZeroDomain (M : RawPAModel) (code : M) : Prop :=
  RawFixedLevelSigmaDomain M 0 code \/
  RawFixedLevelPiDomain M 0 code.

Arguments RawFixedLevelZeroDomain M code : clear implicits.

Definition fixedLevelZeroDomainTermAt (code : term) : formula :=
  pOr (fixedLevelSigmaDomainTermAt 0 code)
    (fixedLevelPiDomainTermAt 0 code).

Lemma raw_sat_fixedLevelZeroDomainTermAt_iff : forall
    (M : RawPAModel) e code,
  raw_formula_sat M e (fixedLevelZeroDomainTermAt code) <->
  RawFixedLevelZeroDomain M (raw_term_eval M e code).
Proof.
  intros. unfold fixedLevelZeroDomainTermAt, RawFixedLevelZeroDomain.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff,
    raw_sat_fixedLevelPiDomainTermAt_iff.
  reflexivity.
Qed.

Definition RawCodedFormulaOccurrence (M : RawPAModel)
    (formulaCode formulaStep bound code : M) : Prop :=
  exists index : M,
    rawLt M index bound /\
    RawCodedAssignmentLookup M formulaCode formulaStep index code.

Arguments RawCodedFormulaOccurrence
  M formulaCode formulaStep bound code : clear implicits.

Definition codedFormulaOccurrenceTermAt
    (formulaCode formulaStep bound code : term) : formula :=
  pEx (pAnd
    (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
    (codedAssignmentLookupTermAt
      (liftTerm 1 formulaCode) (liftTerm 1 formulaStep)
      (tVar 0) (liftTerm 1 code))).

Lemma raw_sat_codedFormulaOccurrenceTermAt_iff : forall
    (M : RawPAModel) e formulaCode formulaStep bound code,
  raw_formula_sat M e
    (codedFormulaOccurrenceTermAt
      formulaCode formulaStep bound code) <->
  RawCodedFormulaOccurrence M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e bound) (raw_term_eval M e code).
Proof.
  intros. unfold codedFormulaOccurrenceTermAt,
    RawCodedFormulaOccurrence.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  split; intros [index [hindex hlookup]]; exists index; split.
  - rewrite raw_term_eval_liftTerm_one_traversal in hindex.
    exact hindex.
  - repeat rewrite raw_term_eval_liftTerm_one_traversal in hlookup.
    exact hlookup.
  - rewrite raw_term_eval_liftTerm_one_traversal.
    exact hindex.
  - repeat rewrite raw_term_eval_liftTerm_one_traversal.
    exact hlookup.
Qed.

Definition RawCodedFormulaZeroOccurrence (M : RawPAModel)
    (formulaCode formulaStep bound code : M) : Prop :=
  RawCodedFormulaOccurrence M formulaCode formulaStep bound code /\
  RawFixedLevelZeroDomain M code.

Arguments RawCodedFormulaZeroOccurrence
  M formulaCode formulaStep bound code : clear implicits.

Definition codedFormulaZeroOccurrenceTermAt
    (formulaCode formulaStep bound code : term) : formula :=
  pAnd
    (codedFormulaOccurrenceTermAt formulaCode formulaStep bound code)
    (fixedLevelZeroDomainTermAt code).

Lemma raw_sat_codedFormulaZeroOccurrenceTermAt_iff : forall
    (M : RawPAModel) e formulaCode formulaStep bound code,
  raw_formula_sat M e
    (codedFormulaZeroOccurrenceTermAt
      formulaCode formulaStep bound code) <->
  RawCodedFormulaZeroOccurrence M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e bound) (raw_term_eval M e code).
Proof.
  intros. unfold codedFormulaZeroOccurrenceTermAt,
    RawCodedFormulaZeroOccurrence.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaOccurrenceTermAt_iff,
    raw_sat_fixedLevelZeroDomainTermAt_iff.
  reflexivity.
Qed.

(** [current] is a numeric code bound.  The beta table is total below it and
    its one-bits are precisely the level-zero formula occurrences. *)
Definition RawFormulaZeroOccurrenceSupportPrefix (M : RawPAModel)
    (current formulaCode formulaStep formulaBound
      supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep current /\
  forall code : M,
    rawLt M code current ->
    (rawFormulaCodeSupported M supportCode supportStep code <->
     RawCodedFormulaZeroOccurrence M
       formulaCode formulaStep formulaBound code).

Arguments RawFormulaZeroOccurrenceSupportPrefix
  M current formulaCode formulaStep formulaBound supportCode supportStep
  : clear implicits.

Definition formulaZeroOccurrenceSupportPrefixTermAt
    (current formulaCode formulaStep formulaBound
      supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt
      supportCode supportStep current)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
        (pAnd
          (pImp
            (formulaCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
            (codedFormulaZeroOccurrenceTermAt
              (liftTerm 1 formulaCode) (liftTerm 1 formulaStep)
              (liftTerm 1 formulaBound) (tVar 0)))
          (pImp
            (codedFormulaZeroOccurrenceTermAt
              (liftTerm 1 formulaCode) (liftTerm 1 formulaStep)
              (liftTerm 1 formulaBound) (tVar 0))
            (formulaCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep)
              (tVar 0)))))).

Lemma raw_sat_formulaZeroOccurrenceSupportPrefixTermAt_iff : forall
    (M : RawPAModel) e current formulaCode formulaStep formulaBound
      supportCode supportStep,
  raw_formula_sat M e
    (formulaZeroOccurrenceSupportPrefixTermAt
      current formulaCode formulaStep formulaBound supportCode supportStep) <->
  RawFormulaZeroOccurrenceSupportPrefix M
    (raw_term_eval M e current)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e formulaBound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold formulaZeroOccurrenceSupportPrefixTermAt,
    RawFormulaZeroOccurrenceSupportPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_formulaCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaZeroOccurrenceTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_one_traversal.
  cbn [raw_term_eval scons]. tauto.
Qed.

Definition RawFormulaZeroOccurrenceSupportPrefixRealizable
    (M : RawPAModel)
    (current formulaCode formulaStep formulaBound : M) : Prop :=
  exists supportCode supportStep : M,
    RawFormulaZeroOccurrenceSupportPrefix M
      current formulaCode formulaStep formulaBound supportCode supportStep.

Arguments RawFormulaZeroOccurrenceSupportPrefixRealizable
  M current formulaCode formulaStep formulaBound : clear implicits.

Definition formulaZeroOccurrenceSupportPrefixRealizableTermAt
    (current formulaCode formulaStep formulaBound : term) : formula :=
  pEx (pEx
    (formulaZeroOccurrenceSupportPrefixTermAt
      (liftTerm 2 current) (liftTerm 2 formulaCode)
      (liftTerm 2 formulaStep) (liftTerm 2 formulaBound)
      (tVar 1) (tVar 0))).

Lemma raw_sat_formulaZeroOccurrenceSupportPrefixRealizableTermAt_iff :
  forall (M : RawPAModel) e current formulaCode formulaStep formulaBound,
  raw_formula_sat M e
    (formulaZeroOccurrenceSupportPrefixRealizableTermAt
      current formulaCode formulaStep formulaBound) <->
  RawFormulaZeroOccurrenceSupportPrefixRealizable M
    (raw_term_eval M e current)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e formulaBound).
Proof.
  intros. unfold formulaZeroOccurrenceSupportPrefixRealizableTermAt,
    RawFormulaZeroOccurrenceSupportPrefixRealizable.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_formulaZeroOccurrenceSupportPrefixTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_two_traversal.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_formulaZeroOccurrenceSupportPrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    formulaCode formulaStep formulaBound,
  RawFormulaZeroOccurrenceSupportPrefix M
    (raw_zero M) formulaCode formulaStep formulaBound
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA formulaCode formulaStep formulaBound.
  split.
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros code hcode. exfalso.
    exact (raw_not_lt_zero M hPA code hcode).
Qed.

(** One beta append installs the characteristic value at [current].  For
    old coordinates, the reverse implication uses totality of the old table
    plus functionality of lookup: preservation gives the old value in the
    new table, so a new one-bit forces that old value itself to be one. *)
Lemma raw_formulaZeroOccurrenceSupportPrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    current formulaCode formulaStep formulaBound
      oldSupportCode oldSupportStep,
  RawFormulaZeroOccurrenceSupportPrefix M
    current formulaCode formulaStep formulaBound
    oldSupportCode oldSupportStep ->
  exists newSupportCode newSupportStep : M,
    RawFormulaZeroOccurrenceSupportPrefix M
      (raw_succ M current) formulaCode formulaStep formulaBound
      newSupportCode newSupportStep.
Proof.
  intros M hPA current formulaCode formulaStep formulaBound
    oldSupportCode oldSupportStep [holdDefined holdExact].
  destruct (classic (RawCodedFormulaZeroOccurrence M
    formulaCode formulaStep formulaBound current))
    as [hcurrentOccurrence | hcurrentNotOccurrence].
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (rawNumeralValue M 1)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); [exact hpreserved |].
          exact hnewSupported.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawFormulaCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hoccurrence.
        unfold rawFormulaCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hoccurrence)).
    + split.
      * intros hnewSupported. exact hcurrentOccurrence.
      * intros hoccurrence.
        unfold rawFormulaCodeSupported. exact hnewValue.
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (raw_zero M)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); [exact hpreserved |].
          exact hnewSupported.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawFormulaCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hoccurrence.
        unfold rawFormulaCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hoccurrence)).
    + split.
      * intro hnewSupported. exfalso.
        apply (raw_zero_neq_truthOne M hPA).
        symmetry.
        exact (raw_codedAssignmentLookup_functional M hPA
          newSupportCode newSupportStep current
          (rawNumeralValue M 1) (raw_zero M)
          hnewSupported hnewValue).
      * intro hoccurrence. exfalso.
        exact (hcurrentNotOccurrence hoccurrence).
Qed.

(** PA's definable induction, rather than Rocq recursion, iterates the beta
    append across an arbitrary carrier element. *)
Theorem raw_formulaZeroOccurrenceSupportPrefix_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    formulaCode formulaStep formulaBound current,
  RawFormulaZeroOccurrenceSupportPrefixRealizable M
    current formulaCode formulaStep formulaBound.
Proof.
  intros M hPA formulaCode formulaStep formulaBound.
  set (parameterEnv := scons M formulaCode
    (scons M formulaStep
      (scons M formulaBound (fun _ : nat => raw_zero M)))).
  set (phi := formulaZeroOccurrenceSupportPrefixRealizableTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_formulaZeroOccurrenceSupportPrefixRealizableTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exists (raw_zero M), (raw_zero M).
      exact (raw_formulaZeroOccurrenceSupportPrefix_zero M hPA
        formulaCode formulaStep formulaBound).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_formulaZeroOccurrenceSupportPrefixRealizableTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_formulaZeroOccurrenceSupportPrefixRealizableTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      destruct hcurrent as [oldSupportCode [oldSupportStep hold]].
      exact (raw_formulaZeroOccurrenceSupportPrefix_succ M hPA
        current formulaCode formulaStep formulaBound
        oldSupportCode oldSupportStep hold).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_formulaZeroOccurrenceSupportPrefixRealizableTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** ------------------------------------------------------------------
    Level zero is genuinely quantifier-free. *)

Lemma raw_truthOne_not_le_zero : forall (M : RawPAModel),
  RawPASatisfies M ->
  ~ rawLe M (rawNumeralValue M 1) (raw_zero M).
Proof.
  intros M hPA honeZero.
  pose proof (raw_proof_zero_le M hPA (rawNumeralValue M 1))
    as hzeroOne.
  pose proof (raw_le_antisymm M hPA
    (rawNumeralValue M 1) (raw_zero M) honeZero hzeroOne) as heq.
  apply (raw_zero_neq_truthOne M hPA). symmetry. exact heq.
Qed.

Lemma raw_succ_not_le_zero : forall (M : RawPAModel),
  RawPASatisfies M -> forall value,
  ~ rawLe M (raw_succ M value) (raw_zero M).
Proof.
  intros M hPA value hsuccZero.
  apply (raw_truthOne_not_le_zero M hPA).
  exact (raw_le_trans M hPA
    (rawNumeralValue M 1) (raw_succ M value) (raw_zero M)
    (raw_rank_one_le_succ M hPA value) hsuccZero).
Qed.

Lemma raw_max_one_not_le_zero : forall (M : RawPAModel),
  RawPASatisfies M -> forall base other,
  RawMax M base (rawNumeralValue M 1) other ->
  ~ rawLe M base (raw_zero M).
Proof.
  intros M hPA base other hmax hbaseZero.
  apply (raw_truthOne_not_le_zero M hPA).
  exact (raw_le_trans M hPA
    (rawNumeralValue M 1) base (raw_zero M)
    (raw_fixedLevel_max_left_le M hPA
      base (rawNumeralValue M 1) other hmax)
    hbaseZero).
Qed.

Lemma raw_fixedLevelZeroDomain_all_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  ~ RawFixedLevelZeroDomain M (rawFormulaAllCode M child).
Proof.
  intros M hPA child [hsigma | hpi].
  - destruct hsigma as (sigma & pi & hrank & hsigmaZero).
    destruct (raw_codedFormulaRank_all_view M hPA
      child sigma pi hrank) as
      (childSigma & childPi & hchildRank &
       base & hmax & hpiEq & hsigmaEq).
    subst sigma. change (rawLe M (raw_succ M base) (raw_zero M))
      in hsigmaZero.
    exact (raw_succ_not_le_zero M hPA base hsigmaZero).
  - destruct hpi as (sigma & pi & hrank & hpiZero).
    destruct (raw_codedFormulaRank_all_view M hPA
      child sigma pi hrank) as
      (childSigma & childPi & hchildRank &
       base & hmax & hpiEq & hsigmaEq).
    subst pi. change (rawLe M base (raw_zero M)) in hpiZero.
    exact (raw_max_one_not_le_zero M hPA base childPi hmax hpiZero).
Qed.

Lemma raw_fixedLevelZeroDomain_ex_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall child,
  ~ RawFixedLevelZeroDomain M (rawFormulaExCode M child).
Proof.
  intros M hPA child [hsigma | hpi].
  - destruct hsigma as (sigma & pi & hrank & hsigmaZero).
    destruct (raw_codedFormulaRank_ex_view M hPA
      child sigma pi hrank) as
      (childSigma & childPi & hchildRank &
       base & hmax & hsigmaEq & hpiEq).
    subst sigma. change (rawLe M base (raw_zero M)) in hsigmaZero.
    exact (raw_max_one_not_le_zero M hPA base childSigma hmax hsigmaZero).
  - destruct hpi as (sigma & pi & hrank & hpiZero).
    destruct (raw_codedFormulaRank_ex_view M hPA
      child sigma pi hrank) as
      (childSigma & childPi & hchildRank &
       base & hmax & hsigmaEq & hpiEq).
    subst pi. change (rawLe M (raw_succ M base) (raw_zero M))
      in hpiZero.
    exact (raw_succ_not_le_zero M hPA base hpiZero).
Qed.

Lemma raw_fixedLevelZeroDomain_imp_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawFixedLevelZeroDomain M (rawFormulaImpCode M left right) ->
  RawFixedLevelZeroDomain M left /\
  RawFixedLevelZeroDomain M right.
Proof.
  intros M hPA left right [hsigma | hpi].
  - destruct (raw_fixedLevelSigmaDomain_imp M hPA 0 left right hsigma)
      as [hleft hright]. split; [right | left]; assumption.
  - destruct (raw_fixedLevelPiDomain_imp M hPA 0 left right hpi)
      as [hleft hright]. split; [left | right]; assumption.
Qed.

Lemma raw_fixedLevelZeroDomain_and_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawFixedLevelZeroDomain M (rawFormulaAndCode M left right) ->
  RawFixedLevelZeroDomain M left /\
  RawFixedLevelZeroDomain M right.
Proof.
  intros M hPA left right [hsigma | hpi].
  - destruct (raw_fixedLevelSigmaDomain_and M hPA 0 left right hsigma)
      as [hleft hright]. split; left; assumption.
  - destruct (raw_fixedLevelPiDomain_and M hPA 0 left right hpi)
      as [hleft hright]. split; right; assumption.
Qed.

Lemma raw_fixedLevelZeroDomain_or_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall left right,
  RawFixedLevelZeroDomain M (rawFormulaOrCode M left right) ->
  RawFixedLevelZeroDomain M left /\
  RawFixedLevelZeroDomain M right.
Proof.
  intros M hPA left right [hsigma | hpi].
  - destruct (raw_fixedLevelSigmaDomain_or M hPA 0 left right hsigma)
      as [hleft hright]. split; left; assumption.
  - destruct (raw_fixedLevelPiDomain_or M hPA 0 left right hpi)
      as [hleft hright]. split; right; assumption.
Qed.

(** These code inequalities are just the generic fact that every field of a
    polynomial list code lies below the enclosing list code. *)
Lemma raw_formulaCodeList3_left_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M left (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_formulaCodeList3_right_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag left right,
  rawLt M right (rawCodeList3 M tag left right).
Proof.
  intros M hPA tag left right. unfold rawCodeList3.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** ------------------------------------------------------------------
    Conversion of full admissibility to rank-zero syntax realizability. *)

Theorem raw_formulaSyntaxTraversal_rankZeroSyntaxRealizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    formulaCode formulaStep formulaBound rootIndex root
    assignmentCode assignmentStep,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep formulaBound rootIndex root ->
  RawCodedFormulaAtomicTermAdequate M
    formulaCode formulaStep formulaBound ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep root ->
  RawFixedLevelZeroDomain M root ->
  RawRankZeroSyntaxRealizable M root assignmentCode assignmentStep.
Proof.
  intros M hPA formulaCode formulaStep formulaBound rootIndex root
    assignmentCode assignmentStep hsyntax hatomic hassignment hrootDomain.
  destruct hsyntax as
    [hformulaDefined [hrootIndex [hrootLookup hsyntaxRows]]].
  destruct (raw_formulaZeroOccurrenceSupportPrefix_exists M hPA
    formulaCode formulaStep formulaBound (raw_succ M root)) as
    (supportCode & supportStep & hsupportPrefix).
  destruct hsupportPrefix as [hsupportDefined hsupportExact].
  exists supportCode, supportStep.
  split.
  - split; [exact hsupportDefined |].
    intros code hcodeBound hsupported.
    pose proof (proj1 (hsupportExact code hcodeBound) hsupported)
      as hzeroOccurrence.
    destruct hzeroOccurrence as
      [[index [hindex hlookup]] hcodeDomain].
    pose proof (hsyntaxRows index code hindex hlookup) as hrow.
    destruct hrow as
      [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + destruct heq as [left [right heq]].
      exists left, right. left. exact heq.
    + exists (raw_zero M), (raw_zero M). right. left. exact hbot.
    + destruct himp as
        (leftIndex & left & rightIndex & right &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
      assert (hleftCode : rawLt M left code).
      {
        rewrite hcode. unfold rawFormulaImpCode.
        apply raw_formulaCodeList3_left_lt. exact hPA.
      }
      assert (hrightCode : rawLt M right code).
      {
        rewrite hcode. unfold rawFormulaImpCode.
        apply raw_formulaCodeList3_right_lt. exact hPA.
      }
      destruct (raw_fixedLevelZeroDomain_imp_children M hPA
        left right) as [hleftDomain hrightDomain]; [now rewrite <- hcode |].
      assert (hleftBound : rawLt M left (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA left code
          (raw_succ M root) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M right (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA right code
          (raw_succ M root) hrightCode hcodeBound).
      }
      assert (hleftSupported : rawFormulaCodeSupported M
          supportCode supportStep left).
      {
        apply (proj2 (hsupportExact left hleftBound)).
        split.
        - exists leftIndex. split.
          + exact (raw_assignment_lt_trans M hPA leftIndex index
              formulaBound hleftIndex hindex).
          + exact hleftLookup.
        - exact hleftDomain.
      }
      assert (hrightSupported : rawFormulaCodeSupported M
          supportCode supportStep right).
      {
        apply (proj2 (hsupportExact right hrightBound)).
        split.
        - exists rightIndex. split.
          + exact (raw_assignment_lt_trans M hPA rightIndex index
              formulaBound hrightIndex hindex).
          + exact hrightLookup.
        - exact hrightDomain.
      }
      exists left, right. right. right. left.
      repeat split; assumption.
    + destruct hand as
        (leftIndex & left & rightIndex & right &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
      assert (hleftCode : rawLt M left code).
      {
        rewrite hcode. unfold rawFormulaAndCode.
        apply raw_formulaCodeList3_left_lt. exact hPA.
      }
      assert (hrightCode : rawLt M right code).
      {
        rewrite hcode. unfold rawFormulaAndCode.
        apply raw_formulaCodeList3_right_lt. exact hPA.
      }
      destruct (raw_fixedLevelZeroDomain_and_children M hPA
        left right) as [hleftDomain hrightDomain]; [now rewrite <- hcode |].
      assert (hleftBound : rawLt M left (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA left code
          (raw_succ M root) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M right (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA right code
          (raw_succ M root) hrightCode hcodeBound).
      }
      assert (hleftSupported : rawFormulaCodeSupported M
          supportCode supportStep left).
      {
        apply (proj2 (hsupportExact left hleftBound)).
        split.
        - exists leftIndex. split.
          + exact (raw_assignment_lt_trans M hPA leftIndex index
              formulaBound hleftIndex hindex).
          + exact hleftLookup.
        - exact hleftDomain.
      }
      assert (hrightSupported : rawFormulaCodeSupported M
          supportCode supportStep right).
      {
        apply (proj2 (hsupportExact right hrightBound)).
        split.
        - exists rightIndex. split.
          + exact (raw_assignment_lt_trans M hPA rightIndex index
              formulaBound hrightIndex hindex).
          + exact hrightLookup.
        - exact hrightDomain.
      }
      exists left, right. right. right. right. left.
      repeat split; assumption.
    + destruct hor as
        (leftIndex & left & rightIndex & right &
         hleftIndex & hleftLookup & hrightIndex & hrightLookup & hcode).
      assert (hleftCode : rawLt M left code).
      {
        rewrite hcode. unfold rawFormulaOrCode.
        apply raw_formulaCodeList3_left_lt. exact hPA.
      }
      assert (hrightCode : rawLt M right code).
      {
        rewrite hcode. unfold rawFormulaOrCode.
        apply raw_formulaCodeList3_right_lt. exact hPA.
      }
      destruct (raw_fixedLevelZeroDomain_or_children M hPA
        left right) as [hleftDomain hrightDomain]; [now rewrite <- hcode |].
      assert (hleftBound : rawLt M left (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA left code
          (raw_succ M root) hleftCode hcodeBound).
      }
      assert (hrightBound : rawLt M right (raw_succ M root)).
      {
        exact (raw_assignment_lt_trans M hPA right code
          (raw_succ M root) hrightCode hcodeBound).
      }
      assert (hleftSupported : rawFormulaCodeSupported M
          supportCode supportStep left).
      {
        apply (proj2 (hsupportExact left hleftBound)).
        split.
        - exists leftIndex. split.
          + exact (raw_assignment_lt_trans M hPA leftIndex index
              formulaBound hleftIndex hindex).
          + exact hleftLookup.
        - exact hleftDomain.
      }
      assert (hrightSupported : rawFormulaCodeSupported M
          supportCode supportStep right).
      {
        apply (proj2 (hsupportExact right hrightBound)).
        split.
        - exists rightIndex. split.
          + exact (raw_assignment_lt_trans M hPA rightIndex index
              formulaBound hrightIndex hindex).
          + exact hrightLookup.
        - exact hrightDomain.
      }
      exists left, right. right. right. right. right.
      repeat split; assumption.
    + destruct hall as [childIndex [child [hchildIndex [hchildLookup hcode]]]].
      exfalso. apply (raw_fixedLevelZeroDomain_all_false M hPA child).
      now rewrite <- hcode.
    + destruct hex as [childIndex [child [hchildIndex [hchildLookup hcode]]]].
      exfalso. apply (raw_fixedLevelZeroDomain_ex_false M hPA child).
      now rewrite <- hcode.
  - split.
    + intros code hcodeBound hsupported left right heq.
      pose proof (proj1 (hsupportExact code hcodeBound) hsupported)
        as [[index [hindex hlookup]] hcodeDomain].
      assert (hassignmentCode : RawCodedAssignmentDefinedThrough M
          assignmentCode assignmentStep code).
      {
        destruct (raw_lt_succ_cases M hPA code root hcodeBound)
          as [hcodeRoot | ->].
        - intros assignmentIndex hassignmentIndex.
          apply hassignment.
          exact (raw_assignment_lt_trans M hPA
            assignmentIndex code root hassignmentIndex hcodeRoot).
        - exact hassignment.
      }
      exact (hatomic index code left right assignmentCode assignmentStep
        hindex hlookup heq hassignmentCode).
    + apply (proj2 (hsupportExact root
        (raw_assignment_lt_self_succ M hPA root))).
      split.
      * exists rootIndex. split; assumption.
      * exact hrootDomain.
Qed.

Corollary raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M 0
    root assignmentCode assignmentStep ->
  RawRankZeroSyntaxRealizable M root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep
    [(formulaCode & formulaStep & formulaBound & rootIndex &
      hsyntax & hatomic) [hassignment hdomain]].
  exact (raw_formulaSyntaxTraversal_rankZeroSyntaxRealizable M hPA
    formulaCode formulaStep formulaBound rootIndex root
    assignmentCode assignmentStep hsyntax hatomic hassignment hdomain).
Qed.

(** A parent's rank-zero tables may be reused at any supported strict child.
    Restricting the traversal is legitimate because [child < root] implies
    [S child <= root], entirely inside the raw PA order. *)
Lemma raw_rankZeroTruthTraversal_restrict_child : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root child assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep,
  RawRankZeroTruthTraversal M (raw_succ M root)
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  rawLt M child root ->
  RawRankZeroTruthTraversal M (raw_succ M child)
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep.
Proof.
  intros M hPA root child assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep
    [hsupport [htruth hrows]] hchild.
  assert (hintoRoot : forall index,
      rawLt M index (raw_succ M child) -> rawLt M index (raw_succ M root)).
  {
    intros index hindex.
    assert (hindexRoot : rawLt M index root).
    {
      exact (raw_lt_le_trans_pair M hPA
        index (raw_succ M child) root hindex
        (raw_succ_le_of_lt_pair M hPA child root hchild)).
    }
    exact (raw_assignment_lt_trans M hPA index root
      (raw_succ M root) hindexRoot
      (raw_assignment_lt_self_succ M hPA root)).
  }
  split.
  - intros index hindex. exact (hsupport index (hintoRoot index hindex)).
  - split.
    + intros index hindex. exact (htruth index (hintoRoot index hindex)).
    + intros code hcode hsupported.
      exact (hrows code (hintoRoot code hcode) hsupported).
Qed.

Lemma raw_rankZeroTruthCertificate_child_with_tables : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root rootOutput assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep,
  RawRankZeroTruthCertificateWithTables M
    root rootOutput assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep ->
  forall child childOutput,
    rawLt M child root ->
    rawFormulaCodeSupported M supportCode supportStep child ->
    RawCodedAssignmentLookup M truthCode truthStep child childOutput ->
    RawTruthBit M childOutput ->
    RawRankZeroTruthCertificate M
      child childOutput assignmentCode assignmentStep.
Proof.
  intros M hPA root rootOutput assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep
    [htraversal [hrootSupport [hrootLookup hrootBit]]]
    child childOutput hchild hchildSupport hchildLookup hchildBit.
  exists supportCode, supportStep, truthCode, truthStep.
  split.
  - exact (raw_rankZeroTruthTraversal_restrict_child M hPA
      root child assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep htraversal hchild).
  - split; [exact hchildSupport |].
    split; assumption.
Qed.

Lemma raw_rankZeroTruthCertificateWithTables_root_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep,
  RawRankZeroTruthCertificateWithTables M
    root output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep ->
  RawRankZeroTruthClosedStep M
    root output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep.
Proof.
  intros M hPA root output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep
    [[hsupportDefined [htruthDefined hrows]]
     [hrootSupport [hrootLookup hrootBit]]].
  destruct (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupport) as [canonical [hcanonicalLookup hstep]].
  assert (houtput : output = canonical).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      truthCode truthStep root output canonical
      hrootLookup hcanonicalLookup).
  }
  now rewrite <- houtput in hstep.
Qed.

(** Constructor views for a closed rank-zero step.  The local evaluator is
    a disjunction of five shapes; list-length separation and numeral-tag
    injectivity eliminate the four impossible alternatives. *)
Lemma raw_rankZeroTruthClosedStep_imp_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left right,
  code = rawFormulaImpCode M left right ->
  RawRankZeroTruthClosedStep M
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  exists leftOutput rightOutput : M,
    RawCodedAssignmentLookup M truthCode truthStep left leftOutput /\
    RawCodedAssignmentLookup M truthCode truthStep right rightOutput /\
    RawImpTruth M output leftOutput rightOutput /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code.
Proof.
  intros M hPA code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right hcode
    (actualLeft & actualLeftOutput & actualRight & actualRightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 2 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hbot as [hactual _]. exfalso.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 2) left right).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as
      [[hactual [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleftLt hrightLt]]]].
    assert (hcodes : rawFormulaImpCode M actualLeft actualRight =
        rawFormulaImpCode M left right).
    { exact (eq_trans (eq_sym hactual) hcode). }
    unfold rawFormulaImpCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleft hright]].
    subst actualLeft. subst actualRight.
    exists actualLeftOutput, actualRightOutput.
    split; [exact hleftLookup |].
    split; [exact hrightLookup |].
    split; [exact htruth |].
    split; [exact hleftSupport |].
    split; [exact hrightSupport |].
    split; assumption.
  - destruct hand as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 2 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hor as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 2 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
Qed.

Lemma raw_rankZeroTruthClosedStep_and_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left right,
  code = rawFormulaAndCode M left right ->
  RawRankZeroTruthClosedStep M
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  exists leftOutput rightOutput : M,
    RawCodedAssignmentLookup M truthCode truthStep left leftOutput /\
    RawCodedAssignmentLookup M truthCode truthStep right rightOutput /\
    RawAndTruth M output leftOutput rightOutput /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code.
Proof.
  intros M hPA code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right hcode
    (actualLeft & actualLeftOutput & actualRight & actualRightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 3 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hbot as [hactual _]. exfalso.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 3) left right).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 3 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hand as
      [[hactual [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleftLt hrightLt]]]].
    assert (hcodes : rawFormulaAndCode M actualLeft actualRight =
        rawFormulaAndCode M left right).
    { exact (eq_trans (eq_sym hactual) hcode). }
    unfold rawFormulaAndCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleft hright]].
    subst actualLeft. subst actualRight.
    exists actualLeftOutput, actualRightOutput.
    split; [exact hleftLookup |].
    split; [exact hrightLookup |].
    split; [exact htruth |].
    split; [exact hleftSupport |].
    split; [exact hrightSupport |].
    split; assumption.
  - destruct hor as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      4 3 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
Qed.

Lemma raw_rankZeroTruthClosedStep_or_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep left right,
  code = rawFormulaOrCode M left right ->
  RawRankZeroTruthClosedStep M
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  exists leftOutput rightOutput : M,
    RawCodedAssignmentLookup M truthCode truthStep left leftOutput /\
    RawCodedAssignmentLookup M truthCode truthStep right rightOutput /\
    RawOrTruth M output leftOutput rightOutput /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code.
Proof.
  intros M hPA code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep left right hcode
    (actualLeft & actualLeftOutput & actualRight & actualRightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      0 4 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hbot as [hactual _]. exfalso.
    apply (raw_codeList1_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 4) left right).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      2 4 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hand as [[hactual _] _]. exfalso.
    pose proof (raw_codeList3_numeral_tags_eq M hPA
      3 4 actualLeft actualRight left right
      (eq_trans (eq_sym hactual) hcode)). discriminate.
  - destruct hor as
      [[hactual [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleftLt hrightLt]]]].
    assert (hcodes : rawFormulaOrCode M actualLeft actualRight =
        rawFormulaOrCode M left right).
    { exact (eq_trans (eq_sym hactual) hcode). }
    unfold rawFormulaOrCode in hcodes.
    destruct (raw_codeList3_injective M (rawListNode_injective M hPA)
      _ _ _ _ _ _ hcodes) as [_ [hleft hright]].
    subst actualLeft. subst actualRight.
    exists actualLeftOutput, actualRightOutput.
    split; [exact hleftLookup |].
    split; [exact hrightLookup |].
    split; [exact htruth |].
    split; [exact hleftSupport |].
    split; [exact hrightSupport |].
    split; assumption.
Qed.

Lemma raw_rankZeroTruthClosedStep_all_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep child,
  code = rawFormulaAllCode M child ->
  RawRankZeroTruthClosedStep M
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep -> False.
Proof.
  intros M hPA code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep child hcode
    (left & leftOutput & right & rightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) child
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hbot as [hactual _].
    apply (raw_codeList1_neq_codeList2 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 5) child).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) child
      (rawNumeralValue M 2) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hand as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) child
      (rawNumeralValue M 3) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hor as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 5) child
      (rawNumeralValue M 4) left right).
    exact (eq_trans (eq_sym hcode) hactual).
Qed.

Lemma raw_rankZeroTruthClosedStep_ex_false : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    code output assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep child,
  code = rawFormulaExCode M child ->
  RawRankZeroTruthClosedStep M
    code output assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep -> False.
Proof.
  intros M hPA code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep child hcode
    (left & leftOutput & right & rightOutput & hrow).
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [hactual _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) child
      (rawNumeralValue M 0) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hbot as [hactual _].
    apply (raw_codeList1_neq_codeList2 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 1) (rawNumeralValue M 6) child).
    exact (eq_trans (eq_sym hactual) hcode).
  - destruct himp as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) child
      (rawNumeralValue M 2) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hand as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) child
      (rawNumeralValue M 3) left right).
    exact (eq_trans (eq_sym hcode) hactual).
  - destruct hor as [[hactual _] _].
    apply (raw_codeList2_neq_codeList3 M hPA
      (rawListNode_injective M hPA)
      (rawNumeralValue M 6) child
      (rawNumeralValue M 4) left right).
    exact (eq_trans (eq_sym hcode) hactual).
Qed.

(** Small projections of the Boolean truth tables.  Functionality lets us
    compare the certified output with the visibly correct bit, avoiding a
    repetitive case split over zero and one. *)
Lemma raw_impTruth_output_one_of_left_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawImpTruth M output left right ->
  left = raw_zero M -> output = rawNumeralValue M 1.
Proof.
  intros M hPA output left right
    htruth hleft.
  apply (raw_impTruth_functional M hPA left right
    output (rawNumeralValue M 1)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [right; reflexivity |].
  right. split; [left; exact hleft | reflexivity].
Qed.

Lemma raw_impTruth_output_one_of_right_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawImpTruth M output left right ->
  right = rawNumeralValue M 1 -> output = rawNumeralValue M 1.
Proof.
  intros M hPA output left right htruth hright.
  apply (raw_impTruth_functional M hPA left right
    output (rawNumeralValue M 1)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [right; reflexivity |].
  right. split; [right; exact hright | reflexivity].
Qed.

Lemma raw_impTruth_output_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawImpTruth M output left right ->
  left = rawNumeralValue M 1 -> right = raw_zero M ->
  output = raw_zero M.
Proof.
  intros M hPA output left right htruth hleft hright.
  apply (raw_impTruth_functional M hPA left right
    output (raw_zero M)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [left; reflexivity |].
  left. split; [split; assumption | reflexivity].
Qed.

Lemma raw_andTruth_output_one : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawAndTruth M output left right ->
  left = rawNumeralValue M 1 -> right = rawNumeralValue M 1 ->
  output = rawNumeralValue M 1.
Proof.
  intros M hPA output left right htruth hleft hright.
  apply (raw_andTruth_functional M hPA left right
    output (rawNumeralValue M 1)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [right; reflexivity |].
  left. split; [split; assumption | reflexivity].
Qed.

Lemma raw_andTruth_output_zero_of_left : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawAndTruth M output left right ->
  left = raw_zero M -> output = raw_zero M.
Proof.
  intros M hPA output left right htruth hleft.
  apply (raw_andTruth_functional M hPA left right
    output (raw_zero M)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [left; reflexivity |].
  right. split; [left; exact hleft | reflexivity].
Qed.

Lemma raw_andTruth_output_zero_of_right : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawAndTruth M output left right ->
  right = raw_zero M -> output = raw_zero M.
Proof.
  intros M hPA output left right htruth hright.
  apply (raw_andTruth_functional M hPA left right
    output (raw_zero M)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [left; reflexivity |].
  right. split; [right; exact hright | reflexivity].
Qed.

Lemma raw_orTruth_output_one_of_left : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawOrTruth M output left right ->
  left = rawNumeralValue M 1 -> output = rawNumeralValue M 1.
Proof.
  intros M hPA output left right htruth hleft.
  apply (raw_orTruth_functional M hPA left right
    output (rawNumeralValue M 1)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [right; reflexivity |].
  left. split; [left; exact hleft | reflexivity].
Qed.

Lemma raw_orTruth_output_one_of_right : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawOrTruth M output left right ->
  right = rawNumeralValue M 1 -> output = rawNumeralValue M 1.
Proof.
  intros M hPA output left right htruth hright.
  apply (raw_orTruth_functional M hPA left right
    output (rawNumeralValue M 1)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [right; reflexivity |].
  left. split; [right; exact hright | reflexivity].
Qed.

Lemma raw_orTruth_output_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall output left right,
  RawOrTruth M output left right ->
  left = raw_zero M -> right = raw_zero M -> output = raw_zero M.
Proof.
  intros M hPA output left right htruth hleft hright.
  apply (raw_orTruth_functional M hPA left right
    output (raw_zero M)); [exact htruth |].
  destruct htruth as [hleftBit [hrightBit [houtputBit hcases]]].
  split; [exact hleftBit |]. split; [exact hrightBit |].
  split; [left; reflexivity |].
  right. split; [split; assumption | reflexivity].
Qed.

(** ------------------------------------------------------------------
    Prefix agreement between a level-one schedule and rank-zero truth. *)

Definition RawFixedLevelOneRankZeroAgreementBelow (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep current : M) : Prop :=
  forall index mode code assignmentCode assignmentStep output : M,
    rawLt M index current ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawRankZeroTruthCertificate M
      code output assignmentCode assignmentStep ->
    (mode = rawFixedLevelSigmaMode M ->
      output = rawNumeralValue M 1) /\
    (mode = rawFixedLevelPiMode M -> output = raw_zero M).

Arguments RawFixedLevelOneRankZeroAgreementBelow
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode
    assignmentStepStep current : clear implicits.

Definition fixedLevelOneRankZeroAgreementBelowTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep current : term) : formula :=
  fixedTruthTotalityAll6
    (pImp
      (Formula.ltTermAt (tVar 5) (liftTerm 6 current))
      (pImp
        (fixedLevelStateLookupTermAt
          (liftTerm 6 modeCode) (liftTerm 6 modeStep)
          (liftTerm 6 formulaCode) (liftTerm 6 formulaStep)
          (liftTerm 6 assignmentCodeCode)
          (liftTerm 6 assignmentCodeStep)
          (liftTerm 6 assignmentStepCode)
          (liftTerm 6 assignmentStepStep)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1))
        (pImp
          (rankZeroTruthCertificateTermAt
            (tVar 3) (tVar 0) (tVar 2) (tVar 1))
          (pAnd
            (pImp (pEq (tVar 4) tZero)
              (pEq (tVar 0) (Term.numeral 1)))
            (pImp (pEq (tVar 4) (Term.numeral 1))
              (pEq (tVar 0) tZero)))))).

Lemma raw_sat_fixedLevelOneRankZeroAgreementBelowTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep current,
  raw_formula_sat M e
    (fixedLevelOneRankZeroAgreementBelowTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep current) <->
  RawFixedLevelOneRankZeroAgreementBelow M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e current).
Proof.
  intros. unfold fixedLevelOneRankZeroAgreementBelowTermAt,
    fixedTruthTotalityAll6, RawFixedLevelOneRankZeroAgreementBelow,
    rawFixedLevelSigmaMode, rawFixedLevelPiMode.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite raw_sat_rankZeroTruthCertificateTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTotality_eval_liftTerm_six.
  cbn [raw_term_eval scons].
  repeat rewrite raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_fixedLevelOneRankZeroAgreementBelow_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep,
  RawFixedLevelOneRankZeroAgreementBelow M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep (raw_zero M).
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep output hindex.
  exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Lemma raw_fixedLevelOneRankZeroAgreementBelow_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep current,
  RawFixedLevelSuccessorTruthTraversal M 0
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep ->
  rawLt M current bound ->
  RawFixedLevelOneRankZeroAgreementBelow M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep current ->
  RawFixedLevelOneRankZeroAgreementBelow M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep (raw_succ M current).
Proof.
  intros M hPA lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep current
    htraversal hcurrentBound hagree
    index mode code assignmentCode assignmentStep output
    hindex hlookup hcertificate.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbefore | ->].
  - exact (hagree index mode code assignmentCode assignmentStep output
      hbefore hlookup hcertificate).
  - pose proof hcertificate as hcertificatePublic.
    destruct hcertificate as
      (supportCode & supportStep & truthCode & truthStep & hwithTables).
    pose proof hwithTables as hwithTablesCopy.
    pose proof (raw_rankZeroTruthCertificateWithTables_root_closed_step
      M hPA code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep hwithTables)
      as hrankZeroClosed.
    destruct htraversal as
      [hmodeDefined [hformulaDefined
       [hassignmentCodeDefined [hassignmentStepDefined
        [hrootIndex [hrootLookup hrows]]]]]].
    pose proof (hrows current mode code assignmentCode assignmentStep
      hcurrentBound hlookup) as hclosed.
    destruct hclosed as
      [[hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
          newAssignmentCode & newAssignmentStep & spare & hsigma)] |
       [hmode (leftIndex & leftCode & rightIndex & rightCode & witness &
          newAssignmentCode & newAssignmentStep & spare & hpi)]].
    + destruct hsigma as [hsigmaDomain hsigmaCase].
      split.
      * intros hmodeSigma.
        destruct hsigmaCase as
          [hrankZeroOne |
           [himpLeft | [himpRight | [hand | [hor | [hex | hall]]]]]].
        -- exact (raw_rankZeroTruthCertificate_output_functional M hPA
             code assignmentCode assignmentStep output
             (rawNumeralValue M 1)
             hcertificatePublic hrankZeroOne).
        -- destruct himpLeft as
             [hcode [[hleftEarlier hleftState] hspare]].
           destruct (raw_rankZeroTruthClosedStep_imp_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & himpTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           assert (hleftCertificate : RawRankZeroTruthCertificate M
               leftCode leftOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy leftCode leftOutput hleftCodeLt
               hleftSupport hleftTruthLookup (proj1 himpTruth)).
           }
           pose proof (hagree leftIndex (rawFixedLevelPiMode M)
             leftCode assignmentCode assignmentStep leftOutput
             hleftEarlier hleftState hleftCertificate) as [_ hleftFalse].
           exact (raw_impTruth_output_one_of_left_zero M hPA
             output leftOutput rightOutput himpTruth
             (hleftFalse eq_refl)).
        -- destruct himpRight as
             [hcode [[hrightEarlier hrightState] hspare]].
           destruct (raw_rankZeroTruthClosedStep_imp_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & himpTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           assert (hrightCertificate : RawRankZeroTruthCertificate M
               rightCode rightOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy rightCode rightOutput hrightCodeLt
               hrightSupport hrightTruthLookup
               (proj1 (proj2 himpTruth))).
           }
           pose proof (hagree rightIndex (rawFixedLevelSigmaMode M)
             rightCode assignmentCode assignmentStep rightOutput
             hrightEarlier hrightState hrightCertificate) as [hrightTrue _].
           exact (raw_impTruth_output_one_of_right_one M hPA
             output leftOutput rightOutput himpTruth
             (hrightTrue eq_refl)).
        -- destruct hand as
             [hcode [[hleftEarlier hleftState]
                     [hrightEarlier hrightState]]].
           destruct (raw_rankZeroTruthClosedStep_and_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & handTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           assert (hleftCertificate : RawRankZeroTruthCertificate M
               leftCode leftOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy leftCode leftOutput hleftCodeLt
               hleftSupport hleftTruthLookup (proj1 handTruth)).
           }
           assert (hrightCertificate : RawRankZeroTruthCertificate M
               rightCode rightOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy rightCode rightOutput hrightCodeLt
               hrightSupport hrightTruthLookup
               (proj1 (proj2 handTruth))).
           }
           pose proof (hagree leftIndex (rawFixedLevelSigmaMode M)
             leftCode assignmentCode assignmentStep leftOutput
             hleftEarlier hleftState hleftCertificate) as [hleftTrue _].
           pose proof (hagree rightIndex (rawFixedLevelSigmaMode M)
             rightCode assignmentCode assignmentStep rightOutput
             hrightEarlier hrightState hrightCertificate) as [hrightTrue _].
           exact (raw_andTruth_output_one M hPA
             output leftOutput rightOutput handTruth
             (hleftTrue eq_refl) (hrightTrue eq_refl)).
        -- destruct hor as [hcode hchosen].
           destruct (raw_rankZeroTruthClosedStep_or_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & horTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           destruct hchosen as
             [[hleftEarlier hleftState] | [hrightEarlier hrightState]].
           ++ assert (hleftCertificate : RawRankZeroTruthCertificate M
                  leftCode leftOutput assignmentCode assignmentStep).
              {
                exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
                  code output assignmentCode assignmentStep
                  truthCode truthStep supportCode supportStep
                  hwithTablesCopy leftCode leftOutput hleftCodeLt
                  hleftSupport hleftTruthLookup (proj1 horTruth)).
              }
              pose proof (hagree leftIndex (rawFixedLevelSigmaMode M)
                leftCode assignmentCode assignmentStep leftOutput
                hleftEarlier hleftState hleftCertificate) as [hleftTrue _].
              exact (raw_orTruth_output_one_of_left M hPA
                output leftOutput rightOutput horTruth
                (hleftTrue eq_refl)).
           ++ assert (hrightCertificate : RawRankZeroTruthCertificate M
                  rightCode rightOutput assignmentCode assignmentStep).
              {
                exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
                  code output assignmentCode assignmentStep
                  truthCode truthStep supportCode supportStep
                  hwithTablesCopy rightCode rightOutput hrightCodeLt
                  hrightSupport hrightTruthLookup
                  (proj1 (proj2 horTruth))).
              }
              pose proof (hagree rightIndex (rawFixedLevelSigmaMode M)
                rightCode assignmentCode assignmentStep rightOutput
                hrightEarlier hrightState hrightCertificate) as [hrightTrue _].
              exact (raw_orTruth_output_one_of_right M hPA
                output leftOutput rightOutput horTruth
                (hrightTrue eq_refl)).
        -- destruct hex as [hcode _].
           exfalso. exact (raw_rankZeroTruthClosedStep_ex_false M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode hcode hrankZeroClosed).
        -- destruct hall as [hcode _].
           exfalso. exact (raw_rankZeroTruthClosedStep_all_false M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode hcode hrankZeroClosed).
      * intros hmodePi. exfalso.
        apply (raw_zero_neq_truthOne M hPA).
        exact (eq_trans (eq_sym hmode) hmodePi).
    + destruct hpi as [hpiDomain hpiCase].
      split.
      * intros hmodeSigma. exfalso.
        apply (raw_zero_neq_truthOne M hPA).
        exact (eq_trans (eq_sym hmodeSigma) hmode).
      * intros hmodePi.
        destruct hpiCase as
          [hrankZeroZero |
           [himp | [hand | [hor | [hall | hex]]]]].
        -- exact (raw_rankZeroTruthCertificate_output_functional M hPA
             code assignmentCode assignmentStep output (raw_zero M)
             hcertificatePublic hrankZeroZero).
        -- destruct himp as
             [hcode [[hleftEarlier hleftState]
                     [[hrightEarlier hrightState] hspare]]].
           destruct (raw_rankZeroTruthClosedStep_imp_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & himpTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           assert (hleftCertificate : RawRankZeroTruthCertificate M
               leftCode leftOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy leftCode leftOutput hleftCodeLt
               hleftSupport hleftTruthLookup (proj1 himpTruth)).
           }
           assert (hrightCertificate : RawRankZeroTruthCertificate M
               rightCode rightOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy rightCode rightOutput hrightCodeLt
               hrightSupport hrightTruthLookup
               (proj1 (proj2 himpTruth))).
           }
           pose proof (hagree leftIndex (rawFixedLevelSigmaMode M)
             leftCode assignmentCode assignmentStep leftOutput
             hleftEarlier hleftState hleftCertificate) as [hleftTrue _].
           pose proof (hagree rightIndex (rawFixedLevelPiMode M)
             rightCode assignmentCode assignmentStep rightOutput
             hrightEarlier hrightState hrightCertificate) as [_ hrightFalse].
           exact (raw_impTruth_output_zero M hPA
             output leftOutput rightOutput himpTruth
             (hleftTrue eq_refl) (hrightFalse eq_refl)).
        -- destruct hand as [hcode hchosen].
           destruct (raw_rankZeroTruthClosedStep_and_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & handTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           destruct hchosen as
             [[hleftEarlier hleftState] | [hrightEarlier hrightState]].
           ++ assert (hleftCertificate : RawRankZeroTruthCertificate M
                  leftCode leftOutput assignmentCode assignmentStep).
              {
                exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
                  code output assignmentCode assignmentStep
                  truthCode truthStep supportCode supportStep
                  hwithTablesCopy leftCode leftOutput hleftCodeLt
                  hleftSupport hleftTruthLookup (proj1 handTruth)).
              }
              pose proof (hagree leftIndex (rawFixedLevelPiMode M)
                leftCode assignmentCode assignmentStep leftOutput
                hleftEarlier hleftState hleftCertificate) as [_ hleftFalse].
              exact (raw_andTruth_output_zero_of_left M hPA
                output leftOutput rightOutput handTruth
                (hleftFalse eq_refl)).
           ++ assert (hrightCertificate : RawRankZeroTruthCertificate M
                  rightCode rightOutput assignmentCode assignmentStep).
              {
                exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
                  code output assignmentCode assignmentStep
                  truthCode truthStep supportCode supportStep
                  hwithTablesCopy rightCode rightOutput hrightCodeLt
                  hrightSupport hrightTruthLookup
                  (proj1 (proj2 handTruth))).
              }
              pose proof (hagree rightIndex (rawFixedLevelPiMode M)
                rightCode assignmentCode assignmentStep rightOutput
                hrightEarlier hrightState hrightCertificate) as [_ hrightFalse].
              exact (raw_andTruth_output_zero_of_right M hPA
                output leftOutput rightOutput handTruth
                (hrightFalse eq_refl)).
        -- destruct hor as
             [hcode [[hleftEarlier hleftState]
                     [hrightEarlier hrightState]]].
           destruct (raw_rankZeroTruthClosedStep_or_view M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode rightCode hcode hrankZeroClosed) as
             (leftOutput & rightOutput & hleftTruthLookup &
              hrightTruthLookup & horTruth & hleftSupport &
              hrightSupport & hleftCodeLt & hrightCodeLt).
           assert (hleftCertificate : RawRankZeroTruthCertificate M
               leftCode leftOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy leftCode leftOutput hleftCodeLt
               hleftSupport hleftTruthLookup (proj1 horTruth)).
           }
           assert (hrightCertificate : RawRankZeroTruthCertificate M
               rightCode rightOutput assignmentCode assignmentStep).
           {
             exact (raw_rankZeroTruthCertificate_child_with_tables M hPA
               code output assignmentCode assignmentStep
               truthCode truthStep supportCode supportStep
               hwithTablesCopy rightCode rightOutput hrightCodeLt
               hrightSupport hrightTruthLookup
               (proj1 (proj2 horTruth))).
           }
           pose proof (hagree leftIndex (rawFixedLevelPiMode M)
             leftCode assignmentCode assignmentStep leftOutput
             hleftEarlier hleftState hleftCertificate) as [_ hleftFalse].
           pose proof (hagree rightIndex (rawFixedLevelPiMode M)
             rightCode assignmentCode assignmentStep rightOutput
             hrightEarlier hrightState hrightCertificate) as [_ hrightFalse].
           exact (raw_orTruth_output_zero M hPA
             output leftOutput rightOutput horTruth
             (hleftFalse eq_refl) (hrightFalse eq_refl)).
        -- destruct hall as [hcode _].
           exfalso. exact (raw_rankZeroTruthClosedStep_all_false M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode hcode hrankZeroClosed).
        -- destruct hex as [hcode _].
           exfalso. exact (raw_rankZeroTruthClosedStep_ex_false M hPA
             code output assignmentCode assignmentStep
             truthCode truthStep supportCode supportStep
             leftCode hcode hrankZeroClosed).
Qed.

Definition RawFixedLevelOneRankZeroAgreementWithin (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound current : M) : Prop :=
  rawLe M current bound ->
  RawFixedLevelOneRankZeroAgreementBelow M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep current.

Arguments RawFixedLevelOneRankZeroAgreementWithin
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode
    assignmentStepStep bound current : clear implicits.

Definition fixedLevelOneRankZeroAgreementWithinTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound current : term) : formula :=
  pImp (Formula.leTermAt current bound)
    (fixedLevelOneRankZeroAgreementBelowTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep current).

Lemma raw_sat_fixedLevelOneRankZeroAgreementWithinTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound current,
  raw_formula_sat M e
    (fixedLevelOneRankZeroAgreementWithinTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound current) <->
  RawFixedLevelOneRankZeroAgreementWithin M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound) (raw_term_eval M e current).
Proof.
  intros. unfold fixedLevelOneRankZeroAgreementWithinTermAt,
    RawFixedLevelOneRankZeroAgreementWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank,
    raw_sat_fixedLevelOneRankZeroAgreementBelowTermAt_iff.
  reflexivity.
Qed.

Lemma raw_fixedLevelOneRankZeroAgreementWithin_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep current,
  RawFixedLevelSuccessorTruthTraversal M 0
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep ->
  RawFixedLevelOneRankZeroAgreementWithin M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound current ->
  RawFixedLevelOneRankZeroAgreementWithin M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound (raw_succ M current).
Proof.
  intros M hPA lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep current htraversal hcurrent
    hsuccBound.
  assert (hcurrentBound : rawLt M current bound).
  {
    exact (raw_rank_lt_of_succ_le M hPA current bound hsuccBound).
  }
  apply (raw_fixedLevelOneRankZeroAgreementBelow_succ M hPA
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep current htraversal
    hcurrentBound).
  apply hcurrent. exact (raw_lt_to_le M current bound hcurrentBound).
Qed.

Theorem raw_fixedLevelOneRankZeroAgreementBelow_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M 0
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root rootAssignmentCode rootAssignmentStep ->
  RawFixedLevelOneRankZeroAgreementBelow M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound.
Proof.
  intros M hPA lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex rootMode root
    rootAssignmentCode rootAssignmentStep htraversal.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => modeCode
    | 1 => modeStep
    | 2 => formulaCode
    | 3 => formulaStep
    | 4 => assignmentCodeCode
    | 5 => assignmentCodeStep
    | 6 => assignmentStepCode
    | 7 => assignmentStepStep
    | _ => bound
    end).
  set (phi := fixedLevelOneRankZeroAgreementWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_fixedLevelOneRankZeroAgreementWithinTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons]. intros hzeroBound.
      exact (raw_fixedLevelOneRankZeroAgreementBelow_zero M hPA
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_fixedLevelOneRankZeroAgreementWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_fixedLevelOneRankZeroAgreementWithinTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_fixedLevelOneRankZeroAgreementWithin_succ M hPA
        lowerSigmaEvidence lowerPiEvidence
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep bound rootIndex rootMode root
        rootAssignmentCode rootAssignmentStep current htraversal hcurrent).
  }
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_fixedLevelOneRankZeroAgreementWithinTermAt_iff M
      (scons M bound parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7) (tVar 8) (tVar 9) (tVar 0))
    (hall bound)) as hbound.
  unfold parameterEnv in hbound.
  cbn [raw_term_eval scons] in hbound.
  exact (hbound (raw_rank_le_refl M hPA bound)).
Qed.

Theorem raw_fixedLevelSigmaTruthCertificate_one_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root assignmentCode assignmentStep output,
  RawFixedLevelSigmaTruthCertificate M 1
    root assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M
    root output assignmentCode assignmentStep ->
  output = rawNumeralValue M 1.
Proof.
  intros M hPA root assignmentCode assignmentStep output hupper hzero.
  cbn [RawFixedLevelSigmaTruthCertificate] in hupper.
  destruct hupper as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
  pose proof (raw_fixedLevelOneRankZeroAgreementBelow_all M hPA
    (RawFixedLevelSigmaTruthCertificate M 0)
    (RawFixedLevelPiFalsityCertificate M 0)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep
    htraversal) as hagree.
  destruct htraversal as
    [hmodeDefined [hformulaDefined
     [hassignmentCodeDefined [hassignmentStepDefined
      [hrootIndex [hrootLookup hrows]]]]]].
  exact (proj1 (hagree rootIndex (rawFixedLevelSigmaMode M)
    root assignmentCode assignmentStep output
    hrootIndex hrootLookup hzero) eq_refl).
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_one_rankZero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root assignmentCode assignmentStep output,
  RawFixedLevelPiFalsityCertificate M 1
    root assignmentCode assignmentStep ->
  RawRankZeroTruthCertificate M
    root output assignmentCode assignmentStep ->
  output = raw_zero M.
Proof.
  intros M hPA root assignmentCode assignmentStep output hupper hzero.
  cbn [RawFixedLevelPiFalsityCertificate] in hupper.
  destruct hupper as
    (modeCode & modeStep & formulaCode & formulaStep &
     assignmentCodeCode & assignmentCodeStep &
     assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
  pose proof (raw_fixedLevelOneRankZeroAgreementBelow_all M hPA
    (RawFixedLevelSigmaTruthCertificate M 0)
    (RawFixedLevelPiFalsityCertificate M 0)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep
    htraversal) as hagree.
  destruct htraversal as
    [hmodeDefined [hformulaDefined
     [hassignmentCodeDefined [hassignmentStepDefined
      [hrootIndex [hrootLookup hrows]]]]]].
  exact (proj2 (hagree rootIndex (rawFixedLevelPiMode M)
    root assignmentCode assignmentStep output
    hrootIndex hrootLookup hzero) eq_refl).
Qed.

(** ------------------------------------------------------------------
    Public admissibility-guarded lowering and base coherence. *)

Theorem raw_fixedLevelSigmaTruthCertificate_one_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M 0
    root assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M 0 root ->
  RawFixedLevelSigmaTruthCertificate M 1
    root assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M 0
    root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep
    hadmissible hdomain hupper.
  pose proof (raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable M hPA
    root assignmentCode assignmentStep hadmissible) as hsyntax.
  destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax M hPA
    root assignmentCode assignmentStep hsyntax) as [output hcertificate].
  pose proof (raw_fixedLevelSigmaTruthCertificate_one_rankZero M hPA
    root assignmentCode assignmentStep output hupper hcertificate)
    as houtput.
  apply (raw_fixedLevelSigmaTruthCertificate_zero_of_local M hPA).
  split; [exact hdomain |].
  now rewrite <- houtput.
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_one_lower : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M 0
    root assignmentCode assignmentStep ->
  RawFixedLevelPiDomain M 0 root ->
  RawFixedLevelPiFalsityCertificate M 1
    root assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M 0
    root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep
    hadmissible hdomain hupper.
  pose proof (raw_fixedLevelTruthAdmissible_zeroSyntaxRealizable M hPA
    root assignmentCode assignmentStep hadmissible) as hsyntax.
  destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax M hPA
    root assignmentCode assignmentStep hsyntax) as [output hcertificate].
  pose proof (raw_fixedLevelPiFalsityCertificate_one_rankZero M hPA
    root assignmentCode assignmentStep output hupper hcertificate)
    as houtput.
  apply (raw_fixedLevelPiFalsityCertificate_zero_of_local M hPA).
  split; [exact hdomain |].
  now rewrite <- houtput.
Qed.

Theorem raw_fixedLevelAdmissibleTruthCertificateCoherence_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawFixedLevelAdmissibleTruthCertificateCoherenceAt M 0.
Proof.
  intros M hPA root assignmentCode assignmentStep hadmissible.
  destruct (raw_fixedLevelTruthCertificate_zero_raise M hPA)
    as [hsigmaRaise hpiRaise].
  split.
  - intros hsigmaDomain. split.
    + apply hsigmaRaise.
    + apply (raw_fixedLevelSigmaTruthCertificate_one_lower M hPA
        root assignmentCode assignmentStep hadmissible hsigmaDomain).
  - intros hpiDomain. split.
    + apply hpiRaise.
    + apply (raw_fixedLevelPiFalsityCertificate_one_lower M hPA
        root assignmentCode assignmentStep hadmissible hpiDomain).
Qed.

Theorem fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula 0).
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_fixedLevelAdmissibleTruthCertificateCoherenceFormula_iff
      M e 0)).
  exact (raw_fixedLevelAdmissibleTruthCertificateCoherence_zero M hPA).
Qed.

Definition fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed
    : formula :=
  Formula.sealPA
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula 0).

Theorem
    fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed_sentence :
  Formula.Sentence
    fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed.
Proof.
  unfold fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed.
  apply Formula.sealPA_sentence.
Qed.

Theorem
    fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed_raw_valid :
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed.
Proof.
  intros M hPA e.
  unfold fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed.
  apply (raw_formula_sat_sealPA_of_valid M).
  intros e'.
  exact
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_raw_valid
      M hPA e').
Qed.

Theorem
    PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed :
  Formula.BProv Formula.Ax_s []
    fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact
      fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed_sentence.
  - exact
      fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed_raw_valid.
Qed.

(** Universal elimination of the mechanical closure recovers the original
    displayed formula.  Thus the public theorem is about exactly the formula
    whose raw semantics was stated in the coherence module. *)
Theorem PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero :
  Formula.BProv Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula 0).
Proof.
  pose proof (Formula.BProv_sealPA_allE_rename
    Formula.Ax_s []
    (fixedLevelAdmissibleTruthCertificateCoherenceFormula 0)
    (fun n => n)
    PA_proves_fixedLevelAdmissibleTruthCertificateCoherenceFormula_zero_closed)
    as hclosed.
  now rewrite Formula.rename_id in hclosed.
Qed.

(** Definedness is downward closed in its numeric bound.  We state the
    strict version because constructor descent naturally produces [child <
    parent]. *)
Lemma raw_codedAssignmentDefinedThrough_of_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    assignmentCode assignmentStep child parent,
  rawLt M child parent ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep parent ->
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep child.
Proof.
  intros M hPA assignmentCode assignmentStep child parent
    hchild hdefined index hindex.
  apply hdefined.
  exact (raw_assignment_lt_trans M hPA
    index child parent hindex hchild).
Qed.

(** Re-root an occurrence-indexed syntax certificate at any row of the same
    traversal.  The atomic-term clause quantifies over all equality rows of
    the traversal, so it can be reused unchanged. *)
Lemma raw_codedFormulaAtomicallyAdequate_at_lookup : forall
    (M : RawPAModel) formulaCode formulaStep bound rootIndex root,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  RawCodedFormulaAtomicTermAdequate M
    formulaCode formulaStep bound ->
  forall childIndex child,
    rawLt M childIndex bound ->
    RawCodedAssignmentLookup M
      formulaCode formulaStep childIndex child ->
    RawCodedFormulaAtomicallyAdequate M child.
Proof.
  intros M formulaCode formulaStep bound rootIndex root
    [hdefined [_ [_ hrows]]] hadequate childIndex child
    hchildIndex hchildLookup.
  exists formulaCode, formulaStep, bound, childIndex.
  split.
  - repeat split; assumption.
  - exact hadequate.
Qed.

(** A child occurrence inherits the syntax and assignment portions of full
    admissibility.  Its polarity-specific domain is supplied separately by
    the constructor-domain inversion lemmas. *)
Lemma raw_fixedLevelTruthAdmissible_child_core : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    level root assignmentCode assignmentStep,
  RawFixedLevelTruthAdmissible M level
    root assignmentCode assignmentStep ->
  forall formulaCode formulaStep bound rootIndex childIndex child,
    RawCodedFormulaSyntaxTraversal M
      formulaCode formulaStep bound rootIndex root ->
    RawCodedFormulaAtomicTermAdequate M
      formulaCode formulaStep bound ->
    rawLt M childIndex bound ->
    RawCodedAssignmentLookup M
      formulaCode formulaStep childIndex child ->
    rawLt M child root ->
    RawCodedFormulaAtomicallyAdequate M child /\
    RawCodedAssignmentDefinedThrough M
      assignmentCode assignmentStep child.
Proof.
  intros M hPA level root assignmentCode assignmentStep
    [_ [hassignment _]] formulaCode formulaStep bound rootIndex
    childIndex child hsyntax hadequate hchildIndex hchildLookup
    hchildCode.
  split.
  - exact (raw_codedFormulaAtomicallyAdequate_at_lookup M
      formulaCode formulaStep bound rootIndex root
      hsyntax hadequate childIndex child hchildIndex hchildLookup).
  - exact (raw_codedAssignmentDefinedThrough_of_lt M hPA
      assignmentCode assignmentStep child root
      hchildCode hassignment).
Qed.

(** Binder extension is defined through [S root].  Every recursive child
    code is below [root], hence the extended assignment is certainly defined
    through that child.  This is the assignment half needed for quantified
    descendants in later adjacent-level inductions. *)
Lemma raw_codedAssignmentPrepend_child_defined : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    assignmentCode assignmentStep witness root
    newAssignmentCode newAssignmentStep child,
  RawCodedAssignmentDefinedThrough M
    assignmentCode assignmentStep root ->
  RawCodedAssignmentPrepend M
    assignmentCode assignmentStep witness root
    newAssignmentCode newAssignmentStep ->
  rawLt M child root ->
  RawCodedAssignmentDefinedThrough M
    newAssignmentCode newAssignmentStep child.
Proof.
  intros M hPA assignmentCode assignmentStep witness root
    newAssignmentCode newAssignmentStep child
    hdefined hprepend hchild.
  pose proof (raw_codedAssignmentPrepend_definedThrough M hPA
    assignmentCode assignmentStep witness root
    newAssignmentCode newAssignmentStep hdefined hprepend) as hnew.
  apply (raw_codedAssignmentDefinedThrough_of_lt M hPA
    newAssignmentCode newAssignmentStep child (raw_succ M root)).
  - exact (raw_assignment_lt_trans M hPA child root (raw_succ M root)
      hchild (raw_assignment_lt_self_succ M hPA root)).
  - exact hnew.
Qed.

End PABoundedRawCodedFixedLevelTruthAdmissibleLowering.
