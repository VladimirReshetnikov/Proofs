(**
  Model-internal realization of rank-zero truth certificates.

  The input is an arithmetized syntax oracle, not a Rocq formula.  Its beta
  support table may have a nonstandard bound and says that every supported
  code is equality, bottom, implication, conjunction, or disjunction; every
  Boolean child is supported at a strictly smaller code.  A separate genuine
  PA formula says that the two term codes in every supported equality atom
  have model-internal term-syntax certificates for the chosen assignment.

  PA induction then builds the truth beta table through the arbitrary model
  bound.  Truth-table CRT capacity is proved rather than assumed: PA supplies
  a common-multiple coding step at least two, and every truth output is zero
  or one.  The only remaining capacity boundary is inherited honestly from
  term evaluation at equality atoms.  It is exposed by
  [RawRankZeroAtomicTermCapacity], never hidden as a decoding assumption.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  PolynomialPairInjectivity RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedRankZeroTruthStep
  RawCodedRankZeroTruthTraversal.

Import ListNotations.

Module PABoundedRawCodedRankZeroTruthRealization.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.

(** ------------------------------------------------------------------
    Independently arithmetized quantifier-free syntax. *)

Definition RawRankZeroSyntaxWitnessRow (M : RawPAModel)
    (code supportCode supportStep left right : M) : Prop :=
  code = rawFormulaEqCode M left right \/
  code = rawFormulaBotCode M \/
  (code = rawFormulaImpCode M left right /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code) \/
  (code = rawFormulaAndCode M left right /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code) \/
  (code = rawFormulaOrCode M left right /\
    rawFormulaCodeSupported M supportCode supportStep left /\
    rawFormulaCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code).

Arguments RawRankZeroSyntaxWitnessRow
  M code supportCode supportStep left right : clear implicits.

Definition rankZeroSyntaxWitnessRowTermAt
    (code supportCode supportStep left right : term) : formula :=
  pOr
    (formulaEqCodeTermAt code left right)
    (pOr
      (formulaBotCodeTermAt code)
      (pOr
        (pAnd
          (formulaImpCodeTermAt code left right)
          (pAnd4
            (formulaCodeSupportedTermAt supportCode supportStep left)
            (formulaCodeSupportedTermAt supportCode supportStep right)
            (Formula.ltTermAt left code)
            (Formula.ltTermAt right code)))
        (pOr
          (pAnd
            (formulaAndCodeTermAt code left right)
            (pAnd4
              (formulaCodeSupportedTermAt supportCode supportStep left)
              (formulaCodeSupportedTermAt supportCode supportStep right)
              (Formula.ltTermAt left code)
              (Formula.ltTermAt right code)))
          (pAnd
            (formulaOrCodeTermAt code left right)
            (pAnd4
              (formulaCodeSupportedTermAt supportCode supportStep left)
              (formulaCodeSupportedTermAt supportCode supportStep right)
              (Formula.ltTermAt left code)
              (Formula.ltTermAt right code)))))).

Lemma raw_sat_rankZeroSyntaxWitnessRowTermAt_iff : forall
    (M : RawPAModel) e code supportCode supportStep left right,
  raw_formula_sat M e
    (rankZeroSyntaxWitnessRowTermAt
      code supportCode supportStep left right) <->
  RawRankZeroSyntaxWitnessRow M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold rankZeroSyntaxWitnessRowTermAt,
    RawRankZeroSyntaxWitnessRow, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaEqCodeTermAt_iff,
    raw_sat_formulaBotCodeTermAt_iff,
    raw_sat_formulaImpCodeTermAt_iff,
    raw_sat_formulaAndCodeTermAt_iff,
    raw_sat_formulaOrCodeTermAt_iff,
    !raw_sat_formulaCodeSupportedTermAt_iff,
    !raw_sat_ltTermAt_iff.
  tauto.
Qed.

Definition rankZeroSyntaxStepTermAt
    (code supportCode supportStep : term) : formula :=
  pEx (pEx
    (rankZeroSyntaxWitnessRowTermAt
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))).

Definition RawRankZeroSyntaxStep (M : RawPAModel)
    (code supportCode supportStep : M) : Prop :=
  exists left right : M,
    RawRankZeroSyntaxWitnessRow M
      code supportCode supportStep left right.

Arguments RawRankZeroSyntaxStep M code supportCode supportStep
  : clear implicits.

Lemma raw_sat_rankZeroSyntaxStepTermAt_iff : forall
    (M : RawPAModel) e code supportCode supportStep,
  raw_formula_sat M e
    (rankZeroSyntaxStepTermAt code supportCode supportStep) <->
  RawRankZeroSyntaxStep M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e code supportCode supportStep.
  unfold rankZeroSyntaxStepTermAt, RawRankZeroSyntaxStep.
  cbn [raw_formula_sat]. split.
  - intros [left [right hrow]]. exists left, right.
    apply (proj1 (raw_sat_rankZeroSyntaxWitnessRowTermAt_iff M
      (scons M right (scons M left e))
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_two_traversal in hrow.
    cbn [raw_term_eval scons] in hrow. exact hrow.
  - intros [left [right hrow]]. exists left, right.
    apply (proj2 (raw_sat_rankZeroSyntaxWitnessRowTermAt_iff M
      (scons M right (scons M left e))
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_two_traversal.
    cbn [raw_term_eval scons]. exact hrow.
Qed.

Definition RawRankZeroSyntaxTraversal (M : RawPAModel)
    (bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code,
    rawLt M code bound ->
    rawFormulaCodeSupported M supportCode supportStep code ->
    RawRankZeroSyntaxStep M code supportCode supportStep.

Arguments RawRankZeroSyntaxTraversal M bound supportCode supportStep
  : clear implicits.

Definition rankZeroSyntaxTraversalTermAt
    (bound supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (formulaCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (rankZeroSyntaxStepTermAt
            (tVar 0) (liftTerm 1 supportCode) (liftTerm 1 supportStep))))).

Lemma raw_sat_rankZeroSyntaxTraversalTermAt_iff : forall
    (M : RawPAModel) e bound supportCode supportStep,
  raw_formula_sat M e
    (rankZeroSyntaxTraversalTermAt bound supportCode supportStep) <->
  RawRankZeroSyntaxTraversal M
    (raw_term_eval M e bound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound supportCode supportStep.
  unfold rankZeroSyntaxTraversalTermAt, RawRankZeroSyntaxTraversal.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  split.
  - intros [hdefined hrows]. split; [exact hdefined |].
    intros code hcode hsupported.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportSat : raw_formula_sat M (scons M code e)
        (formulaCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    pose proof (hrows code hltSat hsupportSat) as hstepSat.
    apply (proj1 (raw_sat_rankZeroSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))) in hstepSat.
    rewrite !raw_term_eval_liftTerm_one_traversal in hstepSat.
    cbn [raw_term_eval scons] in hstepSat. exact hstepSat.
  - intros [hdefined hrows]. split; [exact hdefined |].
    intros code hltSat hsupportSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)
      hsupportSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    apply (proj2 (raw_sat_rankZeroSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))).
    rewrite !raw_term_eval_liftTerm_one_traversal.
    cbn [raw_term_eval scons]. exact (hrows code hcode hsupported).
Qed.

(** Equality payloads are term codes.  This independent formula requires
    their term-syntax certificates for the same coded assignment, without
    asserting the separate CRT capacity needed to realize those terms. *)
Definition RawRankZeroSyntaxTermAdequate (M : RawPAModel)
    (bound assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  forall code,
    rawLt M code bound ->
    rawFormulaCodeSupported M supportCode supportStep code ->
    forall left right,
      code = rawFormulaEqCode M left right ->
      RawTermSyntaxRealizable M left assignmentCode assignmentStep /\
      RawTermSyntaxRealizable M right assignmentCode assignmentStep.

Arguments RawRankZeroSyntaxTermAdequate
  M bound assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Definition rankZeroSyntaxTermAdequateTermAt
    (bound assignmentCode assignmentStep supportCode supportStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pImp
        (formulaCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (pAll (pAll
          (pImp
            (formulaEqCodeTermAt (tVar 2) (tVar 1) (tVar 0))
            (pAnd
              (termSyntaxRealizableTermAt
                (tVar 1) (liftTerm 3 assignmentCode)
                (liftTerm 3 assignmentStep))
              (termSyntaxRealizableTermAt
                (tVar 0) (liftTerm 3 assignmentCode)
                (liftTerm 3 assignmentStep)))))))).

Lemma raw_sat_rankZeroSyntaxTermAdequateTermAt_iff : forall
    (M : RawPAModel) e bound assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (rankZeroSyntaxTermAdequateTermAt
      bound assignmentCode assignmentStep supportCode supportStep) <->
  RawRankZeroSyntaxTermAdequate M
    (raw_term_eval M e bound)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound assignmentCode assignmentStep supportCode supportStep.
  unfold rankZeroSyntaxTermAdequateTermAt,
    RawRankZeroSyntaxTermAdequate.
  cbn [raw_formula_sat]. split.
  - intros h code hcode hsupported left right heq.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportSat : raw_formula_sat M (scons M code e)
        (formulaCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    assert (heqSat : raw_formula_sat M
        (scons M right (scons M left (scons M code e)))
        (formulaEqCodeTermAt (tVar 2) (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_formulaEqCodeTermAt_iff M _ _ _ _)).
      cbn [raw_term_eval scons]. exact heq.
    }
    pose proof (h code hltSat hsupportSat left right heqSat)
      as [hleftSat hrightSat]. split.
    + apply (proj1 (raw_sat_termSyntaxRealizableTermAt_iff M
        (scons M right (scons M left (scons M code e)))
        (tVar 1) (liftTerm 3 assignmentCode)
        (liftTerm 3 assignmentStep))) in hleftSat.
      rewrite !raw_term_eval_liftTerm_three_traversal in hleftSat.
      cbn [raw_term_eval scons] in hleftSat. exact hleftSat.
    + apply (proj1 (raw_sat_termSyntaxRealizableTermAt_iff M
        (scons M right (scons M left (scons M code e)))
        (tVar 0) (liftTerm 3 assignmentCode)
        (liftTerm 3 assignmentStep))) in hrightSat.
      rewrite !raw_term_eval_liftTerm_three_traversal in hrightSat.
      cbn [raw_term_eval scons] in hrightSat. exact hrightSat.
  - intros h code hltSat hsupportSat left right heqSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_formulaCodeSupportedTermAt_iff M _ _ _ _)
      hsupportSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    pose proof (proj1 (raw_sat_formulaEqCodeTermAt_iff M _ _ _ _)
      heqSat) as heq.
    cbn [raw_term_eval scons] in heq.
    destruct (h code hcode hsupported left right heq)
      as [hleft hright]. split.
    + apply (proj2 (raw_sat_termSyntaxRealizableTermAt_iff M
        (scons M right (scons M left (scons M code e)))
        (tVar 1) (liftTerm 3 assignmentCode)
        (liftTerm 3 assignmentStep))).
      rewrite !raw_term_eval_liftTerm_three_traversal.
      cbn [raw_term_eval scons]. exact hleft.
    + apply (proj2 (raw_sat_termSyntaxRealizableTermAt_iff M
        (scons M right (scons M left (scons M code e)))
        (tVar 0) (liftTerm 3 assignmentCode)
        (liftTerm 3 assignmentStep))).
      rewrite !raw_term_eval_liftTerm_three_traversal.
      cbn [raw_term_eval scons]. exact hright.
Qed.

Definition RawRankZeroSyntaxCertificateWithSupport (M : RawPAModel)
    (root assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  RawRankZeroSyntaxTraversal M
    (raw_succ M root) supportCode supportStep /\
  RawRankZeroSyntaxTermAdequate M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep /\
  rawFormulaCodeSupported M supportCode supportStep root.

Arguments RawRankZeroSyntaxCertificateWithSupport
  M root assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Definition rankZeroSyntaxCertificateWithSupportTermAt
    (root assignmentCode assignmentStep supportCode supportStep : term)
    : formula :=
  pAnd3
    (rankZeroSyntaxTraversalTermAt
      (tSucc root) supportCode supportStep)
    (rankZeroSyntaxTermAdequateTermAt
      (tSucc root) assignmentCode assignmentStep supportCode supportStep)
    (formulaCodeSupportedTermAt supportCode supportStep root).

Lemma raw_sat_rankZeroSyntaxCertificateWithSupportTermAt_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (rankZeroSyntaxCertificateWithSupportTermAt
      root assignmentCode assignmentStep supportCode supportStep) <->
  RawRankZeroSyntaxCertificateWithSupport M
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold rankZeroSyntaxCertificateWithSupportTermAt,
    RawRankZeroSyntaxCertificateWithSupport, pAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_rankZeroSyntaxTraversalTermAt_iff,
    raw_sat_rankZeroSyntaxTermAdequateTermAt_iff,
    raw_sat_formulaCodeSupportedTermAt_iff.
  reflexivity.
Qed.

Definition rankZeroSyntaxRealizableTermAt
    (root assignmentCode assignmentStep : term) : formula :=
  pEx (pEx
    (rankZeroSyntaxCertificateWithSupportTermAt
      (liftTerm 2 root) (liftTerm 2 assignmentCode)
      (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))).

Definition RawRankZeroSyntaxRealizable (M : RawPAModel)
    (root assignmentCode assignmentStep : M) : Prop :=
  exists supportCode supportStep : M,
    RawRankZeroSyntaxCertificateWithSupport M
      root assignmentCode assignmentStep supportCode supportStep.

Arguments RawRankZeroSyntaxRealizable
  M root assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_rankZeroSyntaxRealizableTermAt_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
    (rankZeroSyntaxRealizableTermAt root assignmentCode assignmentStep) <->
  RawRankZeroSyntaxRealizable M
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros M e root assignmentCode assignmentStep.
  unfold rankZeroSyntaxRealizableTermAt, RawRankZeroSyntaxRealizable.
  cbn [raw_formula_sat]. split.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj1
      (raw_sat_rankZeroSyntaxCertificateWithSupportTermAt_iff M
        (scons M supportStep (scons M supportCode e))
        (liftTerm 2 root) (liftTerm 2 assignmentCode)
        (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))) in hsyntax.
    rewrite !raw_term_eval_liftTerm_two_traversal in hsyntax.
    cbn [raw_term_eval scons] in hsyntax. exact hsyntax.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj2
      (raw_sat_rankZeroSyntaxCertificateWithSupportTermAt_iff M
        (scons M supportStep (scons M supportCode e))
        (liftTerm 2 root) (liftTerm 2 assignmentCode)
        (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_two_traversal.
    cbn [raw_term_eval scons]. exact hsyntax.
Qed.

(** ------------------------------------------------------------------
    The inherited atomic-term capacity seam. *)

Definition RawRankZeroAtomicTermCapacity (M : RawPAModel)
    (bound assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  forall code left right,
    rawLt M code bound ->
    rawFormulaCodeSupported M supportCode supportStep code ->
    code = rawFormulaEqCode M left right ->
    forall termCode termSupportCode termSupportStep,
      (termCode = left \/ termCode = right) ->
      RawTermSyntaxCertificateWithSupport M
        termCode assignmentCode assignmentStep
        termSupportCode termSupportStep ->
      RawTermEvaluationRealizationCapacity M (raw_succ M termCode)
        assignmentCode assignmentStep termSupportCode termSupportStep.

Arguments RawRankZeroAtomicTermCapacity
  M bound assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

(** ------------------------------------------------------------------
    Truth bits and locally realized closed rows. *)

Lemma raw_rankZeroTruthClosedStep_output_bit : forall
    (M : RawPAModel) code output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep,
  RawRankZeroTruthClosedStep M code output
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  RawTruthBit M output.
Proof.
  intros M code output assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep
    [left [leftValue [right [rightValue hrow]]]].
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct heq as [_ [_ [_ [[_ hout] | [_ hout]]]]];
      unfold RawTruthBit; [right | left]; exact hout.
  - destruct hbot as [_ hout]. unfold RawTruthBit. left. exact hout.
  - destruct himp as [himp _].
    destruct himp as [_ [_ [_ [_ [_ [hout _]]]]]]. exact hout.
  - destruct hand as [hand _].
    destruct hand as [_ [_ [_ [_ [_ [hout _]]]]]]. exact hout.
  - destruct hor as [hor _].
    destruct hor as [_ [_ [_ [_ [_ [hout _]]]]]]. exact hout.
Qed.

Lemma raw_rankZeroTruthTraversal_lookup_bit : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall current assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep,
  RawRankZeroTruthTraversal M current
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  forall code output,
    rawLt M code current ->
    rawFormulaCodeSupported M supportCode supportStep code ->
    RawCodedAssignmentLookup M truthCode truthStep code output ->
    RawTruthBit M output.
Proof.
  intros M hPA current assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep [_ [_ hrows]] code output hcode hsupported
    hlookup.
  destruct (hrows code hcode hsupported)
    as [canonical [hcanonical hstep]].
  assert (hout : output = canonical).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      truthCode truthStep code output canonical hlookup hcanonical).
  }
  rewrite hout.
  exact (raw_rankZeroTruthClosedStep_output_bit M
    code canonical assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep hstep).
Qed.

Lemma raw_impTruth_exists : forall (M : RawPAModel) left right,
  RawTruthBit M left -> RawTruthBit M right ->
  exists output, RawImpTruth M output left right.
Proof.
  intros M left right [hl | hl] [hr | hr]; subst left; subst right.
  - exists (rawTruthOne M). unfold RawImpTruth.
    split; [left; reflexivity |]. split; [left; reflexivity |].
    split; [right; reflexivity |].
    right. split; [left; reflexivity | reflexivity].
  - exists (rawTruthOne M). unfold RawImpTruth.
    split; [left; reflexivity |]. split; [right; reflexivity |].
    split; [right; reflexivity |].
    right. split; [left; reflexivity | reflexivity].
  - exists (raw_zero M). unfold RawImpTruth.
    split; [right; reflexivity |]. split; [left; reflexivity |].
    split; [left; reflexivity |].
    left. repeat split; reflexivity.
  - exists (rawTruthOne M). unfold RawImpTruth.
    split; [right; reflexivity |]. split; [right; reflexivity |].
    split; [right; reflexivity |].
    right. split; [right; reflexivity | reflexivity].
Qed.

Lemma raw_andTruth_exists : forall (M : RawPAModel) left right,
  RawTruthBit M left -> RawTruthBit M right ->
  exists output, RawAndTruth M output left right.
Proof.
  intros M left right [hl | hl] [hr | hr]; subst left; subst right.
  - exists (raw_zero M). unfold RawAndTruth.
    split; [left; reflexivity |]. split; [left; reflexivity |].
    split; [left; reflexivity |].
    right. split; [left; reflexivity | reflexivity].
  - exists (raw_zero M). unfold RawAndTruth.
    split; [left; reflexivity |]. split; [right; reflexivity |].
    split; [left; reflexivity |].
    right. split; [left; reflexivity | reflexivity].
  - exists (raw_zero M). unfold RawAndTruth.
    split; [right; reflexivity |]. split; [left; reflexivity |].
    split; [left; reflexivity |].
    right. split; [right; reflexivity | reflexivity].
  - exists (rawTruthOne M). unfold RawAndTruth.
    split; [right; reflexivity |]. split; [right; reflexivity |].
    split; [right; reflexivity |].
    left. repeat split; reflexivity.
Qed.

Lemma raw_orTruth_exists : forall (M : RawPAModel) left right,
  RawTruthBit M left -> RawTruthBit M right ->
  exists output, RawOrTruth M output left right.
Proof.
  intros M left right [hl | hl] [hr | hr]; subst left; subst right.
  - exists (raw_zero M). unfold RawOrTruth.
    split; [left; reflexivity |]. split; [left; reflexivity |].
    split; [left; reflexivity |].
    right. repeat split; reflexivity.
  - exists (rawTruthOne M). unfold RawOrTruth.
    split; [left; reflexivity |]. split; [right; reflexivity |].
    split; [right; reflexivity |].
    left. split; [right; reflexivity | reflexivity].
  - exists (rawTruthOne M). unfold RawOrTruth.
    split; [right; reflexivity |]. split; [left; reflexivity |].
    split; [right; reflexivity |].
    left. split; [left; reflexivity | reflexivity].
  - exists (rawTruthOne M). unfold RawOrTruth.
    split; [right; reflexivity |]. split; [right; reflexivity |].
    split; [right; reflexivity |].
    left. split; [left; reflexivity | reflexivity].
Qed.

Lemma raw_rankZeroSyntaxStep_truth_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound assignmentCode assignmentStep supportCode supportStep
    truthCode truthStep code,
  RawRankZeroSyntaxTermAdequate M bound
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M bound
    assignmentCode assignmentStep supportCode supportStep ->
  rawLt M code bound ->
  rawFormulaCodeSupported M supportCode supportStep code ->
  RawRankZeroTruthTraversal M code
    assignmentCode assignmentStep truthCode truthStep
    supportCode supportStep ->
  RawRankZeroSyntaxStep M code supportCode supportStep ->
  exists output,
    RawRankZeroTruthClosedStep M code output
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep.
Proof.
  intros M hPA bound assignmentCode assignmentStep supportCode supportStep
    truthCode truthStep code htermAdequate htermCapacity
    hcode hsupported htraversal [left [right hshape]].
  destruct hshape as [heq | [hbot | [himp | [hand | hor]]]].
  - destruct (htermAdequate code hcode hsupported left right heq)
      as [[leftSupportCode [leftSupportStep hleftSyntax]]
          [rightSupportCode [rightSupportStep hrightSyntax]]].
    pose proof (htermCapacity code left right hcode hsupported heq
      left leftSupportCode leftSupportStep (or_introl eq_refl)
      hleftSyntax) as hleftCapacity.
    pose proof (htermCapacity code left right hcode hsupported heq
      right rightSupportCode rightSupportStep (or_intror eq_refl)
      hrightSyntax) as hrightCapacity.
    destruct (raw_termEvaluationCertificate_exists_of_syntax_capacity
      M hPA left assignmentCode assignmentStep
      leftSupportCode leftSupportStep hleftSyntax hleftCapacity)
      as [leftValue hleftValue].
    destruct (raw_termEvaluationCertificate_exists_of_syntax_capacity
      M hPA right assignmentCode assignmentStep
      rightSupportCode rightSupportStep hrightSyntax hrightCapacity)
      as [rightValue hrightValue].
    destruct (classic (leftValue = rightValue)) as [hvalues | hvalues].
    + exists (rawTruthOne M), left, leftValue, right, rightValue.
      left. repeat split; try assumption.
      left. split; [exact hvalues | reflexivity].
    + exists (raw_zero M), left, leftValue, right, rightValue.
      left. repeat split; try assumption.
      right. split; [exact hvalues | reflexivity].
  - exists (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M).
    right. left. split; [exact hbot | reflexivity].
  - destruct himp as
      [hshape [hleftSupport [hrightSupport [hleft hright]]]].
    destruct htraversal as [hsupportDefined [htruthDefined hrows]].
    destruct (htruthDefined left hleft) as [leftTruth hleftLookup].
    destruct (htruthDefined right hright) as [rightTruth hrightLookup].
    assert (hleftBit : RawTruthBit M leftTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        left leftTruth hleft hleftSupport hleftLookup).
    }
    assert (hrightBit : RawTruthBit M rightTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        right rightTruth hright hrightSupport hrightLookup).
    }
    destruct (raw_impTruth_exists M leftTruth rightTruth
      hleftBit hrightBit) as [output htruth].
    exists output, left, leftTruth, right, rightTruth.
    right. right. left. split.
    + split; [exact hshape |]. split; [exact hleftLookup |].
      split; [exact hrightLookup | exact htruth].
    + repeat split; assumption.
  - destruct hand as
      [hshape [hleftSupport [hrightSupport [hleft hright]]]].
    destruct htraversal as [hsupportDefined [htruthDefined hrows]].
    destruct (htruthDefined left hleft) as [leftTruth hleftLookup].
    destruct (htruthDefined right hright) as [rightTruth hrightLookup].
    assert (hleftBit : RawTruthBit M leftTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        left leftTruth hleft hleftSupport hleftLookup).
    }
    assert (hrightBit : RawTruthBit M rightTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        right rightTruth hright hrightSupport hrightLookup).
    }
    destruct (raw_andTruth_exists M leftTruth rightTruth
      hleftBit hrightBit) as [output htruth].
    exists output, left, leftTruth, right, rightTruth.
    right. right. right. left. split.
    + split; [exact hshape |]. split; [exact hleftLookup |].
      split; [exact hrightLookup | exact htruth].
    + repeat split; assumption.
  - destruct hor as
      [hshape [hleftSupport [hrightSupport [hleft hright]]]].
    destruct htraversal as [hsupportDefined [htruthDefined hrows]].
    destruct (htruthDefined left hleft) as [leftTruth hleftLookup].
    destruct (htruthDefined right hright) as [rightTruth hrightLookup].
    assert (hleftBit : RawTruthBit M leftTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        left leftTruth hleft hleftSupport hleftLookup).
    }
    assert (hrightBit : RawTruthBit M rightTruth).
    {
      exact (raw_rankZeroTruthTraversal_lookup_bit M hPA
        code assignmentCode assignmentStep truthCode truthStep
        supportCode supportStep
        (conj hsupportDefined (conj htruthDefined hrows))
        right rightTruth hright hrightSupport hrightLookup).
    }
    destruct (raw_orTruth_exists M leftTruth rightTruth
      hleftBit hrightBit) as [output htruth].
    exists output, left, leftTruth, right, rightTruth.
    right. right. right. right. split.
    + split; [exact hshape |]. split; [exact hleftLookup |].
      split; [exact hrightLookup | exact htruth].
    + repeat split; assumption.
Qed.

(** A truth row reads its truth table only at smaller Boolean children. *)
Lemma raw_rankZeroTruthClosedStep_beta_extend : forall
    (M : RawPAModel) assignmentCode assignmentStep
      oldTruthCode newTruthCode truthStep supportCode supportStep
      target code appendedOutput,
  RawBetaCodeExtension M oldTruthCode truthStep
    target appendedOutput newTruthCode ->
  (forall child, rawLt M child code -> rawLt M child target) ->
  forall output,
  RawRankZeroTruthClosedStep M code output
    assignmentCode assignmentStep oldTruthCode truthStep
    supportCode supportStep ->
  RawRankZeroTruthClosedStep M code output
    assignmentCode assignmentStep newTruthCode truthStep
    supportCode supportStep.
Proof.
  intros M assignmentCode assignmentStep oldTruthCode newTruthCode
    truthStep supportCode supportStep target code appendedOutput
    hext hchildren output
    [left [leftValue [right [rightValue hrow]]]].
  exists left, leftValue, right, rightValue.
  destruct hrow as [heq | [hbot | [himp | [hand | hor]]]].
  - left. exact heq.
  - right. left. exact hbot.
  - right. right. left.
    destruct himp as
      [[hshape [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleft hright]]]].
    split.
    + split; [exact hshape |]. split.
      * exact ((proj1 hext) left (hchildren left hleft)
          leftValue hleftLookup).
      * split.
        -- exact ((proj1 hext) right (hchildren right hright)
             rightValue hrightLookup).
        -- exact htruth.
    + repeat split; assumption.
  - right. right. right. left.
    destruct hand as
      [[hshape [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleft hright]]]].
    split.
    + split; [exact hshape |]. split.
      * exact ((proj1 hext) left (hchildren left hleft)
          leftValue hleftLookup).
      * split.
        -- exact ((proj1 hext) right (hchildren right hright)
             rightValue hrightLookup).
        -- exact htruth.
    + repeat split; assumption.
  - right. right. right. right.
    destruct hor as
      [[hshape [hleftLookup [hrightLookup htruth]]]
       [hleftSupport [hrightSupport [hleft hright]]]].
    split.
    + split; [exact hshape |]. split.
      * exact ((proj1 hext) left (hchildren left hleft)
          leftValue hleftLookup).
      * split.
        -- exact ((proj1 hext) right (hchildren right hright)
             rightValue hrightLookup).
        -- exact htruth.
    + repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    Truth-table capacity is available in every PA model. *)

Definition RawRankZeroTruthCodingStep (M : RawPAModel)
    (bound step : M) : Prop :=
  RawCommonMultipleThrough M bound step /\
  rawLe M (raw_succ M (rawTruthOne M)) step.

Arguments RawRankZeroTruthCodingStep M bound step : clear implicits.

Lemma raw_sat_rankZeroTruthCodingStepTermAt_iff : forall
    (M : RawPAModel) e bound step,
  raw_formula_sat M e
    (Formula.betaCodingStepTermAt
      bound (Term.numeral 1) step) <->
  RawRankZeroTruthCodingStep M
    (raw_term_eval M e bound) (raw_term_eval M e step).
Proof.
  intros M e bound step.
  unfold Formula.betaCodingStepTermAt,
    RawRankZeroTruthCodingStep, rawTruthOne.
  cbn [raw_formula_sat].
  rewrite raw_sat_commonMultipleThroughTermAt_iff,
    raw_sat_leTermAt_iff_traversal.
  reflexivity.
Qed.

Theorem raw_rankZeroTruthCodingStep_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound : M,
  exists step : M, RawRankZeroTruthCodingStep M bound step.
Proof.
  intros M hPA bound.
  set (tail := fun _ : nat => raw_zero M).
  set (e := scons M bound tail).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (BProv_Ax_s_betaCodingStepExistsTermAt []
      (tVar 0) (Term.numeral 1)) e) as hsat.
  unfold Formula.betaCodingStepExistsTermAt in hsat.
  cbn [raw_formula_sat] in hsat.
  destruct hsat as [step hstep]. exists step.
  apply (proj1 (raw_sat_rankZeroTruthCodingStepTermAt_iff M
    (scons M step e)
    (Term.rename S (tVar 0)) (tVar 0))).
  exact hstep.
Qed.

Definition RawRankZeroTruthTableCapacity (M : RawPAModel)
    (bound step : M) : Prop :=
  RawCommonMultipleThrough M bound step /\
  forall target,
    rawLt M target bound ->
    rawLt M (rawTruthOne M) (rawBetaModulus M step target).

Arguments RawRankZeroTruthTableCapacity M bound step : clear implicits.

Theorem raw_rankZeroTruthTableCapacity_of_codingStep : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound step,
  RawRankZeroTruthCodingStep M bound step ->
  RawRankZeroTruthTableCapacity M bound step.
Proof.
  intros M hPA bound step [hcommon hlarge]. split; [exact hcommon |].
  intros target _.
  assert (honeStep : rawLt M (rawTruthOne M) step).
  {
    exact (raw_lt_le_trans_pair M hPA
      (rawTruthOne M) (raw_succ M (rawTruthOne M)) step
      (raw_assignment_lt_self_succ M hPA (rawTruthOne M)) hlarge).
  }
  assert (hstepProduct : rawLe M step
      (raw_mul M (raw_succ M target) step)).
  {
    exists (raw_mul M target step).
    rewrite raw_succ_mul by exact hPA.
    apply raw_add_comm. exact hPA.
  }
  assert (hstepModulus : rawLt M step
      (raw_succ M (raw_mul M (raw_succ M target) step))).
  { exact (raw_lt_succ_of_le M hPA _ _ hstepProduct). }
  unfold rawBetaModulus.
  exact (raw_assignment_lt_trans M hPA
    (rawTruthOne M) step _ honeStep hstepModulus).
Qed.

Corollary raw_rankZeroTruthTableCapacity_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound : M,
  exists step : M, RawRankZeroTruthTableCapacity M bound step.
Proof.
  intros M hPA bound.
  destruct (raw_rankZeroTruthCodingStep_exists M hPA bound)
    as [step hstep].
  exists step.
  exact (raw_rankZeroTruthTableCapacity_of_codingStep M hPA
    bound step hstep).
Qed.

(** ------------------------------------------------------------------
    One truth-table successor stage. *)

Lemma raw_rankZeroTruthTraversal_beta_extend : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall assignmentCode assignmentStep supportCode supportStep
    oldTruthCode newTruthCode truthStep current output,
  RawRankZeroTruthTraversal M current
    assignmentCode assignmentStep oldTruthCode truthStep
    supportCode supportStep ->
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (raw_succ M current) ->
  RawBetaCodeExtension M oldTruthCode truthStep
    current output newTruthCode ->
  (rawFormulaCodeSupported M supportCode supportStep current ->
    RawRankZeroTruthClosedStep M current output
      assignmentCode assignmentStep oldTruthCode truthStep
      supportCode supportStep) ->
  RawRankZeroTruthTraversal M (raw_succ M current)
    assignmentCode assignmentStep newTruthCode truthStep
    supportCode supportStep.
Proof.
  intros M hPA assignmentCode assignmentStep supportCode supportStep
    oldTruthCode newTruthCode truthStep current output
    [holdSupport [holdTruth holdRows]] hnewSupport hext hcurrentStep.
  split; [exact hnewSupport |]. split.
  - exact (raw_betaExtension_definedThrough_succ M hPA
      oldTruthCode newTruthCode truthStep current output holdTruth hext).
  - intros code hcode hsupported.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + destruct (holdRows code hbefore hsupported)
        as [oldOutput [hlookup hstep]].
      exists oldOutput. split.
      * exact ((proj1 hext) code hbefore oldOutput hlookup).
      * apply (raw_rankZeroTruthClosedStep_beta_extend M
          assignmentCode assignmentStep oldTruthCode newTruthCode
          truthStep supportCode supportStep current code output hext).
        -- intros child hchild.
           exact (raw_assignment_lt_trans M hPA
             child code current hchild hbefore).
        -- exact hstep.
    + exists output. split; [exact (proj2 hext) |].
      apply (raw_rankZeroTruthClosedStep_beta_extend M
        assignmentCode assignmentStep oldTruthCode newTruthCode
        truthStep supportCode supportStep current current output hext).
      * intros child hchild. exact hchild.
      * exact (hcurrentStep hsupported).
Qed.

Definition RawRankZeroTruthPrefixRealized (M : RawPAModel)
    (current assignmentCode assignmentStep truthStep
      supportCode supportStep : M) : Prop :=
  exists truthCode : M,
    RawRankZeroTruthTraversal M current
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep.

Arguments RawRankZeroTruthPrefixRealized
  M current assignmentCode assignmentStep truthStep supportCode supportStep
  : clear implicits.

Definition rankZeroTruthPrefixRealizedTermAt
    (current assignmentCode assignmentStep truthStep
      supportCode supportStep : term) : formula :=
  pEx
    (rankZeroTruthTraversalTermAt
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 truthStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep)).

Lemma raw_sat_rankZeroTruthPrefixRealizedTermAt_iff : forall
    (M : RawPAModel) e current assignmentCode assignmentStep truthStep
      supportCode supportStep,
  raw_formula_sat M e
    (rankZeroTruthPrefixRealizedTermAt current
      assignmentCode assignmentStep truthStep supportCode supportStep) <->
  RawRankZeroTruthPrefixRealized M
    (raw_term_eval M e current)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e current assignmentCode assignmentStep truthStep
    supportCode supportStep.
  unfold rankZeroTruthPrefixRealizedTermAt,
    RawRankZeroTruthPrefixRealized.
  cbn [raw_formula_sat]. split.
  - intros [truthCode htraversal]. exists truthCode.
    apply (proj1 (raw_sat_rankZeroTruthTraversalTermAt_iff M
      (scons M truthCode e)
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 truthStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))) in htraversal.
    rewrite !raw_term_eval_liftTerm_one_traversal in htraversal.
    cbn [raw_term_eval scons] in htraversal. exact htraversal.
  - intros [truthCode htraversal]. exists truthCode.
    apply (proj2 (raw_sat_rankZeroTruthTraversalTermAt_iff M
      (scons M truthCode e)
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 truthStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))).
    rewrite !raw_term_eval_liftTerm_one_traversal.
    cbn [raw_term_eval scons]. exact htraversal.
Qed.

Lemma raw_rankZeroTruthPrefixRealized_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall assignmentCode assignmentStep truthStep supportCode supportStep,
  RawRankZeroTruthPrefixRealized M (raw_zero M)
    assignmentCode assignmentStep truthStep supportCode supportStep.
Proof.
  intros M hPA assignmentCode assignmentStep truthStep supportCode supportStep.
  exists (raw_zero M). split.
  - intros index hindex. exfalso.
    exact (raw_not_lt_zero M hPA index hindex).
  - split.
    + intros index hindex. exfalso.
      exact (raw_not_lt_zero M hPA index hindex).
    + intros code hcode. exfalso.
      exact (raw_not_lt_zero M hPA code hcode).
Qed.

Theorem raw_rankZeroTruthPrefixRealized_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep
    truthStep current,
  RawRankZeroSyntaxTraversal M limit supportCode supportStep ->
  RawRankZeroSyntaxTermAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroTruthTableCapacity M limit truthStep ->
  rawLt M current limit ->
  RawRankZeroTruthPrefixRealized M current
    assignmentCode assignmentStep truthStep supportCode supportStep ->
  RawRankZeroTruthPrefixRealized M (raw_succ M current)
    assignmentCode assignmentStep truthStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    truthStep current hsyntax htermAdequate htermCapacity
    htruthCapacity hcurrent [oldTruthCode holdTraversal].
  destruct hsyntax as [hsupportDefined hsyntaxRows].
  destruct htruthCapacity as [hcommonLimit honeBound].
  assert (hnewSupport : RawCodedAssignmentDefinedThrough M
      supportCode supportStep (raw_succ M current)).
  {
    exact (raw_definedThrough_support_succ M hPA
      limit supportCode supportStep current hsupportDefined hcurrent).
  }
  destruct (hsupportDefined current hcurrent)
    as [supportValue hsupportValue].
  destruct (classic (supportValue = rawNumeralValue M 1))
    as [hsupportedValue | hnotSupported].
  - subst supportValue.
    pose proof hsupportValue as hcurrentSupported.
    pose proof (hsyntaxRows current hcurrent hcurrentSupported)
      as hsyntaxStep.
    destruct (raw_rankZeroSyntaxStep_truth_exists M hPA
      limit assignmentCode assignmentStep supportCode supportStep
      oldTruthCode truthStep current htermAdequate htermCapacity
      hcurrent hcurrentSupported holdTraversal hsyntaxStep)
      as [output hstep].
    pose proof (raw_rankZeroTruthClosedStep_output_bit M
      current output assignmentCode assignmentStep
      oldTruthCode truthStep supportCode supportStep hstep) as hbit.
    assert (hbound : rawLt M output
        (rawBetaModulus M truthStep current)).
    {
      destruct hbit as [-> | ->].
      - exact (raw_zero_lt_betaModulus M hPA truthStep current).
      - exact (honeBound current hcurrent).
    }
    assert (hcommon : RawCommonMultipleThrough M current truthStep).
    {
      exact (raw_commonMultipleThrough_weaken M hPA
        current limit truthStep hcurrent hcommonLimit).
    }
    destruct (raw_betaCodeExtension_exists M hPA oldTruthCode truthStep
      current output hcommon hbound) as [newTruthCode hext].
    exists newTruthCode.
    apply (raw_rankZeroTruthTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTruthCode newTruthCode truthStep current output).
    + exact holdTraversal.
    + exact hnewSupport.
    + exact hext.
    + intros _. exact hstep.
  - assert (hcommon : RawCommonMultipleThrough M current truthStep).
    {
      exact (raw_commonMultipleThrough_weaken M hPA
        current limit truthStep hcurrent hcommonLimit).
    }
    pose proof (raw_zero_lt_betaModulus M hPA truthStep current)
      as hzeroBound.
    destruct (raw_betaCodeExtension_exists M hPA oldTruthCode truthStep
      current (raw_zero M) hcommon hzeroBound)
      as [newTruthCode hext].
    exists newTruthCode.
    apply (raw_rankZeroTruthTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTruthCode newTruthCode truthStep current (raw_zero M)).
    + exact holdTraversal.
    + exact hnewSupport.
    + exact hext.
    + intros hsupported. exfalso. apply hnotSupported.
      exact (raw_codedAssignmentLookup_functional M hPA
        supportCode supportStep current
        supportValue (rawNumeralValue M 1)
        hsupportValue hsupported).
Qed.

(** ------------------------------------------------------------------
    PA-definable induction over the arbitrary truth bound. *)

Definition RawRankZeroTruthPrefixRealizedThrough (M : RawPAModel)
    (current limit assignmentCode assignmentStep truthStep
      supportCode supportStep : M) : Prop :=
  rawLe M current limit ->
  RawRankZeroTruthPrefixRealized M current
    assignmentCode assignmentStep truthStep supportCode supportStep.

Definition rankZeroTruthPrefixRealizedThroughTermAt
    (current limit assignmentCode assignmentStep truthStep
      supportCode supportStep : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (rankZeroTruthPrefixRealizedTermAt current
      assignmentCode assignmentStep truthStep supportCode supportStep).

Lemma raw_sat_rankZeroTruthPrefixRealizedThroughTermAt_iff : forall
    (M : RawPAModel) e current limit assignmentCode assignmentStep
      truthStep supportCode supportStep,
  raw_formula_sat M e
    (rankZeroTruthPrefixRealizedThroughTermAt current limit
      assignmentCode assignmentStep truthStep supportCode supportStep) <->
  RawRankZeroTruthPrefixRealizedThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e truthStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold rankZeroTruthPrefixRealizedThroughTermAt,
    RawRankZeroTruthPrefixRealizedThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_rankZeroTruthPrefixRealizedTermAt_iff.
  tauto.
Qed.

Theorem raw_rankZeroTruthPrefixRealized_through_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep
    truthStep,
  RawRankZeroSyntaxTraversal M limit supportCode supportStep ->
  RawRankZeroSyntaxTermAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroTruthTableCapacity M limit truthStep ->
  forall current,
  RawRankZeroTruthPrefixRealizedThrough M current limit
    assignmentCode assignmentStep truthStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    truthStep hsyntax htermAdequate htermCapacity htruthCapacity.
  set (parameterEnv := scons M limit
    (scons M assignmentCode (scons M assignmentStep
      (scons M truthStep (scons M supportCode
        (scons M supportStep (fun _ : nat => raw_zero M))))))).
  set (phi := rankZeroTruthPrefixRealizedThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_rankZeroTruthPrefixRealizedThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _.
      exact (raw_rankZeroTruthPrefixRealized_zero M hPA
        assignmentCode assignmentStep truthStep supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_rankZeroTruthPrefixRealizedThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6)) hcurrentSat) as hcurrentRaw.
      apply (proj2
        (raw_sat_rankZeroTruthPrefixRealizedThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      { exact (raw_lt_of_succ_le_traversal M hPA current limit hsuccLe). }
      apply (raw_rankZeroTruthPrefixRealized_succ M hPA
        limit assignmentCode assignmentStep supportCode supportStep
        truthStep current hsyntax htermAdequate htermCapacity
        htruthCapacity hcurrentLimit).
      apply hcurrentRaw.
      exact (raw_lt_to_le M current limit hcurrentLimit).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_rankZeroTruthPrefixRealizedThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3)
      (tVar 4) (tVar 5) (tVar 6)) (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** ------------------------------------------------------------------
    Conditional nonstandard totality and uniqueness. *)

Theorem raw_rankZeroTruthCertificateWithTables_exists_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep ->
  exists output truthCode truthStep : M,
    RawRankZeroTruthCertificateWithTables M
      root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    [hsyntax [htermAdequate hrootSupport]] htermCapacity.
  destruct (raw_rankZeroTruthTableCapacity_exists M hPA
    (raw_succ M root)) as [truthStep htruthCapacity].
  pose proof (raw_rankZeroTruthPrefixRealized_through_all M hPA
    (raw_succ M root) assignmentCode assignmentStep
    supportCode supportStep truthStep
    hsyntax htermAdequate htermCapacity htruthCapacity
    (raw_succ M root)) as hprefix.
  specialize (hprefix (raw_le_refl_traversal M hPA (raw_succ M root))).
  destruct hprefix as [truthCode htraversal].
  destruct htraversal as [hsupport [htruth hrows]].
  destruct (hrows root (raw_assignment_lt_self_succ M hPA root)
    hrootSupport) as [output [hrootLookup hrootStep]].
  exists output, truthCode, truthStep.
  split.
  - repeat split; assumption.
  - split; [exact hrootSupport |]. split; [exact hrootLookup |].
    exact (raw_rankZeroTruthClosedStep_output_bit M
      root output assignmentCode assignmentStep
      truthCode truthStep supportCode supportStep hrootStep).
Qed.

Corollary raw_rankZeroTruthCertificate_exists_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity.
  destruct
    (raw_rankZeroTruthCertificateWithTables_exists_of_syntax_capacity
      M hPA root assignmentCode assignmentStep supportCode supportStep
      hsyntax hcapacity) as [output [truthCode [truthStep hcertificate]]].
  exists output, supportCode, supportStep, truthCode, truthStep.
  exact hcertificate.
Qed.

Corollary raw_rankZeroTruthCertificate_exists_unique_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawRankZeroSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawRankZeroAtomicTermCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep ->
  exists output : M,
    RawRankZeroTruthCertificate M
      root output assignmentCode assignmentStep /\
    forall otherOutput,
      RawRankZeroTruthCertificate M
        root otherOutput assignmentCode assignmentStep ->
      output = otherOutput.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity.
  destruct (raw_rankZeroTruthCertificate_exists_of_syntax_capacity
    M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity) as [output houtput].
  exists output. split; [exact houtput |].
  intros otherOutput hother.
  exact (raw_rankZeroTruthCertificate_output_functional M hPA
    root assignmentCode assignmentStep output otherOutput houtput hother).
Qed.

(** Public semantic admissibility packages a syntax/support witness together
    with exactly the inherited term-capacity condition. *)
Definition RawRankZeroTruthAdmissible (M : RawPAModel)
    (root assignmentCode assignmentStep : M) : Prop :=
  exists supportCode supportStep : M,
    RawRankZeroSyntaxCertificateWithSupport M
      root assignmentCode assignmentStep supportCode supportStep /\
    RawRankZeroAtomicTermCapacity M (raw_succ M root)
      assignmentCode assignmentStep supportCode supportStep.

Arguments RawRankZeroTruthAdmissible
  M root assignmentCode assignmentStep : clear implicits.

Theorem raw_rankZeroTruthCertificate_totality_for_admissible : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRankZeroTruthCertificateTotalityFor M
    (RawRankZeroTruthAdmissible M).
Proof.
  intros M hPA root assignmentCode assignmentStep
    [supportCode [supportStep [hsyntax hcapacity]]].
  exact (raw_rankZeroTruthCertificate_exists_of_syntax_capacity
    M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity).
Qed.

End PABoundedRawCodedRankZeroTruthRealization.
