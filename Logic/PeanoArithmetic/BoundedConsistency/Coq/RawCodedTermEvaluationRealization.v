(**
  Model-internal realization of beta-coded term evaluation traversals.

  A carrier element of a nonstandard PA model cannot be decoded by Rocq.
  Accordingly, the input below is not an external [term].  It is a genuine
  first-order certificate saying that every supported code has one of the
  five term-constructor shapes, and that recursive children are supported
  at strictly smaller codes.  Variable rows are handled by a second genuine
  first-order condition saying that the supplied beta-coded environment is
  defined at every supported variable index.

  The construction then uses PA induction on the (possibly nonstandard)
  code bound.  At one successor stage, Goedel-beta CRT extension preserves
  every earlier value-table entry and appends the locally computed value.
  There is one honest arithmetic boundary: the chosen fixed beta step must
  be a common multiple through the bound and its target modulus must exceed
  each locally computed value.  [RawTermEvaluationFixedStepCapacity] states
  exactly that condition.  No totality or capacity assertion is postulated.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedTermEvaluationStep RawCodedTermEvaluationTraversal.

Import ListNotations.

Module PABoundedRawCodedTermEvaluationRealization.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedTermEvaluationStep.
Import PABoundedRawCodedTermEvaluationTraversal.

(** ------------------------------------------------------------------
    Model-internal syntax closure. *)

Definition RawTermSyntaxWitnessRow (M : RawPAModel)
    (code supportCode supportStep left right : M) : Prop :=
  code = rawTermVarCode M left \/
  code = rawTermZeroCode M \/
  (code = rawTermSuccCode M left /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawLt M left code) \/
  (code = rawTermAddCode M left right /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawTermCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code) \/
  (code = rawTermMulCode M left right /\
    rawTermCodeSupported M supportCode supportStep left /\
    rawTermCodeSupported M supportCode supportStep right /\
    rawLt M left code /\ rawLt M right code).

Arguments RawTermSyntaxWitnessRow
  M code supportCode supportStep left right : clear implicits.

Definition termSyntaxWitnessRowTermAt
    (code supportCode supportStep left right : term) : formula :=
  pOr
    (termVarCodeTermAt code left)
    (pOr
      (termZeroCodeTermAt code)
      (pOr
        (pAnd3
          (termSuccCodeTermAt code left)
          (termCodeSupportedTermAt supportCode supportStep left)
          (Formula.ltTermAt left code))
        (pOr
          (pAnd
            (termAddCodeTermAt code left right)
            (pAnd4
              (termCodeSupportedTermAt supportCode supportStep left)
              (termCodeSupportedTermAt supportCode supportStep right)
              (Formula.ltTermAt left code)
              (Formula.ltTermAt right code)))
          (pAnd
            (termMulCodeTermAt code left right)
            (pAnd4
              (termCodeSupportedTermAt supportCode supportStep left)
              (termCodeSupportedTermAt supportCode supportStep right)
              (Formula.ltTermAt left code)
              (Formula.ltTermAt right code)))))).

Lemma raw_sat_termSyntaxWitnessRowTermAt_iff : forall
    (M : RawPAModel) e code supportCode supportStep left right,
  raw_formula_sat M e
    (termSyntaxWitnessRowTermAt
      code supportCode supportStep left right) <->
  RawTermSyntaxWitnessRow M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold termSyntaxWitnessRowTermAt,
    RawTermSyntaxWitnessRow, pAnd3, pAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_termVarCodeTermAt_iff,
    raw_sat_termZeroCodeTermAt_iff,
    raw_sat_termSuccCodeTermAt_iff,
    raw_sat_termAddCodeTermAt_iff,
    raw_sat_termMulCodeTermAt_iff,
    !raw_sat_termCodeSupportedTermAt_iff,
    !raw_sat_ltTermAt_iff.
  tauto.
Qed.

Definition termSyntaxStepTermAt
    (code supportCode supportStep : term) : formula :=
  pEx (pEx
    (termSyntaxWitnessRowTermAt
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))).

Definition RawTermSyntaxStep (M : RawPAModel)
    (code supportCode supportStep : M) : Prop :=
  exists left right : M,
    RawTermSyntaxWitnessRow M code supportCode supportStep left right.

Arguments RawTermSyntaxStep M code supportCode supportStep
  : clear implicits.

Lemma raw_sat_termSyntaxStepTermAt_iff : forall
    (M : RawPAModel) e code supportCode supportStep,
  raw_formula_sat M e
    (termSyntaxStepTermAt code supportCode supportStep) <->
  RawTermSyntaxStep M
    (raw_term_eval M e code)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e code supportCode supportStep.
  unfold termSyntaxStepTermAt, RawTermSyntaxStep.
  cbn [raw_formula_sat]. split.
  - intros [left [right hrow]]. exists left, right.
    apply (proj1 (raw_sat_termSyntaxWitnessRowTermAt_iff M
      (scons M right (scons M left e))
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))) in hrow.
    rewrite !raw_term_eval_liftTerm_two_traversal in hrow.
    cbn [raw_term_eval scons] in hrow. exact hrow.
  - intros [left [right hrow]]. exists left, right.
    apply (proj2 (raw_sat_termSyntaxWitnessRowTermAt_iff M
      (scons M right (scons M left e))
      (liftTerm 2 code) (liftTerm 2 supportCode) (liftTerm 2 supportStep)
      (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_two_traversal.
    cbn [raw_term_eval scons]. exact hrow.
Qed.

Definition RawTermSyntaxTraversal (M : RawPAModel)
    (bound supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep bound /\
  forall code,
    rawLt M code bound ->
    rawTermCodeSupported M supportCode supportStep code ->
    RawTermSyntaxStep M code supportCode supportStep.

Arguments RawTermSyntaxTraversal M bound supportCode supportStep
  : clear implicits.

Definition termSyntaxTraversalTermAt
    (bound supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep bound)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
        (pImp
          (termCodeSupportedTermAt
            (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
          (termSyntaxStepTermAt
            (tVar 0) (liftTerm 1 supportCode) (liftTerm 1 supportStep))))).

Lemma raw_sat_termSyntaxTraversalTermAt_iff : forall
    (M : RawPAModel) e bound supportCode supportStep,
  raw_formula_sat M e
    (termSyntaxTraversalTermAt bound supportCode supportStep) <->
  RawTermSyntaxTraversal M
    (raw_term_eval M e bound)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound supportCode supportStep.
  unfold termSyntaxTraversalTermAt, RawTermSyntaxTraversal.
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
    assert (hsupportedSat : raw_formula_sat M (scons M code e)
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    pose proof (hrows code hltSat hsupportedSat) as hstepSat.
    apply (proj1 (raw_sat_termSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))) in hstepSat.
    rewrite !raw_term_eval_liftTerm_one_traversal in hstepSat.
    cbn [raw_term_eval scons] in hstepSat. exact hstepSat.
  - intros [hdefined hrows]. split; [exact hdefined |].
    intros code hcodeSat hsupportedSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hcodeSat)
      as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)
      hsupportedSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    apply (proj2 (raw_sat_termSyntaxStepTermAt_iff M
      (scons M code e) (tVar 0)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))).
    rewrite !raw_term_eval_liftTerm_one_traversal.
    cbn [raw_term_eval scons].
    exact (hrows code hcode hsupported).
Qed.

(** Assignment adequacy is deliberately independent of syntax closure.  It
    says only that a supported variable row can read its de Bruijn index. *)
Definition RawTermSyntaxAssignmentAdequate (M : RawPAModel)
    (bound assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  forall code,
    rawLt M code bound ->
    rawTermCodeSupported M supportCode supportStep code ->
    forall index,
      code = rawTermVarCode M index ->
      exists value,
        RawCodedAssignmentLookup M
          assignmentCode assignmentStep index value.

Arguments RawTermSyntaxAssignmentAdequate
  M bound assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Definition termSyntaxAssignmentAdequateTermAt
    (bound assignmentCode assignmentStep supportCode supportStep : term)
    : formula :=
  pAll
    (pImp
      (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))
      (pImp
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
        (pAll
          (pImp
            (termVarCodeTermAt (tVar 1) (tVar 0))
            (pEx
              (codedAssignmentLookupTermAt
                (liftTerm 3 assignmentCode) (liftTerm 3 assignmentStep)
                (tVar 1) (tVar 0))))))).

Lemma raw_sat_termSyntaxAssignmentAdequateTermAt_iff : forall
    (M : RawPAModel) e bound assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (termSyntaxAssignmentAdequateTermAt
      bound assignmentCode assignmentStep supportCode supportStep) <->
  RawTermSyntaxAssignmentAdequate M
    (raw_term_eval M e bound)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e bound assignmentCode assignmentStep supportCode supportStep.
  unfold termSyntaxAssignmentAdequateTermAt,
    RawTermSyntaxAssignmentAdequate.
  cbn [raw_formula_sat]. split.
  - intros h code hcode hsupported index hvar.
    assert (hltSat : raw_formula_sat M (scons M code e)
        (Formula.ltTermAt (tVar 0) (liftTerm 1 bound))).
    {
      apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hcode.
    }
    assert (hsupportSat : raw_formula_sat M (scons M code e)
        (termCodeSupportedTermAt
          (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))).
    {
      apply (proj2 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)).
      rewrite !raw_term_eval_liftTerm_one_traversal.
      cbn [raw_term_eval scons]. exact hsupported.
    }
    assert (hvarSat : raw_formula_sat M
        (scons M index (scons M code e))
        (termVarCodeTermAt (tVar 1) (tVar 0))).
    {
      apply (proj2 (raw_sat_termVarCodeTermAt_iff M _ _ _)).
      cbn [raw_term_eval scons]. exact hvar.
    }
    destruct (h code hltSat hsupportSat index hvarSat)
      as [value hlookup].
    exists value.
    apply (proj1 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _))
      in hlookup.
    rewrite !raw_term_eval_liftTerm_three_traversal in hlookup.
    cbn [raw_term_eval scons] in hlookup. exact hlookup.
  - intros h code hltSat hsupportSat index hvarSat.
    pose proof (proj1 (raw_sat_ltTermAt_iff M _ _ _) hltSat) as hcode.
    rewrite raw_term_eval_liftTerm_one_traversal in hcode.
    cbn [raw_term_eval scons] in hcode.
    pose proof (proj1 (raw_sat_termCodeSupportedTermAt_iff M _ _ _ _)
      hsupportSat) as hsupported.
    rewrite !raw_term_eval_liftTerm_one_traversal in hsupported.
    cbn [raw_term_eval scons] in hsupported.
    pose proof (proj1 (raw_sat_termVarCodeTermAt_iff M _ _ _)
      hvarSat) as hvar.
    cbn [raw_term_eval scons] in hvar.
    destruct (h code hcode hsupported index hvar) as [value hlookup].
    exists value.
    apply (proj2 (raw_sat_codedAssignmentLookupTermAt_iff M _ _ _ _ _)).
    rewrite !raw_term_eval_liftTerm_three_traversal.
    cbn [raw_term_eval scons]. exact hlookup.
Qed.

(** A root syntax certificate combines closure, assignment adequacy, and the
    assertion that the root itself is supported. *)
Definition RawTermSyntaxCertificateWithSupport (M : RawPAModel)
    (root assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  RawTermSyntaxTraversal M (raw_succ M root) supportCode supportStep /\
  RawTermSyntaxAssignmentAdequate M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep /\
  rawTermCodeSupported M supportCode supportStep root.

Arguments RawTermSyntaxCertificateWithSupport
  M root assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Definition termSyntaxCertificateWithSupportTermAt
    (root assignmentCode assignmentStep supportCode supportStep : term)
    : formula :=
  pAnd3
    (termSyntaxTraversalTermAt
      (tSucc root) supportCode supportStep)
    (termSyntaxAssignmentAdequateTermAt
      (tSucc root) assignmentCode assignmentStep supportCode supportStep)
    (termCodeSupportedTermAt supportCode supportStep root).

Lemma raw_sat_termSyntaxCertificateWithSupportTermAt_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep
      supportCode supportStep,
  raw_formula_sat M e
    (termSyntaxCertificateWithSupportTermAt
      root assignmentCode assignmentStep supportCode supportStep) <->
  RawTermSyntaxCertificateWithSupport M
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termSyntaxCertificateWithSupportTermAt,
    RawTermSyntaxCertificateWithSupport, pAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_termSyntaxTraversalTermAt_iff,
    raw_sat_termSyntaxAssignmentAdequateTermAt_iff,
    raw_sat_termCodeSupportedTermAt_iff.
  reflexivity.
Qed.

(** Existentially hiding the support table gives the public arithmetized
    domain of model-internal term syntax.  This is not asserted for every
    carrier element. *)
Definition termSyntaxRealizableTermAt
    (root assignmentCode assignmentStep : term) : formula :=
  pEx (pEx
    (termSyntaxCertificateWithSupportTermAt
      (liftTerm 2 root) (liftTerm 2 assignmentCode)
      (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))).

Definition RawTermSyntaxRealizable (M : RawPAModel)
    (root assignmentCode assignmentStep : M) : Prop :=
  exists supportCode supportStep : M,
    RawTermSyntaxCertificateWithSupport M
      root assignmentCode assignmentStep supportCode supportStep.

Arguments RawTermSyntaxRealizable
  M root assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_termSyntaxRealizableTermAt_iff : forall
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
    (termSyntaxRealizableTermAt root assignmentCode assignmentStep) <->
  RawTermSyntaxRealizable M
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros M e root assignmentCode assignmentStep.
  unfold termSyntaxRealizableTermAt, RawTermSyntaxRealizable.
  cbn [raw_formula_sat]. split.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj1 (raw_sat_termSyntaxCertificateWithSupportTermAt_iff M
      (scons M supportStep (scons M supportCode e))
      (liftTerm 2 root) (liftTerm 2 assignmentCode)
      (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))) in hsyntax.
    rewrite !raw_term_eval_liftTerm_two_traversal in hsyntax.
    cbn [raw_term_eval scons] in hsyntax. exact hsyntax.
  - intros [supportCode [supportStep hsyntax]].
    exists supportCode, supportStep.
    apply (proj2 (raw_sat_termSyntaxCertificateWithSupportTermAt_iff M
      (scons M supportStep (scons M supportCode e))
      (liftTerm 2 root) (liftTerm 2 assignmentCode)
      (liftTerm 2 assignmentStep) (tVar 1) (tVar 0))).
    rewrite !raw_term_eval_liftTerm_two_traversal.
    cbn [raw_term_eval scons]. exact hsyntax.
Qed.

(** ------------------------------------------------------------------
    Local realization and beta-table preservation. *)

Lemma raw_termSyntaxStep_evaluation_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall bound assignmentCode assignmentStep supportCode supportStep
    tableCode tableStep code,
  RawTermSyntaxAssignmentAdequate M bound
    assignmentCode assignmentStep supportCode supportStep ->
  rawLt M code bound ->
  rawTermCodeSupported M supportCode supportStep code ->
  RawCodedAssignmentDefinedThrough M tableCode tableStep code ->
  RawTermSyntaxStep M code supportCode supportStep ->
  exists value,
    RawTermEvaluationClosedStep M code value
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.
Proof.
  intros M hPA bound assignmentCode assignmentStep supportCode supportStep
    tableCode tableStep code hadequate hcode hsupported htable
    [left [right hshape]].
  destruct hshape as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - destruct (hadequate code hcode hsupported left hvar)
      as [value hlookup].
    exists value, left, (raw_zero M), (raw_zero M), (raw_zero M).
    left. split; assumption.
  - exists (raw_zero M), (raw_zero M), (raw_zero M),
      (raw_zero M), (raw_zero M).
    right. left. split; [exact hzero | reflexivity].
  - destruct hsucc as [hshape [hchildSupport hchild]].
    destruct (htable left hchild) as [childValue hchildValue].
    exists (raw_succ M childValue), left, childValue,
      (raw_zero M), (raw_zero M).
    right. right. left. split.
    + split; [exact hshape |]. split; [exact hchildValue | reflexivity].
    + split; assumption.
  - destruct hadd as
      [hshape [hleftSupport [hrightSupport [hleft hright]]]].
    destruct (htable left hleft) as [leftValue hleftValue].
    destruct (htable right hright) as [rightValue hrightValue].
    exists (raw_add M leftValue rightValue),
      left, leftValue, right, rightValue.
    right. right. right. left. split.
    + split; [exact hshape |].
      split; [exact hleftValue |]. split; [exact hrightValue | reflexivity].
    + repeat split; assumption.
  - destruct hmul as
      [hshape [hleftSupport [hrightSupport [hleft hright]]]].
    destruct (htable left hleft) as [leftValue hleftValue].
    destruct (htable right hright) as [rightValue hrightValue].
    exists (raw_mul M leftValue rightValue),
      left, leftValue, right, rightValue.
    right. right. right. right. split.
    + split; [exact hshape |].
      split; [exact hleftValue |]. split; [exact hrightValue | reflexivity].
    + repeat split; assumption.
Qed.

(** A local row mentions the value table only at recursive children.  Thus a
    beta extension transports the row whenever all of those children lie
    below the extension target. *)
Lemma raw_termEvaluationClosedStep_beta_extend : forall
    (M : RawPAModel) assignmentCode assignmentStep
      oldTableCode newTableCode tableStep supportCode supportStep
      target code value,
  RawBetaCodeExtension M oldTableCode tableStep target value newTableCode ->
  (forall child, rawLt M child code -> rawLt M child target) ->
  forall output,
  RawTermEvaluationClosedStep M code output
    assignmentCode assignmentStep oldTableCode tableStep
    supportCode supportStep ->
  RawTermEvaluationClosedStep M code output
    assignmentCode assignmentStep newTableCode tableStep
    supportCode supportStep.
Proof.
  intros M assignmentCode assignmentStep oldTableCode newTableCode
    tableStep supportCode supportStep target code value hext hchildren
    output [left [leftValue [right [rightValue hrow]]]].
  exists left, leftValue, right, rightValue.
  destruct hrow as [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as [[hshape [hlookup hvalue]] [hsupport hlt]].
    split.
    + split; [exact hshape |]. split; [|exact hvalue].
      exact ((proj1 hext) left (hchildren left hlt) leftValue hlookup).
    + split; assumption.
  - right. right. right. left.
    destruct hadd as
      [[hshape [hleftLookup [hrightLookup hvalue]]]
       [hleftSupport [hrightSupport [hleft hright]]]].
    split.
    + split; [exact hshape |]. split.
      * exact ((proj1 hext) left (hchildren left hleft)
          leftValue hleftLookup).
      * split.
        -- exact ((proj1 hext) right (hchildren right hright)
             rightValue hrightLookup).
        -- exact hvalue.
    + repeat split; assumption.
  - right. right. right. right.
    destruct hmul as
      [[hshape [hleftLookup [hrightLookup hvalue]]]
       [hleftSupport [hrightSupport [hleft hright]]]].
    split.
    + split; [exact hshape |]. split.
      * exact ((proj1 hext) left (hchildren left hleft)
          leftValue hleftLookup).
      * split.
        -- exact ((proj1 hext) right (hchildren right hright)
             rightValue hrightLookup).
        -- exact hvalue.
    + repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    The exact CRT capacity boundary. *)

(** [RawCodedTermEvaluationTraversal] also exposes a paired support/value
    append operation.  Here the support table is already the independently
    certified syntax oracle for the *whole* nonstandard bound, so replacing
    it at each stage would lose its still-unvisited entries.  We therefore
    keep that table fixed and use precisely the value-table half of the same
    underlying [RawBetaCodeExtension] API. *)

Definition RawTermEvaluationFixedStepCapacity (M : RawPAModel)
    (limit assignmentCode assignmentStep supportCode supportStep tableStep
      : M) : Prop :=
  RawCommonMultipleThrough M limit tableStep /\
  forall target tableCode value,
    rawLt M target limit ->
    RawTermEvaluationTraversal M target
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep ->
    rawTermCodeSupported M supportCode supportStep target ->
    RawTermEvaluationClosedStep M target value
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep ->
    rawLt M value (rawBetaModulus M tableStep target).

Arguments RawTermEvaluationFixedStepCapacity
  M limit assignmentCode assignmentStep supportCode supportStep tableStep
  : clear implicits.

Definition RawTermEvaluationRealizationCapacity (M : RawPAModel)
    (limit assignmentCode assignmentStep supportCode supportStep : M)
    : Prop :=
  exists tableStep : M,
    RawTermEvaluationFixedStepCapacity M limit
      assignmentCode assignmentStep supportCode supportStep tableStep.

Arguments RawTermEvaluationRealizationCapacity
  M limit assignmentCode assignmentStep supportCode supportStep
  : clear implicits.

Lemma raw_commonMultipleThrough_weaken : forall (M : RawPAModel),
  RawPASatisfies M -> forall small large multiple,
  rawLt M small large ->
  RawCommonMultipleThrough M large multiple ->
  RawCommonMultipleThrough M small multiple.
Proof.
  intros M hPA small large multiple hsmall hcommon index hindex.
  apply hcommon.
  exact (raw_assignment_lt_trans M hPA index small large hindex hsmall).
Qed.

Lemma raw_zero_le_realization : forall (M : RawPAModel),
  RawPASatisfies M -> forall x, rawLe M (raw_zero M) x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_zero_left [] (tVar 0)) e) as hle.
  change (rawLe M (raw_zero M) x) in hle. exact hle.
Qed.

Lemma raw_zero_lt_betaModulus : forall (M : RawPAModel),
  RawPASatisfies M -> forall step target,
  rawLt M (raw_zero M) (rawBetaModulus M step target).
Proof.
  intros M hPA step target. unfold rawBetaModulus.
  apply raw_lt_succ_of_le; [exact hPA |].
  apply raw_zero_le_realization. exact hPA.
Qed.

(** ------------------------------------------------------------------
    One successor stage. *)

Lemma raw_definedThrough_support_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall limit supportCode supportStep current,
  RawCodedAssignmentDefinedThrough M supportCode supportStep limit ->
  rawLt M current limit ->
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (raw_succ M current).
Proof.
  intros M hPA limit supportCode supportStep current hdefined hcurrent
    index hindex.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbefore | ->].
  - apply hdefined.
    exact (raw_assignment_lt_trans M hPA
      index current limit hbefore hcurrent).
  - apply hdefined. exact hcurrent.
Qed.

Lemma raw_betaExtension_definedThrough_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall oldCode newCode step current value,
  RawCodedAssignmentDefinedThrough M oldCode step current ->
  RawBetaCodeExtension M oldCode step current value newCode ->
  RawCodedAssignmentDefinedThrough M newCode step (raw_succ M current).
Proof.
  intros M hPA oldCode newCode step current value hdefined hext
    index hindex.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbefore | ->].
  - destruct (hdefined index hbefore) as [out hout].
    exists out. exact ((proj1 hext) index hbefore out hout).
  - exists value. exact (proj2 hext).
Qed.

Lemma raw_termEvaluationTraversal_beta_extend : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall assignmentCode assignmentStep supportCode supportStep
    oldTableCode newTableCode tableStep current value,
  RawTermEvaluationTraversal M current
    assignmentCode assignmentStep oldTableCode tableStep
    supportCode supportStep ->
  RawCodedAssignmentDefinedThrough M supportCode supportStep
    (raw_succ M current) ->
  RawBetaCodeExtension M oldTableCode tableStep current value newTableCode ->
  (rawTermCodeSupported M supportCode supportStep current ->
    RawTermEvaluationClosedStep M current value
      assignmentCode assignmentStep oldTableCode tableStep
      supportCode supportStep) ->
  RawTermEvaluationTraversal M (raw_succ M current)
    assignmentCode assignmentStep newTableCode tableStep
    supportCode supportStep.
Proof.
  intros M hPA assignmentCode assignmentStep supportCode supportStep
    oldTableCode newTableCode tableStep current value
    [holdSupport [holdTable holdRows]] hnewSupport hext hcurrentStep.
  split; [exact hnewSupport |]. split.
  - exact (raw_betaExtension_definedThrough_succ M hPA
      oldTableCode newTableCode tableStep current value holdTable hext).
  - intros code hcode hsupported.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + destruct (holdRows code hbefore hsupported)
        as [output [hlookup hstep]].
      exists output. split.
      * exact ((proj1 hext) code hbefore output hlookup).
      * apply (raw_termEvaluationClosedStep_beta_extend M
          assignmentCode assignmentStep oldTableCode newTableCode
          tableStep supportCode supportStep current code value hext).
        -- intros child hchild.
           exact (raw_assignment_lt_trans M hPA
             child code current hchild hbefore).
        -- exact hstep.
    + exists value. split; [exact (proj2 hext) |].
      apply (raw_termEvaluationClosedStep_beta_extend M
        assignmentCode assignmentStep oldTableCode newTableCode
        tableStep supportCode supportStep current current value hext).
      * intros child hchild. exact hchild.
      * exact (hcurrentStep hsupported).
Qed.

Definition RawTermEvaluationPrefixRealized (M : RawPAModel)
    (current assignmentCode assignmentStep tableStep
      supportCode supportStep : M) : Prop :=
  exists tableCode : M,
    RawTermEvaluationTraversal M current
      assignmentCode assignmentStep tableCode tableStep
      supportCode supportStep.

Arguments RawTermEvaluationPrefixRealized
  M current assignmentCode assignmentStep tableStep supportCode supportStep
  : clear implicits.

Definition termEvaluationPrefixRealizedTermAt
    (current assignmentCode assignmentStep tableStep
      supportCode supportStep : term) : formula :=
  pEx
    (termEvaluationTraversalTermAt
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 tableStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep)).

Lemma raw_sat_termEvaluationPrefixRealizedTermAt_iff : forall
    (M : RawPAModel) e current assignmentCode assignmentStep tableStep
      supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationPrefixRealizedTermAt current
      assignmentCode assignmentStep tableStep supportCode supportStep) <->
  RawTermEvaluationPrefixRealized M
    (raw_term_eval M e current)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros M e current assignmentCode assignmentStep tableStep
    supportCode supportStep.
  unfold termEvaluationPrefixRealizedTermAt,
    RawTermEvaluationPrefixRealized.
  cbn [raw_formula_sat]. split.
  - intros [tableCode htraversal]. exists tableCode.
    apply (proj1 (raw_sat_termEvaluationTraversalTermAt_iff M
      (scons M tableCode e)
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 tableStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))) in htraversal.
    rewrite !raw_term_eval_liftTerm_one_traversal in htraversal.
    cbn [raw_term_eval scons] in htraversal. exact htraversal.
  - intros [tableCode htraversal]. exists tableCode.
    apply (proj2 (raw_sat_termEvaluationTraversalTermAt_iff M
      (scons M tableCode e)
      (liftTerm 1 current)
      (liftTerm 1 assignmentCode) (liftTerm 1 assignmentStep)
      (tVar 0) (liftTerm 1 tableStep)
      (liftTerm 1 supportCode) (liftTerm 1 supportStep))).
    rewrite !raw_term_eval_liftTerm_one_traversal.
    cbn [raw_term_eval scons]. exact htraversal.
Qed.

Lemma raw_termEvaluationPrefixRealized_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall assignmentCode assignmentStep tableStep supportCode supportStep,
  RawTermEvaluationPrefixRealized M (raw_zero M)
    assignmentCode assignmentStep tableStep supportCode supportStep.
Proof.
  intros M hPA assignmentCode assignmentStep tableStep supportCode supportStep.
  exists (raw_zero M). split.
  - intros index hindex. exfalso.
    exact (raw_not_lt_zero M hPA index hindex).
  - split.
    + intros index hindex. exfalso.
      exact (raw_not_lt_zero M hPA index hindex).
    + intros code hcode. exfalso.
      exact (raw_not_lt_zero M hPA code hcode).
Qed.

Theorem raw_termEvaluationPrefixRealized_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep
    tableStep current,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationFixedStepCapacity M limit
    assignmentCode assignmentStep supportCode supportStep tableStep ->
  rawLt M current limit ->
  RawTermEvaluationPrefixRealized M current
    assignmentCode assignmentStep tableStep supportCode supportStep ->
  RawTermEvaluationPrefixRealized M (raw_succ M current)
    assignmentCode assignmentStep tableStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    tableStep current hsyntax hadequate hcapacity hcurrent
    [oldTableCode holdTraversal].
  destruct hsyntax as [hsupportDefined hsyntaxRows].
  destruct hcapacity as [hcommonLimit hvalueBound].
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
    destruct holdTraversal as
      [holdSupport [holdTable holdRows]].
    destruct (raw_termSyntaxStep_evaluation_exists M hPA
      limit assignmentCode assignmentStep supportCode supportStep
      oldTableCode tableStep current hadequate hcurrent
      hcurrentSupported holdTable hsyntaxStep) as [value hstep].
    assert (hbound : rawLt M value
        (rawBetaModulus M tableStep current)).
    {
      apply (hvalueBound current oldTableCode value hcurrent).
      - repeat split; assumption.
      - exact hcurrentSupported.
      - exact hstep.
    }
    assert (hcommon : RawCommonMultipleThrough M current tableStep).
    {
      exact (raw_commonMultipleThrough_weaken M hPA
        current limit tableStep hcurrent hcommonLimit).
    }
    destruct (raw_betaCodeExtension_exists M hPA oldTableCode tableStep
      current value hcommon hbound) as [newTableCode hext].
    exists newTableCode.
    apply (raw_termEvaluationTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTableCode newTableCode tableStep current value).
    + repeat split; assumption.
    + exact hnewSupport.
    + exact hext.
    + intros _. exact hstep.
  - assert (hcommon : RawCommonMultipleThrough M current tableStep).
    {
      exact (raw_commonMultipleThrough_weaken M hPA
        current limit tableStep hcurrent hcommonLimit).
    }
    pose proof (raw_zero_lt_betaModulus M hPA tableStep current)
      as hzeroBound.
    destruct (raw_betaCodeExtension_exists M hPA oldTableCode tableStep
      current (raw_zero M) hcommon hzeroBound)
      as [newTableCode hext].
    exists newTableCode.
    apply (raw_termEvaluationTraversal_beta_extend M hPA
      assignmentCode assignmentStep supportCode supportStep
      oldTableCode newTableCode tableStep current (raw_zero M)).
    + exact holdTraversal.
    + exact hnewSupport.
    + exact hext.
    + intros hsupported.
      exfalso. apply hnotSupported.
      exact (raw_codedAssignmentLookup_functional M hPA
        supportCode supportStep current
        supportValue (rawNumeralValue M 1)
        hsupportValue hsupported).
Qed.

(** ------------------------------------------------------------------
    Genuine PA induction through the nonstandard bound. *)

Definition RawTermEvaluationPrefixRealizedThrough (M : RawPAModel)
    (current limit assignmentCode assignmentStep tableStep
      supportCode supportStep : M) : Prop :=
  rawLe M current limit ->
  RawTermEvaluationPrefixRealized M current
    assignmentCode assignmentStep tableStep supportCode supportStep.

Definition termEvaluationPrefixRealizedThroughTermAt
    (current limit assignmentCode assignmentStep tableStep
      supportCode supportStep : term) : formula :=
  pImp
    (Formula.leTermAt current limit)
    (termEvaluationPrefixRealizedTermAt current
      assignmentCode assignmentStep tableStep supportCode supportStep).

Lemma raw_sat_termEvaluationPrefixRealizedThroughTermAt_iff : forall
    (M : RawPAModel) e current limit assignmentCode assignmentStep
      tableStep supportCode supportStep,
  raw_formula_sat M e
    (termEvaluationPrefixRealizedThroughTermAt current limit
      assignmentCode assignmentStep tableStep supportCode supportStep) <->
  RawTermEvaluationPrefixRealizedThrough M
    (raw_term_eval M e current) (raw_term_eval M e limit)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e tableStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termEvaluationPrefixRealizedThroughTermAt,
    RawTermEvaluationPrefixRealizedThrough.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_traversal,
    raw_sat_termEvaluationPrefixRealizedTermAt_iff.
  tauto.
Qed.

Theorem raw_termEvaluationPrefixRealized_through_all : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall limit assignmentCode assignmentStep supportCode supportStep
    tableStep,
  RawTermSyntaxTraversal M limit supportCode supportStep ->
  RawTermSyntaxAssignmentAdequate M limit
    assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationFixedStepCapacity M limit
    assignmentCode assignmentStep supportCode supportStep tableStep ->
  forall current,
  RawTermEvaluationPrefixRealizedThrough M current limit
    assignmentCode assignmentStep tableStep supportCode supportStep.
Proof.
  intros M hPA limit assignmentCode assignmentStep supportCode supportStep
    tableStep hsyntax hadequate hcapacity.
  set (parameterEnv := scons M limit
    (scons M assignmentCode (scons M assignmentStep
      (scons M tableStep (scons M supportCode
        (scons M supportStep (fun _ : nat => raw_zero M))))))).
  set (phi := termEvaluationPrefixRealizedThroughTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3)
    (tVar 4) (tVar 5) (tVar 6)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termEvaluationPrefixRealizedThroughTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _.
      exact (raw_termEvaluationPrefixRealized_zero M hPA
        assignmentCode assignmentStep tableStep supportCode supportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termEvaluationPrefixRealizedThroughTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6)) hcurrentSat) as hcurrentRaw.
      apply (proj2
        (raw_sat_termEvaluationPrefixRealizedThroughTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3)
          (tVar 4) (tVar 5) (tVar 6))).
      unfold parameterEnv in hcurrentRaw |- *.
      cbn [raw_term_eval scons] in hcurrentRaw |- *.
      intro hsuccLe.
      assert (hcurrentLimit : rawLt M current limit).
      {
        exact (raw_lt_of_succ_le_traversal M hPA
          current limit hsuccLe).
      }
      apply (raw_termEvaluationPrefixRealized_succ M hPA
        limit assignmentCode assignmentStep supportCode supportStep
        tableStep current hsyntax hadequate hcapacity hcurrentLimit).
      apply hcurrentRaw.
      exact (raw_lt_to_le M current limit hcurrentLimit).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termEvaluationPrefixRealizedThroughTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3)
      (tVar 4) (tVar 5) (tVar 6)) (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** The strongest realization theorem supplied here is fully nonstandard:
    [root], both syntax/support beta components, and the induction bound all
    live in [M].  Its one remaining premise is the explicit arithmetic
    capacity condition above. *)
Theorem raw_termEvaluationCertificateWithTables_exists_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep
    tableStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationFixedStepCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep tableStep ->
  exists value tableCode : M,
    RawTermEvaluationCertificateWithTables M
      root value assignmentCode assignmentStep
      tableCode tableStep supportCode supportStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    tableStep [hsyntax [hadequate hrootSupport]] hcapacity.
  pose proof (raw_termEvaluationPrefixRealized_through_all M hPA
    (raw_succ M root) assignmentCode assignmentStep
    supportCode supportStep tableStep
    hsyntax hadequate hcapacity (raw_succ M root)) as hprefix.
  specialize (hprefix (raw_le_refl_traversal M hPA (raw_succ M root))).
  destruct hprefix as [tableCode htraversal].
  destruct htraversal as [hsupport [htable hrows]].
  destruct (htable root (raw_assignment_lt_self_succ M hPA root))
    as [value hrootValue].
  exists value, tableCode.
  split.
  - repeat split; assumption.
  - split; assumption.
Qed.

Corollary raw_termEvaluationCertificate_exists_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationRealizationCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep ->
  exists value : M,
    RawTermEvaluationCertificate M
      root value assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax [tableStep hcapacity].
  destruct
    (raw_termEvaluationCertificateWithTables_exists_of_syntax_capacity
      M hPA root assignmentCode assignmentStep supportCode supportStep
      tableStep hsyntax hcapacity) as [value [tableCode hcertificate]].
  exists value, supportCode, supportStep, tableCode, tableStep.
  exact hcertificate.
Qed.

(** The construction supplies existence; the traversal module's independent
    cross-certificate theorem supplies uniqueness even against certificates
    built with entirely different support/value tables. *)
Corollary raw_termEvaluationCertificate_exists_unique_of_syntax_capacity :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep supportCode supportStep,
  RawTermSyntaxCertificateWithSupport M
    root assignmentCode assignmentStep supportCode supportStep ->
  RawTermEvaluationRealizationCapacity M (raw_succ M root)
    assignmentCode assignmentStep supportCode supportStep ->
  exists value : M,
    RawTermEvaluationCertificate M
      root value assignmentCode assignmentStep /\
    forall otherValue,
      RawTermEvaluationCertificate M
        root otherValue assignmentCode assignmentStep ->
      value = otherValue.
Proof.
  intros M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity.
  destruct (raw_termEvaluationCertificate_exists_of_syntax_capacity
    M hPA root assignmentCode assignmentStep supportCode supportStep
    hsyntax hcapacity) as [value hvalue].
  exists value. split; [exact hvalue |].
  intros otherValue hother.
  exact (raw_termEvaluationCertificate_value_functional M hPA
    root assignmentCode assignmentStep value otherValue hvalue hother).
Qed.

End PABoundedRawCodedTermEvaluationRealization.
