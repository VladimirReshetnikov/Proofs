(**
  Globally closed model-internal traversals for fixed-level partial truth.

  [RawCodedFixedLevelTruth] supplies exact *local* row checkers.  A Boolean
  row may consult a state stored at a smaller table index, so a local row by
  itself is not yet a closed certificate.  This file places those rows in
  four synchronized Goedel-beta tables (polarity, formula, assignment code,
  and assignment step), requires every stored row to pass its checker, and
  designates one stored state as the root.  Consequently every same-level
  dependency is present strictly earlier in the same certificate.

  Opposite quantifiers are different: their evidence lives at the preceding
  external level.  They therefore receive a fresh, recursively closed global
  certificate.  In particular, the recursive certificate is rooted at the
  quantified child and at the newly prepended assignment; it does not reuse
  either the quantified parent or the old assignment.

  Exact formula semantics below hold in every law-free [RawPAModel].  PA is
  needed only for beta functionality, prefix restriction, and realization.
  Level zero is realized from the already proved rank-zero totality theorem.
  Positive-level totality still needs an honest model-internal state schedule:
  quantifier witnesses change assignments and cannot be obtained merely by
  replaying the formula-syntax postorder.  That remaining seam is named at
  the end rather than assumed as an axiom.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedRankZeroTruthStepFunctionality
  RawCodedRankZeroTruthRealization RawCodedRankZeroTruthTotality
  RawCodedFixedLevelTruth.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruthTraversal.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedRankZeroTruthRealization.
Import PABoundedRawCodedRankZeroTruthTotality.
Import PABoundedRawCodedFixedLevelTruth.

(** ------------------------------------------------------------------
    Formula combinators and lift facts. *)

Definition fixedTruthTraversalAnd7 (a b c d f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g h))))).

Definition fixedTruthTraversalAll5 (body : formula) : formula :=
  pAll (pAll (pAll (pAll (pAll body)))).

Definition fixedTruthTraversalEx10 (body : formula) : formula :=
  fixedLevelEx8 (pEx (pEx body)).

Lemma raw_fixedTruthTraversal_eval_liftTerm_five : forall
    (M : RawPAModel) a b c d f (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f e)))))
    (liftTerm 5 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 5) with (S (S (S (S (S i))))) by lia. reflexivity.
Qed.

Lemma raw_fixedTruthTraversal_eval_liftTerm_ten : forall
    (M : RawPAModel) a b c d f g h i j k (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d (scons M f
      (scons M g (scons M h (scons M i (scons M j (scons M k e))))))))))
    (liftTerm 10 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j k e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro n.
  replace (n + 10) with
    (S (S (S (S (S (S (S (S (S (S n)))))))))) by lia.
  reflexivity.
Qed.

(** Four synchronized beta lookups are functional in every PA model. *)
Theorem raw_fixedLevelStateLookup_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep
    mode' code' assignmentCode' assignmentStep',
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep ->
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode' code' assignmentCode' assignmentStep' ->
  mode = mode' /\ code = code' /\
  assignmentCode = assignmentCode' /\ assignmentStep = assignmentStep'.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep
    mode' code' assignmentCode' assignmentStep'
    [hmode [hcode [hassignmentCode hassignmentStep]]]
    [hmode' [hcode' [hassignmentCode' hassignmentStep']]].
  repeat split.
  - exact (raw_codedAssignmentLookup_functional M hPA
      modeCode modeStep index mode mode' hmode hmode').
  - exact (raw_codedAssignmentLookup_functional M hPA
      formulaCode formulaStep index code code' hcode hcode').
  - exact (raw_codedAssignmentLookup_functional M hPA
      assignmentCodeCode assignmentCodeStep index
      assignmentCode assignmentCode' hassignmentCode hassignmentCode').
  - exact (raw_codedAssignmentLookup_functional M hPA
      assignmentStepCode assignmentStepStep index
      assignmentStep assignmentStep' hassignmentStep hassignmentStep').
Qed.

(** ------------------------------------------------------------------
    Closed rows. *)

Definition fixedLevelClosedZeroRowTermAt
    (mode code assignmentCode assignmentStep : term) : formula :=
  pOr
    (pAnd (pEq mode tZero)
      (fixedLevelSigmaZeroTermAt code assignmentCode assignmentStep))
    (pAnd (pEq mode (Term.numeral 1))
      (fixedLevelPiZeroTermAt code assignmentCode assignmentStep)).

Definition RawFixedLevelClosedZeroRow (M : RawPAModel)
    (mode code assignmentCode assignmentStep : M) : Prop :=
  (mode = rawFixedLevelSigmaMode M /\
    RawFixedLevelSigmaZero M code assignmentCode assignmentStep) \/
  (mode = rawFixedLevelPiMode M /\
    RawFixedLevelPiZero M code assignmentCode assignmentStep).

Arguments RawFixedLevelClosedZeroRow
  M mode code assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_fixedLevelClosedZeroRowTermAt_iff : forall
    (M : RawPAModel) e mode code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelClosedZeroRowTermAt
      mode code assignmentCode assignmentStep) <->
  RawFixedLevelClosedZeroRow M
    (raw_term_eval M e mode) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelClosedZeroRowTermAt,
    RawFixedLevelClosedZeroRow,
    rawFixedLevelSigmaMode, rawFixedLevelPiMode.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaZeroTermAt_iff,
    raw_sat_fixedLevelPiZeroTermAt_iff,
    raw_term_eval_numeral.
  reflexivity.
Qed.

(** [lowerSigmaEvidence] and [lowerPiEvidence] are Coq-level formula
    constructors.  Applying them only builds syntax; the resulting object is
    still an ordinary first-order PA formula.  Inside the Sigma-All and
    Pi-Ex clauses the child is variable six of the eight row witnesses, lifted
    past the three binder-extension variables. *)
Definition fixedLevelClosedSuccessorRowTermAt (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence :
      term -> term -> term -> formula)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep : term) : formula :=
  pOr
    (pAnd (pEq mode tZero)
      (fixedLevelEx8
        (fixedLevelSigmaSuccessorWitnessRowTermAt lower
          (lowerPiEvidence (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0))
          (liftTerm 8 modeCode) (liftTerm 8 modeStep)
          (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
          (liftTerm 8 assignmentCodeCode)
          (liftTerm 8 assignmentCodeStep)
          (liftTerm 8 assignmentStepCode)
          (liftTerm 8 assignmentStepStep)
          (liftTerm 8 index) (liftTerm 8 code)
          (liftTerm 8 assignmentCode) (liftTerm 8 assignmentStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))))
    (pAnd (pEq mode (Term.numeral 1))
      (fixedLevelEx8
        (fixedLevelPiSuccessorWitnessRowTermAt lower
          (lowerSigmaEvidence (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0))
          (liftTerm 8 modeCode) (liftTerm 8 modeStep)
          (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
          (liftTerm 8 assignmentCodeCode)
          (liftTerm 8 assignmentCodeStep)
          (liftTerm 8 assignmentStepCode)
          (liftTerm 8 assignmentStepStep)
          (liftTerm 8 index) (liftTerm 8 code)
          (liftTerm 8 assignmentCode) (liftTerm 8 assignmentStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Definition RawFixedLevelClosedSuccessorRow (M : RawPAModel) (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep : M) : Prop :=
  (mode = rawFixedLevelSigmaMode M /\
    exists leftIndex leftCode rightIndex rightCode witness
      newAssignmentCode newAssignmentStep spare : M,
      RawFixedLevelSigmaSuccessorWitnessRow M lower
        (fun _ binderAssignmentCode binderAssignmentStep =>
          lowerPiEvidence leftCode
            binderAssignmentCode binderAssignmentStep)
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        index code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare) \/
  (mode = rawFixedLevelPiMode M /\
    exists leftIndex leftCode rightIndex rightCode witness
      newAssignmentCode newAssignmentStep spare : M,
      RawFixedLevelPiSuccessorWitnessRow M lower
        (fun _ binderAssignmentCode binderAssignmentStep =>
          lowerSigmaEvidence leftCode
            binderAssignmentCode binderAssignmentStep)
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        index code assignmentCode assignmentStep
        leftIndex leftCode rightIndex rightCode witness
        newAssignmentCode newAssignmentStep spare).

Arguments RawFixedLevelClosedSuccessorRow
  M lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_fixedLevelClosedSuccessorRowTermAt_iff : forall
    (M : RawPAModel)
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula)
    (lowerSigmaRaw lowerPiRaw : M -> M -> M -> Prop),
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerSigmaEvidence code assignmentCode assignmentStep) <->
    lowerSigmaRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerPiEvidence code assignmentCode assignmentStep) <->
    lowerPiRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  forall e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelClosedSuccessorRowTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep) <->
  RawFixedLevelClosedSuccessorRow M lower lowerSigmaRaw lowerPiRaw
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e index) (raw_term_eval M e mode)
    (raw_term_eval M e code) (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros M lowerSigmaEvidence lowerPiEvidence
    lowerSigmaRaw lowerPiRaw hSigma hPi e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep.
  unfold fixedLevelClosedSuccessorRowTermAt,
    RawFixedLevelClosedSuccessorRow,
    rawFixedLevelSigmaMode, rawFixedLevelPiMode, fixedLevelEx8.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_fixedLevelSigmaSuccessorWitnessRowTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelPiSuccessorWitnessRowTermAt_iff.
  unfold RawFixedLevelSigmaSuccessorWitnessRow,
    RawFixedLevelPiSuccessorWitnessRow,
    RawFixedLevelNoBinderCounterexample.
  repeat setoid_rewrite hSigma.
  repeat setoid_rewrite hPi.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_three.
  repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_eight.
  cbn [raw_term_eval scons].
  rewrite raw_term_eval_numeral.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    All stored rows are closed.  The five universal variables are, from
    outermost to innermost, index, mode, formula code, assignment code, and
    assignment step; at the body they occupy variables four down to zero. *)

Definition fixedLevelZeroTruthTraversalRowsTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : term) : formula :=
  fixedTruthTraversalAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 bound))
      (pImp
        (fixedLevelStateLookupTermAt
          (liftTerm 5 modeCode) (liftTerm 5 modeStep)
          (liftTerm 5 formulaCode) (liftTerm 5 formulaStep)
          (liftTerm 5 assignmentCodeCode)
          (liftTerm 5 assignmentCodeStep)
          (liftTerm 5 assignmentStepCode)
          (liftTerm 5 assignmentStepStep)
          (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (fixedLevelClosedZeroRowTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Definition RawFixedLevelZeroTruthTraversalRows (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : M) : Prop :=
  forall index mode code assignmentCode assignmentStep : M,
    rawLt M index bound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawFixedLevelClosedZeroRow M
      mode code assignmentCode assignmentStep.

Arguments RawFixedLevelZeroTruthTraversalRows
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound : clear implicits.

Lemma raw_sat_fixedLevelZeroTruthTraversalRowsTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound,
  raw_formula_sat M e
    (fixedLevelZeroTruthTraversalRowsTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound) <->
  RawFixedLevelZeroTruthTraversalRows M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold fixedLevelZeroTruthTraversalRowsTermAt,
    RawFixedLevelZeroTruthTraversalRows, fixedTruthTraversalAll5.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelClosedZeroRowTermAt_iff.
  repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition fixedLevelSuccessorTruthTraversalRowsTermAt (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence :
      term -> term -> term -> formula)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : term) : formula :=
  fixedTruthTraversalAll5
    (pImp
      (Formula.ltTermAt (tVar 4) (liftTerm 5 bound))
      (pImp
        (fixedLevelStateLookupTermAt
          (liftTerm 5 modeCode) (liftTerm 5 modeStep)
          (liftTerm 5 formulaCode) (liftTerm 5 formulaStep)
          (liftTerm 5 assignmentCodeCode)
          (liftTerm 5 assignmentCodeStep)
          (liftTerm 5 assignmentStepCode)
          (liftTerm 5 assignmentStepStep)
          (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (fixedLevelClosedSuccessorRowTermAt lower
          lowerSigmaEvidence lowerPiEvidence
          (liftTerm 5 modeCode) (liftTerm 5 modeStep)
          (liftTerm 5 formulaCode) (liftTerm 5 formulaStep)
          (liftTerm 5 assignmentCodeCode)
          (liftTerm 5 assignmentCodeStep)
          (liftTerm 5 assignmentStepCode)
          (liftTerm 5 assignmentStepStep)
          (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)))).

Definition RawFixedLevelSuccessorTruthTraversalRows
    (M : RawPAModel) (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound : M) : Prop :=
  forall index mode code assignmentCode assignmentStep : M,
    rawLt M index bound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep ->
    RawFixedLevelClosedSuccessorRow M lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep.

Arguments RawFixedLevelSuccessorTruthTraversalRows
  M lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound : clear implicits.

Lemma raw_sat_fixedLevelSuccessorTruthTraversalRowsTermAt_iff : forall
    (M : RawPAModel)
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula)
    (lowerSigmaRaw lowerPiRaw : M -> M -> M -> Prop),
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerSigmaEvidence code assignmentCode assignmentStep) <->
    lowerSigmaRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerPiEvidence code assignmentCode assignmentStep) <->
    lowerPiRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  forall e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound,
  raw_formula_sat M e
    (fixedLevelSuccessorTruthTraversalRowsTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound) <->
  RawFixedLevelSuccessorTruthTraversalRows M lower
    lowerSigmaRaw lowerPiRaw
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound).
Proof.
  intros M lowerSigmaEvidence lowerPiEvidence lowerSigmaRaw lowerPiRaw
    hSigma hPi e lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound.
  unfold fixedLevelSuccessorTruthTraversalRowsTermAt,
    RawFixedLevelSuccessorTruthTraversalRows, fixedTruthTraversalAll5.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_fixedLevelStateLookupTermAt_iff.
  setoid_rewrite (raw_sat_fixedLevelClosedSuccessorRowTermAt_iff
    M lowerSigmaEvidence lowerPiEvidence lowerSigmaRaw lowerPiRaw
    hSigma hPi).
  repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_five.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Complete table certificates. *)

Definition fixedLevelZeroTruthTraversalTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep : term)
    : formula :=
  fixedTruthTraversalAnd7
    (codedAssignmentDefinedThroughTermAt modeCode modeStep bound)
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentCodeCode assignmentCodeStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentStepCode assignmentStepStep bound)
    (Formula.ltTermAt rootIndex bound)
    (fixedLevelStateLookupTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      rootIndex rootMode root assignmentCode assignmentStep)
    (fixedLevelZeroTruthTraversalRowsTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound).

Definition RawFixedLevelZeroTruthTraversal (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound /\
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound /\
  rawLt M rootIndex bound /\
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    rootIndex rootMode root assignmentCode assignmentStep /\
  RawFixedLevelZeroTruthTraversalRows M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound.

Arguments RawFixedLevelZeroTruthTraversal
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
  : clear implicits.

Lemma raw_sat_fixedLevelZeroTruthTraversalTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelZeroTruthTraversalTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep) <->
  RawFixedLevelZeroTruthTraversal M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e rootMode) (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelZeroTruthTraversalTermAt,
    RawFixedLevelZeroTruthTraversal, fixedTruthTraversalAnd7.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_ltTermAt_iff,
    raw_sat_fixedLevelStateLookupTermAt_iff,
    raw_sat_fixedLevelZeroTruthTraversalRowsTermAt_iff.
  reflexivity.
Qed.

Definition fixedLevelSuccessorTruthTraversalTermAt (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence :
      term -> term -> term -> formula)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep : term)
    : formula :=
  fixedTruthTraversalAnd7
    (codedAssignmentDefinedThroughTermAt modeCode modeStep bound)
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentCodeCode assignmentCodeStep bound)
    (codedAssignmentDefinedThroughTermAt
      assignmentStepCode assignmentStepStep bound)
    (Formula.ltTermAt rootIndex bound)
    (fixedLevelStateLookupTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      rootIndex rootMode root assignmentCode assignmentStep)
    (fixedLevelSuccessorTruthTraversalRowsTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound).

Definition RawFixedLevelSuccessorTruthTraversal (M : RawPAModel)
    (lower : nat)
    (lowerSigmaEvidence lowerPiEvidence : M -> M -> M -> Prop)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M modeCode modeStep bound /\
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentCodeCode assignmentCodeStep bound /\
  RawCodedAssignmentDefinedThrough M
    assignmentStepCode assignmentStepStep bound /\
  rawLt M rootIndex bound /\
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    rootIndex rootMode root assignmentCode assignmentStep /\
  RawFixedLevelSuccessorTruthTraversalRows M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound.

Arguments RawFixedLevelSuccessorTruthTraversal
  M lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
  : clear implicits.

Lemma raw_sat_fixedLevelSuccessorTruthTraversalTermAt_iff : forall
    (M : RawPAModel)
    (lowerSigmaEvidence lowerPiEvidence : term -> term -> term -> formula)
    (lowerSigmaRaw lowerPiRaw : M -> M -> M -> Prop),
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerSigmaEvidence code assignmentCode assignmentStep) <->
    lowerSigmaRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  (forall e code assignmentCode assignmentStep,
    raw_formula_sat M e
      (lowerPiEvidence code assignmentCode assignmentStep) <->
    lowerPiRaw (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) ->
  forall e lower
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelSuccessorTruthTraversalTermAt lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex rootMode root assignmentCode assignmentStep) <->
  RawFixedLevelSuccessorTruthTraversal M lower lowerSigmaRaw lowerPiRaw
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e rootMode) (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intros M lowerSigmaEvidence lowerPiEvidence lowerSigmaRaw lowerPiRaw
    hSigma hPi e lower modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep.
  unfold fixedLevelSuccessorTruthTraversalTermAt,
    RawFixedLevelSuccessorTruthTraversal, fixedTruthTraversalAnd7.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff,
    raw_sat_ltTermAt_iff,
    raw_sat_fixedLevelStateLookupTermAt_iff.
  rewrite (raw_sat_fixedLevelSuccessorTruthTraversalRowsTermAt_iff
    M lowerSigmaEvidence lowerPiEvidence lowerSigmaRaw lowerPiRaw
    hSigma hPi).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Recursively global Sigma-truth and Pi-falsity certificates.

    The ten existential witnesses are the four beta-table code/step pairs,
    followed by the table bound and root index.  Lower-level recursive calls
    allocate their own tables.  This separation is what makes an
    opposite-quantifier clause globally closed rather than merely local. *)

Fixpoint fixedLevelSigmaTruthCertificateTermAt (level : nat)
    (root assignmentCode assignmentStep : term) : formula :=
  match level with
  | 0 =>
      fixedTruthTraversalEx10
        (fixedLevelZeroTruthTraversalTermAt
          (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0) tZero
          (liftTerm 10 root) (liftTerm 10 assignmentCode)
          (liftTerm 10 assignmentStep))
  | S lower =>
      fixedTruthTraversalEx10
        (fixedLevelSuccessorTruthTraversalTermAt lower
          (fun child childAssignmentCode childAssignmentStep =>
            fixedLevelSigmaTruthCertificateTermAt lower
              child childAssignmentCode childAssignmentStep)
          (fun child childAssignmentCode childAssignmentStep =>
            fixedLevelPiFalsityCertificateTermAt lower
              child childAssignmentCode childAssignmentStep)
          (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0) tZero
          (liftTerm 10 root) (liftTerm 10 assignmentCode)
          (liftTerm 10 assignmentStep))
  end
with fixedLevelPiFalsityCertificateTermAt (level : nat)
    (root assignmentCode assignmentStep : term) : formula :=
  match level with
  | 0 =>
      fixedTruthTraversalEx10
        (fixedLevelZeroTruthTraversalTermAt
          (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0) (Term.numeral 1)
          (liftTerm 10 root) (liftTerm 10 assignmentCode)
          (liftTerm 10 assignmentStep))
  | S lower =>
      fixedTruthTraversalEx10
        (fixedLevelSuccessorTruthTraversalTermAt lower
          (fun child childAssignmentCode childAssignmentStep =>
            fixedLevelSigmaTruthCertificateTermAt lower
              child childAssignmentCode childAssignmentStep)
          (fun child childAssignmentCode childAssignmentStep =>
            fixedLevelPiFalsityCertificateTermAt lower
              child childAssignmentCode childAssignmentStep)
          (tVar 9) (tVar 8) (tVar 7) (tVar 6)
          (tVar 5) (tVar 4) (tVar 3) (tVar 2)
          (tVar 1) (tVar 0) (Term.numeral 1)
          (liftTerm 10 root) (liftTerm 10 assignmentCode)
          (liftTerm 10 assignmentStep))
  end.

Fixpoint RawFixedLevelSigmaTruthCertificate (M : RawPAModel) (level : nat)
    (root assignmentCode assignmentStep : M) : Prop :=
  match level with
  | 0 =>
      exists modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep bound rootIndex : M,
        RawFixedLevelZeroTruthTraversal M
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M)
          root assignmentCode assignmentStep
  | S lower =>
      exists modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep bound rootIndex : M,
        RawFixedLevelSuccessorTruthTraversal M lower
          (fun child childAssignmentCode childAssignmentStep =>
            RawFixedLevelSigmaTruthCertificate M lower
              child childAssignmentCode childAssignmentStep)
          (fun child childAssignmentCode childAssignmentStep =>
            RawFixedLevelPiFalsityCertificate M lower
              child childAssignmentCode childAssignmentStep)
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelSigmaMode M)
          root assignmentCode assignmentStep
  end
with RawFixedLevelPiFalsityCertificate (M : RawPAModel) (level : nat)
    (root assignmentCode assignmentStep : M) : Prop :=
  match level with
  | 0 =>
      exists modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep bound rootIndex : M,
        RawFixedLevelZeroTruthTraversal M
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M)
          root assignmentCode assignmentStep
  | S lower =>
      exists modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep bound rootIndex : M,
        RawFixedLevelSuccessorTruthTraversal M lower
          (fun child childAssignmentCode childAssignmentStep =>
            RawFixedLevelSigmaTruthCertificate M lower
              child childAssignmentCode childAssignmentStep)
          (fun child childAssignmentCode childAssignmentStep =>
            RawFixedLevelPiFalsityCertificate M lower
              child childAssignmentCode childAssignmentStep)
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound rootIndex (rawFixedLevelPiMode M)
          root assignmentCode assignmentStep
  end.

Arguments RawFixedLevelSigmaTruthCertificate
  M level root assignmentCode assignmentStep : clear implicits.
Arguments RawFixedLevelPiFalsityCertificate
  M level root assignmentCode assignmentStep : clear implicits.

(** Simultaneous exact semantics.  The induction hypotheses are precisely the
    semantic interfaces supplied to the successor traversal constructor. *)
Theorem raw_sat_fixedLevelTruthCertificateTermAt_iff : forall level,
  (forall (M : RawPAModel) e root assignmentCode assignmentStep,
    raw_formula_sat M e
      (fixedLevelSigmaTruthCertificateTermAt level
        root assignmentCode assignmentStep) <->
    RawFixedLevelSigmaTruthCertificate M level
      (raw_term_eval M e root)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)) /\
  (forall (M : RawPAModel) e root assignmentCode assignmentStep,
    raw_formula_sat M e
      (fixedLevelPiFalsityCertificateTermAt level
        root assignmentCode assignmentStep) <->
    RawFixedLevelPiFalsityCertificate M level
      (raw_term_eval M e root)
      (raw_term_eval M e assignmentCode)
      (raw_term_eval M e assignmentStep)).
Proof.
  induction level as [|lower [IHsigma IHpi]].
  - split; intros M e root assignmentCode assignmentStep;
      cbn [fixedLevelSigmaTruthCertificateTermAt
        fixedLevelPiFalsityCertificateTermAt
        RawFixedLevelSigmaTruthCertificate
        RawFixedLevelPiFalsityCertificate
        fixedTruthTraversalEx10 fixedLevelEx8 raw_formula_sat].
    + setoid_rewrite raw_sat_fixedLevelZeroTruthTraversalTermAt_iff.
      repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_ten.
      cbn [raw_term_eval scons]. reflexivity.
    + setoid_rewrite raw_sat_fixedLevelZeroTruthTraversalTermAt_iff.
      repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_ten.
      cbn [raw_term_eval scons].
      reflexivity.
  - split; intros M e root assignmentCode assignmentStep;
      cbn [fixedLevelSigmaTruthCertificateTermAt
        fixedLevelPiFalsityCertificateTermAt
        RawFixedLevelSigmaTruthCertificate
        RawFixedLevelPiFalsityCertificate
        fixedTruthTraversalEx10 fixedLevelEx8 raw_formula_sat].
    + setoid_rewrite (raw_sat_fixedLevelSuccessorTruthTraversalTermAt_iff
        M
        (fun child childAssignmentCode childAssignmentStep =>
          fixedLevelSigmaTruthCertificateTermAt lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          fixedLevelPiFalsityCertificateTermAt lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (IHsigma M) (IHpi M)).
      repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_ten.
      cbn [raw_term_eval scons]. reflexivity.
    + setoid_rewrite (raw_sat_fixedLevelSuccessorTruthTraversalTermAt_iff
        M
        (fun child childAssignmentCode childAssignmentStep =>
          fixedLevelSigmaTruthCertificateTermAt lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          fixedLevelPiFalsityCertificateTermAt lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelSigmaTruthCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (fun child childAssignmentCode childAssignmentStep =>
          RawFixedLevelPiFalsityCertificate M lower
            child childAssignmentCode childAssignmentStep)
        (IHsigma M) (IHpi M)).
      repeat setoid_rewrite raw_fixedTruthTraversal_eval_liftTerm_ten.
      cbn [raw_term_eval scons].
      reflexivity.
Qed.

Corollary raw_sat_fixedLevelSigmaTruthCertificateTermAt_iff : forall level
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelSigmaTruthCertificateTermAt level
      root assignmentCode assignmentStep) <->
  RawFixedLevelSigmaTruthCertificate M level
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intro level.
  exact (proj1 (raw_sat_fixedLevelTruthCertificateTermAt_iff level)).
Qed.

Corollary raw_sat_fixedLevelPiFalsityCertificateTermAt_iff : forall level
    (M : RawPAModel) e root assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelPiFalsityCertificateTermAt level
      root assignmentCode assignmentStep) <->
  RawFixedLevelPiFalsityCertificate M level
    (raw_term_eval M e root)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intro level.
  exact (proj2 (raw_sat_fixedLevelTruthCertificateTermAt_iff level)).
Qed.

(** ------------------------------------------------------------------
    Functionality, root closure, and prefix closure. *)

Theorem raw_fixedLevelZeroTruthTraversal_row_exists_unique : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelZeroTruthTraversal M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  forall index, rawLt M index bound ->
  exists mode code rowAssignmentCode rowAssignmentStep,
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep /\
    RawFixedLevelClosedZeroRow M
      mode code rowAssignmentCode rowAssignmentStep /\
    forall mode' code' rowAssignmentCode' rowAssignmentStep',
      RawFixedLevelStateLookup M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        index mode' code' rowAssignmentCode' rowAssignmentStep' ->
      mode = mode' /\ code = code' /\
      rowAssignmentCode = rowAssignmentCode' /\
      rowAssignmentStep = rowAssignmentStep'.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined [hassignmentCodeDefined
      [hassignmentStepDefined [_ [_ hrows]]]]]] index hindex.
  destruct (hmodeDefined index hindex) as [mode hmode].
  destruct (hformulaDefined index hindex) as [code hcode].
  destruct (hassignmentCodeDefined index hindex)
    as [rowAssignmentCode hassignmentCode].
  destruct (hassignmentStepDefined index hindex)
    as [rowAssignmentStep hassignmentStep].
  assert (hlookup : RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep).
  { repeat split; assumption. }
  exists mode, code, rowAssignmentCode, rowAssignmentStep.
  split; [exact hlookup |]. split.
  - exact (hrows index mode code rowAssignmentCode rowAssignmentStep
      hindex hlookup).
  - intros mode' code' rowAssignmentCode' rowAssignmentStep' hlookup'.
    exact (raw_fixedLevelStateLookup_functional M hPA
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep
      mode' code' rowAssignmentCode' rowAssignmentStep' hlookup hlookup').
Qed.

Theorem raw_fixedLevelSuccessorTruthTraversal_row_exists_unique : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  forall index, rawLt M index bound ->
  exists mode code rowAssignmentCode rowAssignmentStep,
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep /\
    RawFixedLevelClosedSuccessorRow M lower
      lowerSigmaEvidence lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep /\
    forall mode' code' rowAssignmentCode' rowAssignmentStep',
      RawFixedLevelStateLookup M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        index mode' code' rowAssignmentCode' rowAssignmentStep' ->
      mode = mode' /\ code = code' /\
      rowAssignmentCode = rowAssignmentCode' /\
      rowAssignmentStep = rowAssignmentStep'.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmodeDefined [hformulaDefined [hassignmentCodeDefined
      [hassignmentStepDefined [_ [_ hrows]]]]]] index hindex.
  destruct (hmodeDefined index hindex) as [mode hmode].
  destruct (hformulaDefined index hindex) as [code hcode].
  destruct (hassignmentCodeDefined index hindex)
    as [rowAssignmentCode hassignmentCode].
  destruct (hassignmentStepDefined index hindex)
    as [rowAssignmentStep hassignmentStep].
  assert (hlookup : RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep).
  { repeat split; assumption. }
  exists mode, code, rowAssignmentCode, rowAssignmentStep.
  split; [exact hlookup |]. split.
  - exact (hrows index mode code rowAssignmentCode rowAssignmentStep
      hindex hlookup).
  - intros mode' code' rowAssignmentCode' rowAssignmentStep' hlookup'.
    exact (raw_fixedLevelStateLookup_functional M hPA
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep
      mode' code' rowAssignmentCode' rowAssignmentStep' hlookup hlookup').
Qed.

Lemma raw_fixedLevelZeroTruthTraversal_root_row : forall
    (M : RawPAModel)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelZeroTruthTraversal M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelClosedZeroRow M
    rootMode root assignmentCode assignmentStep.
Proof.
  intros M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [_ [_ [_ [_ [hrootIndex [hrootLookup hrows]]]]]].
  exact (hrows rootIndex rootMode root assignmentCode assignmentStep
    hrootIndex hrootLookup).
Qed.

Lemma raw_fixedLevelSuccessorTruthTraversal_root_row : forall
    (M : RawPAModel) lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    rootIndex rootMode root assignmentCode assignmentStep.
Proof.
  intros M lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [_ [_ [_ [_ [hrootIndex [hrootLookup hrows]]]]]].
  exact (hrows rootIndex rootMode root assignmentCode assignmentStep
    hrootIndex hrootLookup).
Qed.

(** Any state explicitly consulted by a row is itself a closed row of the
    traversal.  This theorem is the advertised same-level global-closure
    property; strictness comes from [RawFixedLevelEarlierState]. *)
Theorem raw_fixedLevelSuccessorTruthTraversal_closes_earlier : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    currentIndex childIndex childMode childCode
    childAssignmentCode childAssignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  rawLt M currentIndex bound ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex childMode childCode
    childAssignmentCode childAssignmentStep ->
  rawLt M childIndex currentIndex /\
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    childIndex childMode childCode childAssignmentCode childAssignmentStep /\
  RawFixedLevelClosedSuccessorRow M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    childIndex childMode childCode childAssignmentCode childAssignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    currentIndex childIndex childMode childCode
    childAssignmentCode childAssignmentStep
    [_ [_ [_ [_ [_ [_ hrows]]]]]] hcurrent [hchild hlookup].
  split; [exact hchild |]. split; [exact hlookup |].
  apply (hrows childIndex childMode childCode
    childAssignmentCode childAssignmentStep).
  - exact (raw_assignment_lt_trans M hPA
      childIndex currentIndex bound hchild hcurrent).
  - exact hlookup.
Qed.

Theorem raw_fixedLevelZeroTruthTraversal_restrict_to_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelZeroTruthTraversal M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  forall index mode code rowAssignmentCode rowAssignmentStep,
    rawLt M index bound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep ->
  RawFixedLevelZeroTruthTraversal M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    (raw_succ M index) index mode code rowAssignmentCode rowAssignmentStep.
Proof.
  intros M hPA modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep [_ [_ hrows]]]]]]
    index mode code rowAssignmentCode rowAssignmentStep hindex hlookup.
  assert (hbelow : forall x,
      rawLt M x (raw_succ M index) -> rawLt M x bound).
  {
    intros x hx. destruct (raw_lt_succ_cases M hPA x index hx) as [hxi | ->].
    - exact (raw_assignment_lt_trans M hPA x index bound hxi hindex).
    - exact hindex.
  }
  split.
  - intros x hx. exact (hmode x (hbelow x hx)).
  - split.
    + intros x hx. exact (hformula x (hbelow x hx)).
    + split.
      * intros x hx. exact (hassignmentCode x (hbelow x hx)).
      * split.
        -- intros x hx. exact (hassignmentStep x (hbelow x hx)).
        -- split.
           ++ exact (raw_assignment_lt_self_succ M hPA index).
           ++ split; [exact hlookup |].
              intros x m c ac astep hx hrowLookup.
              exact (hrows x m c ac astep (hbelow x hx) hrowLookup).
Qed.

Theorem raw_fixedLevelSuccessorTruthTraversal_restrict_to_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep,
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep ->
  forall index mode code rowAssignmentCode rowAssignmentStep,
    rawLt M index bound ->
    RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code rowAssignmentCode rowAssignmentStep ->
  RawFixedLevelSuccessorTruthTraversal M lower
    lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    (raw_succ M index) index mode code rowAssignmentCode rowAssignmentStep.
Proof.
  intros M hPA lower lowerSigmaEvidence lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    bound rootIndex rootMode root assignmentCode assignmentStep
    [hmode [hformula [hassignmentCode [hassignmentStep [_ [_ hrows]]]]]]
    index mode code rowAssignmentCode rowAssignmentStep hindex hlookup.
  assert (hbelow : forall x,
      rawLt M x (raw_succ M index) -> rawLt M x bound).
  {
    intros x hx. destruct (raw_lt_succ_cases M hPA x index hx) as [hxi | ->].
    - exact (raw_assignment_lt_trans M hPA x index bound hxi hindex).
    - exact hindex.
  }
  split.
  - intros x hx. exact (hmode x (hbelow x hx)).
  - split.
    + intros x hx. exact (hformula x (hbelow x hx)).
    + split.
      * intros x hx. exact (hassignmentCode x (hbelow x hx)).
      * split.
        -- intros x hx. exact (hassignmentStep x (hbelow x hx)).
        -- split.
           ++ exact (raw_assignment_lt_self_succ M hPA index).
           ++ split; [exact hlookup |].
              intros x m c ac astep hx hrowLookup.
              exact (hrows x m c ac astep (hbelow x hx) hrowLookup).
Qed.

(** Global certificates always advertise their correct hierarchy domain. *)
Theorem raw_fixedLevelSigmaTruthCertificate_domain : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root assignmentCode assignmentStep,
  RawFixedLevelSigmaTruthCertificate M level
    root assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M level root.
Proof.
  intros M hPA [|lower] root assignmentCode assignmentStep hcertificate.
  - cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
    pose proof (raw_fixedLevelZeroTruthTraversal_root_row M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep htraversal) as hrow.
    destruct hrow as [[_ hzero] | [hmodes _]].
    + exact (proj1 hzero).
    + exfalso. apply (raw_zero_neq_truthOne M hPA).
      exact hmodes.
  - cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
    pose proof (raw_fixedLevelSuccessorTruthTraversal_root_row M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelSigmaMode M)
      root assignmentCode assignmentStep htraversal) as hrow.
    destruct hrow as [[_ hwitness] | [hmodes _]].
    + destruct hwitness as
        (leftIndex & leftCode & rightIndex & rightCode & witness &
         newAssignmentCode & newAssignmentStep & spare & hsuccessor).
      exact (proj1 hsuccessor).
    + exfalso. apply (raw_zero_neq_truthOne M hPA).
      exact hmodes.
Qed.

Theorem raw_fixedLevelPiFalsityCertificate_domain : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall level root assignmentCode assignmentStep,
  RawFixedLevelPiFalsityCertificate M level
    root assignmentCode assignmentStep ->
  RawFixedLevelPiDomain M level root.
Proof.
  intros M hPA [|lower] root assignmentCode assignmentStep hcertificate.
  - cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
    pose proof (raw_fixedLevelZeroTruthTraversal_root_row M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep htraversal) as hrow.
    destruct hrow as [[hmodes _] | [_ hzero]].
    + exfalso. apply (raw_zero_neq_truthOne M hPA).
      symmetry. exact hmodes.
    + exact (proj1 hzero).
  - cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex & htraversal).
    pose proof (raw_fixedLevelSuccessorTruthTraversal_root_row M lower
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelSigmaTruthCertificate M lower
          child childAssignmentCode childAssignmentStep)
      (fun child childAssignmentCode childAssignmentStep =>
        RawFixedLevelPiFalsityCertificate M lower
          child childAssignmentCode childAssignmentStep)
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      bound rootIndex (rawFixedLevelPiMode M)
      root assignmentCode assignmentStep htraversal) as hrow.
    destruct hrow as [[hmodes _] | [_ hwitness]].
    + exfalso. apply (raw_zero_neq_truthOne M hPA).
      symmetry. exact hmodes.
    + destruct hwitness as
        (leftIndex & leftCode & rightIndex & rightCode & witness &
         newAssignmentCode & newAssignmentStep & spare & hsuccessor).
      exact (proj1 hsuccessor).
Qed.

(** The former root-only assembly seam from the local-row module is now
    discharged: every advertised certificate supplies not just a root lookup
    but a globally closed traversal containing it. *)
Theorem raw_fixedLevelGlobalAssemblyFor_closed_certificates : forall
    (M : RawPAModel),
  RawFixedLevelGlobalAssemblyFor M
    (RawFixedLevelSigmaTruthCertificate M)
    (RawFixedLevelPiFalsityCertificate M).
Proof.
  intros M [|lower] root assignmentCode assignmentStep mode
    [[-> hcertificate] | [-> hcertificate]].
  - cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       [_ [_ [_ [_ [hroot [hlookup _]]]]]]).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    split; assumption.
  - cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       [_ [_ [_ [_ [hroot [hlookup _]]]]]]).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    split; assumption.
  - cbn [RawFixedLevelSigmaTruthCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       [_ [_ [_ [_ [hroot [hlookup _]]]]]]).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    split; assumption.
  - cbn [RawFixedLevelPiFalsityCertificate] in hcertificate.
    destruct hcertificate as
      (modeCode & modeStep & formulaCode & formulaStep &
       assignmentCodeCode & assignmentCodeStep &
       assignmentStepCode & assignmentStepStep & bound & rootIndex &
       [_ [_ [_ [_ [hroot [hlookup _]]]]]]).
    exists modeCode, modeStep, formulaCode, formulaStep,
      assignmentCodeCode, assignmentCodeStep,
      assignmentStepCode, assignmentStepStep, bound, rootIndex.
    split; assumption.
Qed.

(** ------------------------------------------------------------------
    Level-zero realization.

    A closed leaf can be placed in a one-row traversal.  The four calls to
    [raw_codedAssignmentPrepend_defined_exists] are genuine internal beta
    capacity constructions: no external decoding of the carrier values is
    used. *)

Theorem raw_fixedLevelClosedZeroRow_singleton_traversal : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall mode root assignmentCode assignmentStep,
  RawFixedLevelClosedZeroRow M mode root assignmentCode assignmentStep ->
  exists modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep bound rootIndex : M,
    RawFixedLevelZeroTruthTraversal M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound rootIndex mode root assignmentCode assignmentStep.
Proof.
  intros M hPA mode root assignmentCode assignmentStep hclosed.
  pose proof (raw_codedAssignment_empty_defined M hPA) as hempty.
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    (raw_zero M) (raw_zero M) mode (raw_zero M) hempty)
    as [modeCode [modeStep [hmodePrepend hmodeDefined]]].
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    (raw_zero M) (raw_zero M) root (raw_zero M) hempty)
    as [formulaCode [formulaStep [hformulaPrepend hformulaDefined]]].
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    (raw_zero M) (raw_zero M) assignmentCode (raw_zero M) hempty)
    as [assignmentCodeCode [assignmentCodeStep
      [hassignmentCodePrepend hassignmentCodeDefined]]].
  destruct (raw_codedAssignmentPrepend_defined_exists M hPA
    (raw_zero M) (raw_zero M) assignmentStep (raw_zero M) hempty)
    as [assignmentStepCode [assignmentStepStep
      [hassignmentStepPrepend hassignmentStepDefined]]].
  set (bound := raw_succ M (raw_zero M)).
  assert (hrootLookup : RawFixedLevelStateLookup M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (raw_zero M) mode root assignmentCode assignmentStep).
  {
    repeat split.
    - exact (proj1 hmodePrepend).
    - exact (proj1 hformulaPrepend).
    - exact (proj1 hassignmentCodePrepend).
    - exact (proj1 hassignmentStepPrepend).
  }
  exists modeCode, modeStep, formulaCode, formulaStep,
    assignmentCodeCode, assignmentCodeStep,
    assignmentStepCode, assignmentStepStep, bound, (raw_zero M).
  unfold bound.
  split; [exact hmodeDefined |].
  split; [exact hformulaDefined |].
  split; [exact hassignmentCodeDefined |].
  split; [exact hassignmentStepDefined |].
  split.
  - exact (raw_assignment_lt_self_succ M hPA (raw_zero M)).
  - split; [exact hrootLookup |].
    intros index rowMode rowCode rowAssignmentCode rowAssignmentStep
      hindex hlookup.
    destruct (raw_lt_succ_cases M hPA index (raw_zero M) hindex)
      as [himpossible | hzero].
    + exfalso. exact (raw_not_lt_zero M hPA index himpossible).
    + subst index.
      destruct (raw_fixedLevelStateLookup_functional M hPA
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (raw_zero M) mode root assignmentCode assignmentStep
        rowMode rowCode rowAssignmentCode rowAssignmentStep
        hrootLookup hlookup) as [-> [-> [-> ->]]].
      exact hclosed.
Qed.

Corollary raw_fixedLevelSigmaTruthCertificate_zero_of_local : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawFixedLevelSigmaZero M root assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M 0
    root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep hlocal.
  cbn [RawFixedLevelSigmaTruthCertificate].
  apply (raw_fixedLevelClosedZeroRow_singleton_traversal M hPA
    (rawFixedLevelSigmaMode M) root assignmentCode assignmentStep).
  left. split; [reflexivity | exact hlocal].
Qed.

Corollary raw_fixedLevelPiFalsityCertificate_zero_of_local : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawFixedLevelPiZero M root assignmentCode assignmentStep ->
  RawFixedLevelPiFalsityCertificate M 0
    root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep hlocal.
  cbn [RawFixedLevelPiFalsityCertificate].
  apply (raw_fixedLevelClosedZeroRow_singleton_traversal M hPA
    (rawFixedLevelPiMode M) root assignmentCode assignmentStep).
  right. split; [reflexivity | exact hlocal].
Qed.

(** The admissible zero-level domain combines honest formula/term syntax with
    both advertised rank-zero polarity domains.  Rank-zero totality is proved
    by PA induction and fixed-step beta capacity in the imported module. *)
Definition RawFixedLevelZeroTruthAdmissible (M : RawPAModel)
    (root assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelSigmaDomain M 0 root /\
  RawFixedLevelPiDomain M 0 root /\
  RawRankZeroSyntaxRealizable M root assignmentCode assignmentStep.

Arguments RawFixedLevelZeroTruthAdmissible
  M root assignmentCode assignmentStep : clear implicits.

Theorem raw_fixedLevelTruthCertificate_zero_decides : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall root assignmentCode assignmentStep,
  RawFixedLevelZeroTruthAdmissible M
    root assignmentCode assignmentStep ->
  RawFixedLevelSigmaTruthCertificate M 0
      root assignmentCode assignmentStep \/
  RawFixedLevelPiFalsityCertificate M 0
      root assignmentCode assignmentStep.
Proof.
  intros M hPA root assignmentCode assignmentStep
    [hsigmaDomain [hpiDomain hsyntax]].
  destruct (raw_rankZeroTruthCertificate_exists_of_realizable_syntax M hPA
    root assignmentCode assignmentStep hsyntax) as [output hcertificate].
  destruct hcertificate as
    [supportCode [supportStep [truthCode [truthStep hwithTables]]]].
  destruct hwithTables as [htraversal [hsupport [hlookup hbit]]].
  destruct hbit as [hzero | hone].
  - right. apply (raw_fixedLevelPiFalsityCertificate_zero_of_local M hPA).
    split; [exact hpiDomain |].
    exists supportCode, supportStep, truthCode, truthStep.
    split; [exact htraversal |].
    split; [exact hsupport |].
    split.
    + rewrite <- hzero. exact hlookup.
    + left. reflexivity.
  - left. apply (raw_fixedLevelSigmaTruthCertificate_zero_of_local M hPA).
    split; [exact hsigmaDomain |].
    change (output = rawNumeralValue M 1) in hone.
    exists supportCode, supportStep, truthCode, truthStep.
    split; [exact htraversal |].
    split; [exact hsupport |].
    split.
    + rewrite <- hone. exact hlookup.
    + right. reflexivity.
Qed.

(** ------------------------------------------------------------------
    The exact remaining positive-level seam.

    Formula-syntax postorders alone do not supply this property: preferred
    quantifier rows introduce new assignments, so the state schedule is a
    postorder of (polarity, formula, assignment) triples rather than merely a
    postorder of formula codes.  A subsequent totality proof must construct
    such schedules internally.  This definition records precisely that
    obligation and nothing stronger, such as semantic truth for arbitrary
    nonstandard codes. *)
Definition RawFixedLevelPositiveTruthScheduleRealizationFor
    (M : RawPAModel)
    (admissible : nat -> M -> M -> M -> Prop) : Prop :=
  forall lower root assignmentCode assignmentStep,
    admissible (S lower) root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M (S lower)
        root assignmentCode assignmentStep \/
    RawFixedLevelPiFalsityCertificate M (S lower)
        root assignmentCode assignmentStep.

Definition RawFixedLevelTruthCertificateTotalityFor
    (M : RawPAModel)
    (admissible : nat -> M -> M -> M -> Prop) : Prop :=
  forall level root assignmentCode assignmentStep,
    admissible level root assignmentCode assignmentStep ->
    RawFixedLevelSigmaTruthCertificate M level
        root assignmentCode assignmentStep \/
    RawFixedLevelPiFalsityCertificate M level
        root assignmentCode assignmentStep.

Arguments RawFixedLevelPositiveTruthScheduleRealizationFor
  M admissible : clear implicits.
Arguments RawFixedLevelTruthCertificateTotalityFor
  M admissible : clear implicits.

Theorem raw_fixedLevelTruthCertificate_totality_from_positive_schedule :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall admissible,
  (forall root assignmentCode assignmentStep,
    admissible 0 root assignmentCode assignmentStep ->
    RawFixedLevelZeroTruthAdmissible M
      root assignmentCode assignmentStep) ->
  RawFixedLevelPositiveTruthScheduleRealizationFor M admissible ->
  RawFixedLevelTruthCertificateTotalityFor M admissible.
Proof.
  intros M hPA admissible hzero hpositive
    [|lower] root assignmentCode assignmentStep hadmissible.
  - apply (raw_fixedLevelTruthCertificate_zero_decides M hPA).
    exact (hzero root assignmentCode assignmentStep hadmissible).
  - exact (hpositive lower root assignmentCode assignmentStep hadmissible).
Qed.

End PABoundedRawCodedFixedLevelTruthTraversal.
