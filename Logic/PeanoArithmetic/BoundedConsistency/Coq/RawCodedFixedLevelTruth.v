(**
  Externally indexed local rows for fixed-level partial truth.

  The two polarities are chosen so that their positive evidence is finite:
  Sigma evidence asserts truth, while Pi evidence asserts falsity.  A state
  in a model-internal postorder table stores four fields: its polarity mode,
  formula code, assignment code, and assignment step.  Boolean and preferred
  quantifier rows point only to strictly earlier states.  The opposite
  quantifier is discharged by negating the recursively generated evidence
  formula at the preceding external level.

  This file first exposes the transparent rank domains, state-table access,
  and complete successor-row formulae together with exact semantics in every
  raw arithmetic structure.  The final section names the global table
  assembly interface.  No totality or semantic soundness theorem is claimed:
  those require a separate induction over the assembled postorder table.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthTraversal.

Import ListNotations.

Module PABoundedRawCodedFixedLevelTruth.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthTraversal.

(** ------------------------------------------------------------------
    Small formula combinators and lift facts. *)

Definition fixedLevelAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition fixedLevelAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition fixedLevelAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition fixedLevelAnd6 (a b c d f g : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f g)))).

Definition fixedLevelOr6 (a b c d f g : formula) : formula :=
  pOr a (pOr b (pOr c (pOr d (pOr f g)))).

Definition fixedLevelOr7 (a b c d f g h : formula) : formula :=
  pOr a (pOr b (pOr c (pOr d (pOr f (pOr g h))))).

Definition fixedLevelEx2 (body : formula) : formula := pEx (pEx body).

Definition fixedLevelEx3 (body : formula) : formula :=
  pEx (pEx (pEx body)).

Definition fixedLevelEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

Lemma raw_fixedLevel_eval_liftTerm_two : forall (M : RawPAModel)
    a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_fixedLevel_eval_liftTerm_three : forall (M : RawPAModel)
    a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma raw_fixedLevel_eval_liftTerm_eight : forall (M : RawPAModel)
    a b c d f g h i (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i e))))))))
    (liftTerm 8 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro j.
  replace (j + 8) with (S (S (S (S (S (S (S (S j)))))))) by lia.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Polarity-aware rank domains. *)

Definition fixedLevelSigmaDomainTermAt (level : nat) (code : term) : formula :=
  fixedLevelEx2
    (pAnd
      (codedFormulaRankTermAt (liftTerm 2 code) (tVar 1) (tVar 0))
      (Formula.leTermAt (tVar 1) (Term.numeral level))).

Definition fixedLevelPiDomainTermAt (level : nat) (code : term) : formula :=
  fixedLevelEx2
    (pAnd
      (codedFormulaRankTermAt (liftTerm 2 code) (tVar 1) (tVar 0))
      (Formula.leTermAt (tVar 0) (Term.numeral level))).

Definition RawFixedLevelSigmaDomain (M : RawPAModel)
    (level : nat) (code : M) : Prop :=
  exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\
    rawLe M sigma (rawNumeralValue M level).

Definition RawFixedLevelPiDomain (M : RawPAModel)
    (level : nat) (code : M) : Prop :=
  exists sigma pi : M,
    RawCodedFormulaRank M code sigma pi /\
    rawLe M pi (rawNumeralValue M level).

Arguments RawFixedLevelSigmaDomain M level code : clear implicits.
Arguments RawFixedLevelPiDomain M level code : clear implicits.

Lemma raw_sat_fixedLevelSigmaDomainTermAt_iff : forall
    (M : RawPAModel) e level code,
  raw_formula_sat M e (fixedLevelSigmaDomainTermAt level code) <->
  RawFixedLevelSigmaDomain M level (raw_term_eval M e code).
Proof.
  intros M e level code.
  unfold fixedLevelSigmaDomainTermAt, fixedLevelEx2,
    RawFixedLevelSigmaDomain.
  cbn [raw_formula_sat].
  split.
  - intros [sigma [pi [hrankSat hleSat]]].
    exists sigma, pi. split.
    + apply (proj1 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))) in hrankSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hrankSat.
      cbn [raw_term_eval scons] in hrankSat. exact hrankSat.
    + apply (proj1 (raw_sat_leTermAt_iff_rank M
        (tVar 1) (Term.numeral level)
        (scons M pi (scons M sigma e)))) in hleSat.
      cbn [raw_term_eval scons] in hleSat.
      rewrite raw_term_eval_numeral in hleSat. exact hleSat.
  - intros [sigma [pi [hrank hle]]].
    exists sigma, pi. split.
    + apply (proj2 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hrank.
    + apply (proj2 (raw_sat_leTermAt_iff_rank M
        (tVar 1) (Term.numeral level)
        (scons M pi (scons M sigma e)))).
      cbn [raw_term_eval scons].
      rewrite raw_term_eval_numeral. exact hle.
Qed.

Lemma raw_sat_fixedLevelPiDomainTermAt_iff : forall
    (M : RawPAModel) e level code,
  raw_formula_sat M e (fixedLevelPiDomainTermAt level code) <->
  RawFixedLevelPiDomain M level (raw_term_eval M e code).
Proof.
  intros M e level code.
  unfold fixedLevelPiDomainTermAt, fixedLevelEx2,
    RawFixedLevelPiDomain.
  cbn [raw_formula_sat].
  split.
  - intros [sigma [pi [hrankSat hleSat]]].
    exists sigma, pi. split.
    + apply (proj1 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))) in hrankSat.
      rewrite raw_fixedLevel_eval_liftTerm_two in hrankSat.
      cbn [raw_term_eval scons] in hrankSat. exact hrankSat.
    + apply (proj1 (raw_sat_leTermAt_iff_rank M
        (tVar 0) (Term.numeral level)
        (scons M pi (scons M sigma e)))) in hleSat.
      cbn [raw_term_eval scons] in hleSat.
      rewrite raw_term_eval_numeral in hleSat. exact hleSat.
  - intros [sigma [pi [hrank hle]]].
    exists sigma, pi. split.
    + apply (proj2 (raw_sat_codedFormulaRankTermAt_iff M
        (scons M pi (scons M sigma e))
        (liftTerm 2 code) (tVar 1) (tVar 0))).
      rewrite raw_fixedLevel_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hrank.
    + apply (proj2 (raw_sat_leTermAt_iff_rank M
        (tVar 0) (Term.numeral level)
        (scons M pi (scons M sigma e)))).
      cbn [raw_term_eval scons].
      rewrite raw_term_eval_numeral. exact hle.
Qed.

Lemma raw_fixedLevelSigmaDomain_mono : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  RawFixedLevelSigmaDomain M level code ->
  RawFixedLevelSigmaDomain M (S level) code.
Proof.
  intros M hPA level code [sigma [pi [hrank hle]]].
  exists sigma, pi. split; [exact hrank |].
  eapply raw_le_trans; [exact hPA | exact hle |].
  apply raw_lt_to_le.
  apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
Qed.

Lemma raw_fixedLevelPiDomain_mono : forall
    (M : RawPAModel), RawPASatisfies M -> forall level code,
  RawFixedLevelPiDomain M level code ->
  RawFixedLevelPiDomain M (S level) code.
Proof.
  intros M hPA level code [sigma [pi [hrank hle]]].
  exists sigma, pi. split; [exact hrank |].
  eapply raw_le_trans; [exact hPA | exact hle |].
  apply raw_lt_to_le.
  apply raw_lt_numeralValue_of_lt; [exact hPA | lia].
Qed.

(** ------------------------------------------------------------------
    Four synchronized fields of a postorder state. *)

Definition fixedLevelStateLookupTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep : term) : formula :=
  fixedLevelAnd4
    (codedAssignmentLookupTermAt modeCode modeStep index mode)
    (codedAssignmentLookupTermAt formulaCode formulaStep index code)
    (codedAssignmentLookupTermAt
      assignmentCodeCode assignmentCodeStep index assignmentCode)
    (codedAssignmentLookupTermAt
      assignmentStepCode assignmentStepStep index assignmentStep).

Definition RawFixedLevelStateLookup (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep : M) : Prop :=
  RawCodedAssignmentLookup M modeCode modeStep index mode /\
  RawCodedAssignmentLookup M formulaCode formulaStep index code /\
  RawCodedAssignmentLookup M
    assignmentCodeCode assignmentCodeStep index assignmentCode /\
  RawCodedAssignmentLookup M
    assignmentStepCode assignmentStepStep index assignmentStep.

Arguments RawFixedLevelStateLookup
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep : clear implicits.

Lemma raw_sat_fixedLevelStateLookupTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    index mode code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelStateLookupTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      index mode code assignmentCode assignmentStep) <->
  RawFixedLevelStateLookup M
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
  intros. unfold fixedLevelStateLookupTermAt,
    RawFixedLevelStateLookup, fixedLevelAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff. reflexivity.
Qed.

Definition fixedLevelEarlierStateTermAt
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep : term) : formula :=
  pAnd
    (Formula.ltTermAt childIndex currentIndex)
    (fixedLevelStateLookupTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep).

Definition RawFixedLevelEarlierState (M : RawPAModel)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep : M) : Prop :=
  rawLt M childIndex currentIndex /\
  RawFixedLevelStateLookup M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep.

Arguments RawFixedLevelEarlierState
  M modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep : clear implicits.

Lemma raw_sat_fixedLevelEarlierStateTermAt_iff : forall
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex expectedMode childCode
    childAssignmentCode childAssignmentStep,
  raw_formula_sat M e
    (fixedLevelEarlierStateTermAt
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex childIndex expectedMode childCode
      childAssignmentCode childAssignmentStep) <->
  RawFixedLevelEarlierState M
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e childIndex)
    (raw_term_eval M e expectedMode) (raw_term_eval M e childCode)
    (raw_term_eval M e childAssignmentCode)
    (raw_term_eval M e childAssignmentStep).
Proof.
  intros. unfold fixedLevelEarlierStateTermAt,
    RawFixedLevelEarlierState.
  cbn [raw_formula_sat].
  rewrite raw_sat_ltTermAt_iff,
    raw_sat_fixedLevelStateLookupTermAt_iff. reflexivity.
Qed.

(** Mode zero means Sigma truth; mode one means Pi falsity. *)
Definition rawFixedLevelSigmaMode (M : RawPAModel) : M := raw_zero M.
Definition rawFixedLevelPiMode (M : RawPAModel) : M := rawNumeralValue M 1.

(** ------------------------------------------------------------------
    Level-zero leaves. *)

Definition fixedLevelSigmaZeroTermAt
    (code assignmentCode assignmentStep : term) : formula :=
  pAnd
    (fixedLevelSigmaDomainTermAt 0 code)
    (rankZeroTruthCertificateTermAt
      code (Term.numeral 1) assignmentCode assignmentStep).

Definition fixedLevelPiZeroTermAt
    (code assignmentCode assignmentStep : term) : formula :=
  pAnd
    (fixedLevelPiDomainTermAt 0 code)
    (rankZeroTruthCertificateTermAt
      code tZero assignmentCode assignmentStep).

Definition RawFixedLevelSigmaZero (M : RawPAModel)
    (code assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelSigmaDomain M 0 code /\
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
    assignmentCode assignmentStep.

Definition RawFixedLevelPiZero (M : RawPAModel)
    (code assignmentCode assignmentStep : M) : Prop :=
  RawFixedLevelPiDomain M 0 code /\
  RawRankZeroTruthCertificate M code (raw_zero M)
    assignmentCode assignmentStep.

Arguments RawFixedLevelSigmaZero M code assignmentCode assignmentStep
  : clear implicits.
Arguments RawFixedLevelPiZero M code assignmentCode assignmentStep
  : clear implicits.

Lemma raw_sat_fixedLevelSigmaZeroTermAt_iff : forall
    (M : RawPAModel) e code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelSigmaZeroTermAt code assignmentCode assignmentStep) <->
  RawFixedLevelSigmaZero M
    (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelSigmaZeroTermAt, RawFixedLevelSigmaZero.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff,
    raw_sat_rankZeroTruthCertificateTermAt_iff,
    raw_term_eval_numeral. reflexivity.
Qed.

Lemma raw_sat_fixedLevelPiZeroTermAt_iff : forall
    (M : RawPAModel) e code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelPiZeroTermAt code assignmentCode assignmentStep) <->
  RawFixedLevelPiZero M
    (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode)
    (raw_term_eval M e assignmentStep).
Proof.
  intros. unfold fixedLevelPiZeroTermAt, RawFixedLevelPiZero.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelPiDomainTermAt_iff,
    raw_sat_rankZeroTruthCertificateTermAt_iff. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Opposite-quantifier counterexamples.

    Truth of a universal formula at a Sigma level means that there is no
    binder value whose extended assignment carries lower-level Pi-falsity
    evidence for the child.  Dually, Pi-falsity of an existential formula
    means that there is no extension carrying lower-level Sigma-truth
    evidence.  The three existential variables below are, from outermost to
    innermost, the binder value, the extended assignment code, and its beta
    step.  Naming this clause separately makes that scoping visible and keeps
    the successor-row semantics from accidentally reusing the old assignment.
*)

Definition fixedLevelNoBinderCounterexampleTermAt
    (lowerEvidence : formula)
    (assignmentCode assignmentStep bound : term) : formula :=
  pImp
    (fixedLevelEx3
      (pAnd
        (codedAssignmentPrependTermAt
          (liftTerm 3 assignmentCode) (liftTerm 3 assignmentStep)
          (tVar 2) (liftTerm 3 bound) (tVar 1) (tVar 0))
        lowerEvidence))
    pBot.

Definition RawFixedLevelNoBinderCounterexample (M : RawPAModel)
    (lowerEvidence : M -> M -> M -> Prop)
    (assignmentCode assignmentStep bound : M) : Prop :=
  ~ exists binderWitness binderAssignmentCode binderAssignmentStep : M,
      RawCodedAssignmentPrepend M assignmentCode assignmentStep
        binderWitness bound binderAssignmentCode binderAssignmentStep /\
      lowerEvidence
        binderWitness binderAssignmentCode binderAssignmentStep.

Arguments RawFixedLevelNoBinderCounterexample
  M lowerEvidence assignmentCode assignmentStep bound : clear implicits.

(** This expanded lemma is intentionally stated at the proposition exposed by
    [raw_formula_sat].  It lets larger row proofs rewrite the whole quantified
    clause at once; rewriting only the prepend atom cannot cross Coq binders. *)
Lemma raw_fixedLevel_noBinderCounterexample_expanded_iff : forall
    (M : RawPAModel) e lowerEvidence assignmentCode assignmentStep bound,
  (~ exists binderWitness binderAssignmentCode binderAssignmentStep : M,
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        (codedAssignmentPrependTermAt
          (liftTerm 3 assignmentCode) (liftTerm 3 assignmentStep)
          (tVar 2) (liftTerm 3 bound) (tVar 1) (tVar 0)) /\
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerEvidence) <->
  RawFixedLevelNoBinderCounterexample M
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerEvidence)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e bound).
Proof.
  intros M e lowerEvidence assignmentCode assignmentStep bound.
  unfold RawFixedLevelNoBinderCounterexample.
  split.
  - intros hformula
      [binderWitness [binderAssignmentCode [binderAssignmentStep
        [hprepend hlower]]]].
    apply hformula.
    exists binderWitness, binderAssignmentCode, binderAssignmentStep.
    split; [|exact hlower].
    apply (proj2 (raw_sat_codedAssignmentPrependTermAt_iff M
      (liftTerm 3 assignmentCode) (liftTerm 3 assignmentStep)
      (tVar 2) (liftTerm 3 bound) (tVar 1) (tVar 0)
      (scons M binderAssignmentStep
        (scons M binderAssignmentCode (scons M binderWitness e))))).
    repeat rewrite raw_fixedLevel_eval_liftTerm_three.
    cbn [raw_term_eval scons].
    exact hprepend.
  - intros hraw
      [binderWitness [binderAssignmentCode [binderAssignmentStep
        [hprependSat hlower]]]].
    apply hraw.
    exists binderWitness, binderAssignmentCode, binderAssignmentStep.
    split; [|exact hlower].
    apply (proj1 (raw_sat_codedAssignmentPrependTermAt_iff M
      (liftTerm 3 assignmentCode) (liftTerm 3 assignmentStep)
      (tVar 2) (liftTerm 3 bound) (tVar 1) (tVar 0)
      (scons M binderAssignmentStep
        (scons M binderAssignmentCode (scons M binderWitness e)))))
      in hprependSat.
    repeat rewrite raw_fixedLevel_eval_liftTerm_three in hprependSat.
    cbn [raw_term_eval scons] in hprependSat.
    exact hprependSat.
Qed.

Lemma raw_sat_fixedLevelNoBinderCounterexampleTermAt_iff : forall
    (M : RawPAModel) e lowerEvidence assignmentCode assignmentStep bound,
  raw_formula_sat M e
    (fixedLevelNoBinderCounterexampleTermAt lowerEvidence
      assignmentCode assignmentStep bound) <->
  RawFixedLevelNoBinderCounterexample M
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerEvidence)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e bound).
Proof.
  intros M e lowerEvidence assignmentCode assignmentStep bound.
  unfold fixedLevelNoBinderCounterexampleTermAt, fixedLevelEx3.
  cbn [raw_formula_sat].
  apply raw_fixedLevel_noBinderCounterexample_expanded_iff.
Qed.

(** ------------------------------------------------------------------
    Complete successor witness rows.

    The eight generic witnesses are, in order: left state index, left formula
    code, right state index, right formula code, binder witness, new
    assignment code, new assignment step, and a spare slot reserved for the
    global assembler.  Keeping one fixed arity makes a single PA row checker
    usable for every constructor. *)

Definition fixedLevelSigmaSuccessorWitnessRowTermAt
    (level : nat) (lowerPiEvidence : formula)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : term) : formula :=
  pAnd
    (fixedLevelSigmaDomainTermAt (S level) code)
    (fixedLevelOr7
      (rankZeroTruthCertificateTermAt
        code (Term.numeral 1) assignmentCode assignmentStep)
      (fixedLevelAnd3
        (formulaImpCodeTermAt code leftCode rightCode)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex (Term.numeral 1) leftCode
          assignmentCode assignmentStep)
        (pEq spare spare))
      (fixedLevelAnd3
        (formulaImpCodeTermAt code leftCode rightCode)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex rightIndex tZero rightCode
          assignmentCode assignmentStep)
        (pEq spare spare))
      (fixedLevelAnd3
        (formulaAndCodeTermAt code leftCode rightCode)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex tZero leftCode
          assignmentCode assignmentStep)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex rightIndex tZero rightCode
          assignmentCode assignmentStep))
      (pAnd
        (formulaOrCodeTermAt code leftCode rightCode)
        (pOr
          (fixedLevelEarlierStateTermAt
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            currentIndex leftIndex tZero leftCode
            assignmentCode assignmentStep)
          (fixedLevelEarlierStateTermAt
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            currentIndex rightIndex tZero rightCode
            assignmentCode assignmentStep)))
      (fixedLevelAnd3
        (formulaExCodeTermAt code leftCode)
        (codedAssignmentPrependTermAt
          assignmentCode assignmentStep witness code
          newAssignmentCode newAssignmentStep)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex tZero leftCode
          newAssignmentCode newAssignmentStep))
      (pAnd
        (formulaAllCodeTermAt code leftCode)
        (fixedLevelNoBinderCounterexampleTermAt lowerPiEvidence
          assignmentCode assignmentStep code))).

Definition fixedLevelPiSuccessorWitnessRowTermAt
    (level : nat) (lowerSigmaEvidence : formula)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : term) : formula :=
  pAnd
    (fixedLevelPiDomainTermAt (S level) code)
    (fixedLevelOr6
      (rankZeroTruthCertificateTermAt
        code tZero assignmentCode assignmentStep)
      (fixedLevelAnd4
        (formulaImpCodeTermAt code leftCode rightCode)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex tZero leftCode
          assignmentCode assignmentStep)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex rightIndex (Term.numeral 1) rightCode
          assignmentCode assignmentStep)
        (pEq spare spare))
      (pAnd
        (formulaAndCodeTermAt code leftCode rightCode)
        (pOr
          (fixedLevelEarlierStateTermAt
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            currentIndex leftIndex (Term.numeral 1) leftCode
            assignmentCode assignmentStep)
          (fixedLevelEarlierStateTermAt
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            currentIndex rightIndex (Term.numeral 1) rightCode
            assignmentCode assignmentStep)))
      (fixedLevelAnd3
        (formulaOrCodeTermAt code leftCode rightCode)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex (Term.numeral 1) leftCode
          assignmentCode assignmentStep)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex rightIndex (Term.numeral 1) rightCode
          assignmentCode assignmentStep))
      (fixedLevelAnd3
        (formulaAllCodeTermAt code leftCode)
        (codedAssignmentPrependTermAt
          assignmentCode assignmentStep witness code
          newAssignmentCode newAssignmentStep)
        (fixedLevelEarlierStateTermAt
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex leftIndex (Term.numeral 1) leftCode
          newAssignmentCode newAssignmentStep))
      (pAnd
        (formulaExCodeTermAt code leftCode)
        (fixedLevelNoBinderCounterexampleTermAt lowerSigmaEvidence
          assignmentCode assignmentStep code))).

Definition RawFixedLevelSigmaSuccessorWitnessRow (M : RawPAModel)
    (level : nat) (lowerPiEvidence : M -> M -> M -> Prop)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M) : Prop :=
  RawFixedLevelSigmaDomain M (S level) code /\
  (RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
      assignmentCode assignmentStep \/
   (code = rawFormulaImpCode M leftCode rightCode /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (rawNumeralValue M 1) leftCode
      assignmentCode assignmentStep /\ spare = spare) \/
   (code = rawFormulaImpCode M leftCode rightCode /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (raw_zero M) rightCode
      assignmentCode assignmentStep /\ spare = spare) \/
   (code = rawFormulaAndCode M leftCode rightCode /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      assignmentCode assignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (raw_zero M) rightCode
      assignmentCode assignmentStep) \/
   (code = rawFormulaOrCode M leftCode rightCode /\
    (RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      assignmentCode assignmentStep \/
     RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (raw_zero M) rightCode
      assignmentCode assignmentStep)) \/
   (code = rawFormulaExCode M leftCode /\
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
      newAssignmentCode newAssignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      newAssignmentCode newAssignmentStep) \/
   (code = rawFormulaAllCode M leftCode /\
    RawFixedLevelNoBinderCounterexample M lowerPiEvidence
      assignmentCode assignmentStep code)).

Definition RawFixedLevelPiSuccessorWitnessRow (M : RawPAModel)
    (level : nat) (lowerSigmaEvidence : M -> M -> M -> Prop)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode
      witness newAssignmentCode newAssignmentStep spare : M) : Prop :=
  RawFixedLevelPiDomain M (S level) code /\
  (RawRankZeroTruthCertificate M code (raw_zero M)
      assignmentCode assignmentStep \/
   (code = rawFormulaImpCode M leftCode rightCode /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (raw_zero M) leftCode
      assignmentCode assignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (rawNumeralValue M 1) rightCode
      assignmentCode assignmentStep /\ spare = spare) \/
   (code = rawFormulaAndCode M leftCode rightCode /\
    (RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (rawNumeralValue M 1) leftCode
      assignmentCode assignmentStep \/
     RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (rawNumeralValue M 1) rightCode
      assignmentCode assignmentStep)) \/
   (code = rawFormulaOrCode M leftCode rightCode /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (rawNumeralValue M 1) leftCode
      assignmentCode assignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex rightIndex (rawNumeralValue M 1) rightCode
      assignmentCode assignmentStep) \/
   (code = rawFormulaAllCode M leftCode /\
    RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
      newAssignmentCode newAssignmentStep /\
    RawFixedLevelEarlierState M
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex leftIndex (rawNumeralValue M 1) leftCode
      newAssignmentCode newAssignmentStep) \/
   (code = rawFormulaExCode M leftCode /\
    RawFixedLevelNoBinderCounterexample M lowerSigmaEvidence
      assignmentCode assignmentStep code)).

Arguments RawFixedLevelSigmaSuccessorWitnessRow
  M level lowerPiEvidence modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare : clear implicits.
Arguments RawFixedLevelPiSuccessorWitnessRow
  M level lowerSigmaEvidence modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare : clear implicits.

Lemma raw_sat_fixedLevelSigmaSuccessorWitnessRowTermAt_iff : forall
    (M : RawPAModel) e level lowerPiEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  raw_formula_sat M e
    (fixedLevelSigmaSuccessorWitnessRowTermAt level lowerPiEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode witness
      newAssignmentCode newAssignmentStep spare) <->
  RawFixedLevelSigmaSuccessorWitnessRow M level
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerPiEvidence)
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e leftIndex) (raw_term_eval M e leftCode)
    (raw_term_eval M e rightIndex) (raw_term_eval M e rightCode)
    (raw_term_eval M e witness) (raw_term_eval M e newAssignmentCode)
    (raw_term_eval M e newAssignmentStep) (raw_term_eval M e spare).
Proof.
  intros. unfold fixedLevelSigmaSuccessorWitnessRowTermAt,
    RawFixedLevelSigmaSuccessorWitnessRow,
    fixedLevelAnd3, fixedLevelAnd4, fixedLevelOr7, fixedLevelEx3.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelSigmaDomainTermAt_iff,
    raw_sat_rankZeroTruthCertificateTermAt_iff,
    !raw_sat_formulaImpCodeTermAt_iff,
    raw_sat_formulaAndCodeTermAt_iff,
    raw_sat_formulaOrCodeTermAt_iff,
    raw_sat_formulaExCodeTermAt_iff,
    raw_sat_formulaAllCodeTermAt_iff,
    !raw_sat_fixedLevelEarlierStateTermAt_iff,
    raw_sat_fixedLevelNoBinderCounterexampleTermAt_iff,
    !raw_sat_codedAssignmentPrependTermAt_iff,
    !raw_term_eval_numeral.
  repeat rewrite raw_fixedLevel_eval_liftTerm_three.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

Lemma raw_sat_fixedLevelPiSuccessorWitnessRowTermAt_iff : forall
    (M : RawPAModel) e level lowerSigmaEvidence
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    leftIndex leftCode rightIndex rightCode witness
    newAssignmentCode newAssignmentStep spare,
  raw_formula_sat M e
    (fixedLevelPiSuccessorWitnessRowTermAt level lowerSigmaEvidence
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep
      leftIndex leftCode rightIndex rightCode witness
      newAssignmentCode newAssignmentStep spare) <->
  RawFixedLevelPiSuccessorWitnessRow M level
    (fun binderWitness binderAssignmentCode binderAssignmentStep =>
      raw_formula_sat M
        (scons M binderAssignmentStep
          (scons M binderAssignmentCode (scons M binderWitness e)))
        lowerSigmaEvidence)
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)
    (raw_term_eval M e leftIndex) (raw_term_eval M e leftCode)
    (raw_term_eval M e rightIndex) (raw_term_eval M e rightCode)
    (raw_term_eval M e witness) (raw_term_eval M e newAssignmentCode)
    (raw_term_eval M e newAssignmentStep) (raw_term_eval M e spare).
Proof.
  intros. unfold fixedLevelPiSuccessorWitnessRowTermAt,
    RawFixedLevelPiSuccessorWitnessRow,
    fixedLevelAnd3, fixedLevelAnd4, fixedLevelOr6, fixedLevelEx3.
  cbn [raw_formula_sat].
  rewrite raw_sat_fixedLevelPiDomainTermAt_iff,
    raw_sat_rankZeroTruthCertificateTermAt_iff,
    raw_sat_formulaImpCodeTermAt_iff,
    raw_sat_formulaAndCodeTermAt_iff,
    raw_sat_formulaOrCodeTermAt_iff,
    raw_sat_formulaAllCodeTermAt_iff,
    raw_sat_formulaExCodeTermAt_iff,
    !raw_sat_fixedLevelEarlierStateTermAt_iff,
    raw_sat_fixedLevelNoBinderCounterexampleTermAt_iff,
    !raw_sat_codedAssignmentPrependTermAt_iff,
    !raw_term_eval_numeral.
  repeat rewrite raw_fixedLevel_eval_liftTerm_three.
  cbn [raw_term_eval scons].
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Transparent external-level recursion.

    These are deliberately called *local* evidence formulae.  At a positive
    level they verify one state and consult the shared beta tables for
    same-level Boolean children.  The opposite-quantifier complement is a
    genuine recursive call at the smaller external level.  Global closure of
    every consulted state is the separate assembly obligation below. *)

Fixpoint fixedLevelSigmaLocalTermAt (level : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep : term) : formula :=
  match level with
  | 0 => fixedLevelSigmaZeroTermAt code assignmentCode assignmentStep
  | S lower =>
      fixedLevelEx8
        (fixedLevelSigmaSuccessorWitnessRowTermAt lower
          (fixedLevelPiLocalTermAt lower
            (liftTerm 3 (liftTerm 8 modeCode))
            (liftTerm 3 (liftTerm 8 modeStep))
            (liftTerm 3 (liftTerm 8 formulaCode))
            (liftTerm 3 (liftTerm 8 formulaStep))
            (liftTerm 3 (liftTerm 8 assignmentCodeCode))
            (liftTerm 3 (liftTerm 8 assignmentCodeStep))
            (liftTerm 3 (liftTerm 8 assignmentStepCode))
            (liftTerm 3 (liftTerm 8 assignmentStepStep))
            (liftTerm 3 (liftTerm 8 currentIndex))
            (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0))
          (liftTerm 8 modeCode) (liftTerm 8 modeStep)
          (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
          (liftTerm 8 assignmentCodeCode)
          (liftTerm 8 assignmentCodeStep)
          (liftTerm 8 assignmentStepCode)
          (liftTerm 8 assignmentStepStep)
          (liftTerm 8 currentIndex) (liftTerm 8 code)
          (liftTerm 8 assignmentCode) (liftTerm 8 assignmentStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
  end
with fixedLevelPiLocalTermAt (level : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep : term) : formula :=
  match level with
  | 0 => fixedLevelPiZeroTermAt code assignmentCode assignmentStep
  | S lower =>
      fixedLevelEx8
        (fixedLevelPiSuccessorWitnessRowTermAt lower
          (fixedLevelSigmaLocalTermAt lower
            (liftTerm 3 (liftTerm 8 modeCode))
            (liftTerm 3 (liftTerm 8 modeStep))
            (liftTerm 3 (liftTerm 8 formulaCode))
            (liftTerm 3 (liftTerm 8 formulaStep))
            (liftTerm 3 (liftTerm 8 assignmentCodeCode))
            (liftTerm 3 (liftTerm 8 assignmentCodeStep))
            (liftTerm 3 (liftTerm 8 assignmentStepCode))
            (liftTerm 3 (liftTerm 8 assignmentStepStep))
            (liftTerm 3 (liftTerm 8 currentIndex))
            (liftTerm 3 (tVar 6)) (tVar 1) (tVar 0))
          (liftTerm 8 modeCode) (liftTerm 8 modeStep)
          (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
          (liftTerm 8 assignmentCodeCode)
          (liftTerm 8 assignmentCodeStep)
          (liftTerm 8 assignmentStepCode)
          (liftTerm 8 assignmentStepStep)
          (liftTerm 8 currentIndex) (liftTerm 8 code)
          (liftTerm 8 assignmentCode) (liftTerm 8 assignmentStep)
          (tVar 7) (tVar 6) (tVar 5) (tVar 4)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
  end.

Fixpoint RawFixedLevelSigmaLocal (M : RawPAModel) (level : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep : M) : Prop :=
  match level with
  | 0 => RawFixedLevelSigmaZero M code assignmentCode assignmentStep
  | S lower =>
      exists leftIndex leftCode rightIndex rightCode
        witness newAssignmentCode newAssignmentStep spare : M,
        RawFixedLevelSigmaSuccessorWitnessRow M lower
          (fun _ binderAssignmentCode binderAssignmentStep =>
            RawFixedLevelPiLocal M lower
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              currentIndex leftCode
              binderAssignmentCode binderAssignmentStep)
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex code assignmentCode assignmentStep
          leftIndex leftCode rightIndex rightCode
          witness newAssignmentCode newAssignmentStep spare
  end
with RawFixedLevelPiLocal (M : RawPAModel) (level : nat)
    (modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep : M) : Prop :=
  match level with
  | 0 => RawFixedLevelPiZero M code assignmentCode assignmentStep
  | S lower =>
      exists leftIndex leftCode rightIndex rightCode
        witness newAssignmentCode newAssignmentStep spare : M,
        RawFixedLevelPiSuccessorWitnessRow M lower
          (fun _ binderAssignmentCode binderAssignmentStep =>
            RawFixedLevelSigmaLocal M lower
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              currentIndex leftCode
              binderAssignmentCode binderAssignmentStep)
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          currentIndex code assignmentCode assignmentStep
          leftIndex leftCode rightIndex rightCode
          witness newAssignmentCode newAssignmentStep spare
  end.

Arguments RawFixedLevelSigmaLocal
  M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep : clear implicits.
Arguments RawFixedLevelPiLocal
  M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep : clear implicits.

(** The two exact semantic equivalences are proved simultaneously because a
    successor Sigma row contains the preceding Pi formula and conversely. *)
Theorem raw_sat_fixedLevelLocalTermAt_iff : forall level,
  (forall (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
    raw_formula_sat M e
      (fixedLevelSigmaLocalTermAt level
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        currentIndex code assignmentCode assignmentStep) <->
    RawFixedLevelSigmaLocal M level
      (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
      (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
      (raw_term_eval M e assignmentCodeCode)
      (raw_term_eval M e assignmentCodeStep)
      (raw_term_eval M e assignmentStepCode)
      (raw_term_eval M e assignmentStepStep)
      (raw_term_eval M e currentIndex) (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)) /\
  (forall (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
    raw_formula_sat M e
      (fixedLevelPiLocalTermAt level
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        currentIndex code assignmentCode assignmentStep) <->
    RawFixedLevelPiLocal M level
      (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
      (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
      (raw_term_eval M e assignmentCodeCode)
      (raw_term_eval M e assignmentCodeStep)
      (raw_term_eval M e assignmentStepCode)
      (raw_term_eval M e assignmentStepStep)
      (raw_term_eval M e currentIndex) (raw_term_eval M e code)
      (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep)).
Proof.
  induction level as [|level [IHsigma IHpi]].
  - split; intros M e modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep; cbn.
    + apply raw_sat_fixedLevelSigmaZeroTermAt_iff.
    + apply raw_sat_fixedLevelPiZeroTermAt_iff.
  - split; intros M e modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep.
    + cbn [fixedLevelSigmaLocalTermAt RawFixedLevelSigmaLocal].
      unfold fixedLevelEx8. cbn [raw_formula_sat].
      setoid_rewrite raw_sat_fixedLevelSigmaSuccessorWitnessRowTermAt_iff.
      unfold RawFixedLevelSigmaSuccessorWitnessRow,
        RawFixedLevelNoBinderCounterexample.
      repeat setoid_rewrite IHpi.
      repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_three.
      repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. reflexivity.
    + cbn [fixedLevelPiLocalTermAt RawFixedLevelPiLocal].
      unfold fixedLevelEx8. cbn [raw_formula_sat].
      setoid_rewrite raw_sat_fixedLevelPiSuccessorWitnessRowTermAt_iff.
      unfold RawFixedLevelPiSuccessorWitnessRow,
        RawFixedLevelNoBinderCounterexample.
      repeat setoid_rewrite IHsigma.
      repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_three.
      repeat setoid_rewrite raw_fixedLevel_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. reflexivity.
Qed.

Corollary raw_sat_fixedLevelSigmaLocalTermAt_iff : forall level
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelSigmaLocalTermAt level
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep) <->
  RawFixedLevelSigmaLocal M level
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intro level. exact (proj1 (raw_sat_fixedLevelLocalTermAt_iff level)).
Qed.

Corollary raw_sat_fixedLevelPiLocalTermAt_iff : forall level
    (M : RawPAModel) e
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  raw_formula_sat M e
    (fixedLevelPiLocalTermAt level
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      currentIndex code assignmentCode assignmentStep) <->
  RawFixedLevelPiLocal M level
    (raw_term_eval M e modeCode) (raw_term_eval M e modeStep)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e assignmentCodeCode)
    (raw_term_eval M e assignmentCodeStep)
    (raw_term_eval M e assignmentStepCode)
    (raw_term_eval M e assignmentStepStep)
    (raw_term_eval M e currentIndex) (raw_term_eval M e code)
    (raw_term_eval M e assignmentCode) (raw_term_eval M e assignmentStep).
Proof.
  intro level. exact (proj2 (raw_sat_fixedLevelLocalTermAt_iff level)).
Qed.

(** Every local certificate explicitly carries its advertised polarity
    domain.  These facts require no global-table soundness argument. *)
Lemma raw_fixedLevelSigmaLocal_domain : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  RawFixedLevelSigmaLocal M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep ->
  RawFixedLevelSigmaDomain M level code.
Proof.
  intros M [|level] modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep h.
  - exact (proj1 h).
  - destruct h as (leftIndex & leftCode & rightIndex & rightCode & witness &
      newAssignmentCode & newAssignmentStep & spare & hrow).
    exact (proj1 hrow).
Qed.

Lemma raw_fixedLevelPiLocal_domain : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  RawFixedLevelPiLocal M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep ->
  RawFixedLevelPiDomain M level code.
Proof.
  intros M [|level] modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep h.
  - exact (proj1 h).
  - destruct h as (leftIndex & leftCode & rightIndex & rightCode & witness &
      newAssignmentCode & newAssignmentStep & spare & hrow).
    exact (proj1 hrow).
Qed.

(** Basic introduction laws expose the intended compositional reading of the
    row checker.  They are deliberately local: no conclusion about the
    semantic truth of an arbitrary nonstandard root is drawn. *)

Lemma raw_fixedLevelSigmaLocal_qf_successor : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  RawFixedLevelSigmaDomain M (S level) code ->
  RawRankZeroTruthCertificate M code (rawNumeralValue M 1)
    assignmentCode assignmentStep ->
  RawFixedLevelSigmaLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep hdomain hzero.
  exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
    (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
  split; [exact hdomain |]. now left.
Qed.

Lemma raw_fixedLevelPiLocal_qf_successor : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep,
  RawFixedLevelPiDomain M (S level) code ->
  RawRankZeroTruthCertificate M code (raw_zero M)
    assignmentCode assignmentStep ->
  RawFixedLevelPiLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep hdomain hzero.
  exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M),
    (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
  split; [exact hdomain |]. now left.
Qed.

Lemma raw_fixedLevelSigmaLocal_existential : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    childIndex childCode witness newAssignmentCode newAssignmentStep,
  RawFixedLevelSigmaDomain M (S level) code ->
  code = rawFormulaExCode M childCode ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
    newAssignmentCode newAssignmentStep ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex (raw_zero M) childCode
    newAssignmentCode newAssignmentStep ->
  RawFixedLevelSigmaLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    childIndex childCode witness newAssignmentCode newAssignmentStep
    hdomain hcode hprepend hchild.
  exists childIndex, childCode, (raw_zero M), (raw_zero M), witness,
    newAssignmentCode, newAssignmentStep, (raw_zero M).
  split; [exact hdomain |].
  right. right. right. right. right. left.
  split; [exact hcode |]. split; assumption.
Qed.

Lemma raw_fixedLevelPiLocal_universal_counterexample : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    childIndex childCode witness newAssignmentCode newAssignmentStep,
  RawFixedLevelPiDomain M (S level) code ->
  code = rawFormulaAllCode M childCode ->
  RawCodedAssignmentPrepend M assignmentCode assignmentStep witness code
    newAssignmentCode newAssignmentStep ->
  RawFixedLevelEarlierState M
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex childIndex (rawNumeralValue M 1) childCode
    newAssignmentCode newAssignmentStep ->
  RawFixedLevelPiLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep
    childIndex childCode witness newAssignmentCode newAssignmentStep
    hdomain hcode hprepend hchild.
  exists childIndex, childCode, (raw_zero M), (raw_zero M), witness,
    newAssignmentCode, newAssignmentStep, (raw_zero M).
  split; [exact hdomain |].
  right. right. right. right. left.
  split; [exact hcode |]. split; assumption.
Qed.

Lemma raw_fixedLevelSigmaLocal_universal_complement : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep childCode,
  RawFixedLevelSigmaDomain M (S level) code ->
  code = rawFormulaAllCode M childCode ->
  (~ exists binderWitness binderAssignmentCode binderAssignmentStep : M,
      RawCodedAssignmentPrepend M assignmentCode assignmentStep
        binderWitness code binderAssignmentCode binderAssignmentStep /\
      RawFixedLevelPiLocal M level
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        currentIndex childCode binderAssignmentCode binderAssignmentStep) ->
  RawFixedLevelSigmaLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep childCode
    hdomain hcode hcomplement.
  cbn [RawFixedLevelSigmaLocal].
  exists (raw_zero M), childCode, (raw_zero M), (raw_zero M),
    (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
  split; [exact hdomain |].
  right. right. right. right. right. right.
  split; assumption.
Qed.

Lemma raw_fixedLevelPiLocal_existential_complement : forall M level
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep childCode,
  RawFixedLevelPiDomain M (S level) code ->
  code = rawFormulaExCode M childCode ->
  (~ exists binderWitness binderAssignmentCode binderAssignmentStep : M,
      RawCodedAssignmentPrepend M assignmentCode assignmentStep
        binderWitness code binderAssignmentCode binderAssignmentStep /\
      RawFixedLevelSigmaLocal M level
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        currentIndex childCode binderAssignmentCode binderAssignmentStep) ->
  RawFixedLevelPiLocal M (S level)
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep.
Proof.
  intros M level modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep assignmentStepCode assignmentStepStep
    currentIndex code assignmentCode assignmentStep childCode
    hdomain hcode hcomplement.
  cbn [RawFixedLevelPiLocal].
  exists (raw_zero M), childCode, (raw_zero M), (raw_zero M),
    (raw_zero M), assignmentCode, assignmentStep, (raw_zero M).
  split; [exact hdomain |].
  right. right. right. right. right.
  split; assumption.
Qed.

(** The named global assembly seam.  A future table certificate will require
    every state below its bound to satisfy the matching successor row and its
    designated root state to carry the requested formula/assignment.  This is
    a definition, not an assumed theorem. *)
Definition RawFixedLevelGlobalAssemblyFor (M : RawPAModel)
    (sigmaEvidence piFalsity : nat -> M -> M -> M -> Prop) : Prop :=
  forall level root assignmentCode assignmentStep mode,
    ((mode = rawFixedLevelSigmaMode M /\
      sigmaEvidence level root assignmentCode assignmentStep) \/
     (mode = rawFixedLevelPiMode M /\
      piFalsity level root assignmentCode assignmentStep)) ->
    exists modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep bound rootIndex,
      rawLt M rootIndex bound /\
      RawFixedLevelStateLookup M
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        rootIndex mode root assignmentCode assignmentStep.

End PABoundedRawCodedFixedLevelTruth.
