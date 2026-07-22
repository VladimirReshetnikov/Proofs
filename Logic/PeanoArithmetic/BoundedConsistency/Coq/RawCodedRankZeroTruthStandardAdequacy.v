(**
  Standard-quotation adequacy for the global rank-zero truth traversal.

  This file deliberately proves only an external, standard-root theorem.
  Given an ordinary quantifier-free PA formula [phi], an arbitrary raw model
  of PA, and an external environment, we beta-code the finitely many slots
  through [formulaCode phi].  A checked decoder marks exactly canonical
  quantifier-free formula codes as supported.  The truth table stores zero or
  one according to the ordinary raw semantics.

  Atomic equality rows use the supplied-assignment interface of
  [RawCodedTermEvaluationStandardAdequacy].  Consequently every term
  certificate in the traversal uses the very same assignment code and step;
  no atom can silently choose an unrelated environment.

  Nothing here asserts realization for an arbitrary, possibly nonstandard,
  carrier code.  That stronger totality problem remains separate.
*)

From Stdlib Require Import List Arith Bool Lia ClassicalDescription.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedRankZeroTruthStep RawCodedRankZeroTruthStepFunctionality
  RawCodedTermEvaluationTraversal
  RawCodedTermEvaluationStandardAdequacy
  RawCodedRankZeroTruthTraversal.

Import ListNotations.

Module PABoundedRawCodedRankZeroTruthStandardAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedRankZeroTruthStep.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationStandardAdequacy.
Import PABoundedRawCodedRankZeroTruthTraversal.

(** ------------------------------------------------------------------
    Quantifier-free syntax and a checked standard decoder. *)

Fixpoint rankZeroFormulab (phi : formula) : bool :=
  match phi with
  | pEq _ _ => true
  | pBot => true
  | pImp lhs rhs => rankZeroFormulab lhs && rankZeroFormulab rhs
  | pAnd lhs rhs => rankZeroFormulab lhs && rankZeroFormulab rhs
  | pOr lhs rhs => rankZeroFormulab lhs && rankZeroFormulab rhs
  | pAll _ => false
  | pEx _ => false
  end.

Definition RankZeroFormula (phi : formula) : Prop :=
  rankZeroFormulab phi = true.

Lemma rankZeroFormula_imp_iff : forall left right,
  RankZeroFormula (pImp left right) <->
  RankZeroFormula left /\ RankZeroFormula right.
Proof.
  intros. unfold RankZeroFormula. cbn [rankZeroFormulab].
  apply andb_true_iff.
Qed.

Lemma rankZeroFormula_and_iff : forall left right,
  RankZeroFormula (pAnd left right) <->
  RankZeroFormula left /\ RankZeroFormula right.
Proof.
  intros. unfold RankZeroFormula. cbn [rankZeroFormulab].
  apply andb_true_iff.
Qed.

Lemma rankZeroFormula_or_iff : forall left right,
  RankZeroFormula (pOr left right) <->
  RankZeroFormula left /\ RankZeroFormula right.
Proof.
  intros. unfold RankZeroFormula. cbn [rankZeroFormulab].
  apply andb_true_iff.
Qed.

(** Re-encoding is checked even though [decodeFormula] is deterministic.
    This ensures that a supported slot is literally the canonical code of
    the decoded formula rather than merely a number accepted by a future,
    more permissive decoder. *)
Definition checkedDecodeRankZeroFormula (code : nat) : option formula :=
  match decodeFormula code with
  | Some phi =>
      if Nat.eqb (formulaCode phi) code then
        if rankZeroFormulab phi then Some phi else None
      else None
  | None => None
  end.

Lemma checkedDecodeRankZeroFormula_formulaCode : forall phi,
  RankZeroFormula phi ->
  checkedDecodeRankZeroFormula (formulaCode phi) = Some phi.
Proof.
  intros phi hzero.
  unfold checkedDecodeRankZeroFormula.
  rewrite decodeFormula_formulaCode, Nat.eqb_refl, hzero.
  reflexivity.
Qed.

Lemma checkedDecodeRankZeroFormula_sound : forall code phi,
  checkedDecodeRankZeroFormula code = Some phi ->
  decodeFormula code = Some phi /\
  formulaCode phi = code /\ RankZeroFormula phi.
Proof.
  intros code phi. unfold checkedDecodeRankZeroFormula.
  destruct (decodeFormula code) as [decoded |] eqn:hdecode;
    [|discriminate].
  destruct (Nat.eqb (formulaCode decoded) code) eqn:hcode;
    [|discriminate].
  destruct (rankZeroFormulab decoded) eqn:hzero;
    [|discriminate].
  intro h. inversion h. subst decoded.
  split; [reflexivity |]. split.
  - now apply Nat.eqb_eq.
  - exact hzero.
Qed.

(** ------------------------------------------------------------------
    The canonical semantic bit and finite standard vectors. *)

Definition rawStandardFormulaTruthValue (M : RawPAModel)
    (env : nat -> M) (phi : formula) : M :=
  if excluded_middle_informative (raw_formula_sat M env phi)
  then rawTruthOne M
  else raw_zero M.

Arguments rawStandardFormulaTruthValue M env phi : clear implicits.

Lemma rawStandardFormulaTruthValue_bit : forall M env phi,
  RawTruthBit M (rawStandardFormulaTruthValue M env phi).
Proof.
  intros M env phi. unfold rawStandardFormulaTruthValue, RawTruthBit.
  destruct (excluded_middle_informative (raw_formula_sat M env phi));
    [right | left]; reflexivity.
Qed.

Lemma rawStandardFormulaTruthValue_of_sat : forall M env phi,
  raw_formula_sat M env phi ->
  rawStandardFormulaTruthValue M env phi = rawTruthOne M.
Proof.
  intros M env phi hsat. unfold rawStandardFormulaTruthValue.
  destruct (excluded_middle_informative (raw_formula_sat M env phi));
    [reflexivity | contradiction].
Qed.

Lemma rawStandardFormulaTruthValue_of_not_sat : forall M env phi,
  ~ raw_formula_sat M env phi ->
  rawStandardFormulaTruthValue M env phi = raw_zero M.
Proof.
  intros M env phi hnot. unfold rawStandardFormulaTruthValue.
  destruct (excluded_middle_informative (raw_formula_sat M env phi));
    [contradiction | reflexivity].
Qed.

Lemma rawStandardFormulaTruthValue_one_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall env phi,
  rawStandardFormulaTruthValue M env phi = rawTruthOne M <->
  raw_formula_sat M env phi.
Proof.
  intros M hPA env phi. split.
  - unfold rawStandardFormulaTruthValue.
    destruct (excluded_middle_informative (raw_formula_sat M env phi))
      as [hsat | hnot]; [exact (fun _ => hsat) |].
    intro hzero.
    exfalso. apply (raw_zero_neq_truthOne M hPA). exact hzero.
  - apply rawStandardFormulaTruthValue_of_sat.
Qed.

Lemma rawStandardFormulaTruthValue_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall env phi,
  rawStandardFormulaTruthValue M env phi = raw_zero M <->
  ~ raw_formula_sat M env phi.
Proof.
  intros M hPA env phi. split.
  - unfold rawStandardFormulaTruthValue.
    destruct (excluded_middle_informative (raw_formula_sat M env phi))
      as [hsat | hnot]; [|exact (fun _ => hnot)].
    intro hone. exfalso.
    apply (raw_zero_neq_truthOne M hPA). symmetry. exact hone.
  - apply rawStandardFormulaTruthValue_of_not_sat.
Qed.

Definition rawStandardRankZeroSupportAt (M : RawPAModel)
    (code : nat) : M :=
  match checkedDecodeRankZeroFormula code with
  | Some _ => rawTruthOne M
  | None => raw_zero M
  end.

Definition rawStandardRankZeroTruthAt (M : RawPAModel)
    (env : nat -> M) (code : nat) : M :=
  match checkedDecodeRankZeroFormula code with
  | Some phi => rawStandardFormulaTruthValue M env phi
  | None => raw_zero M
  end.

Lemma rawStandardRankZeroSupportAt_formulaCode : forall M phi,
  RankZeroFormula phi ->
  rawStandardRankZeroSupportAt M (formulaCode phi) = rawTruthOne M.
Proof.
  intros M phi hzero. unfold rawStandardRankZeroSupportAt.
  now rewrite checkedDecodeRankZeroFormula_formulaCode.
Qed.

Lemma rawStandardRankZeroTruthAt_formulaCode : forall M env phi,
  RankZeroFormula phi ->
  rawStandardRankZeroTruthAt M env (formulaCode phi) =
    rawStandardFormulaTruthValue M env phi.
Proof.
  intros M env phi hzero. unfold rawStandardRankZeroTruthAt.
  now rewrite checkedDecodeRankZeroFormula_formulaCode.
Qed.

Lemma rawStandardRankZeroTruthAt_checked : forall M env code phi,
  checkedDecodeRankZeroFormula code = Some phi ->
  rawStandardRankZeroTruthAt M env code =
    rawStandardFormulaTruthValue M env phi.
Proof.
  intros M env code phi hdecode.
  unfold rawStandardRankZeroTruthAt. now rewrite hdecode.
Qed.

Lemma rawStandardRankZeroSupportAt_one_has_formula : forall
    (M : RawPAModel), RawPASatisfies M -> forall code,
  rawStandardRankZeroSupportAt M code = rawTruthOne M ->
  exists phi, checkedDecodeRankZeroFormula code = Some phi.
Proof.
  intros M hPA code. unfold rawStandardRankZeroSupportAt.
  destruct (checkedDecodeRankZeroFormula code) as [phi |] eqn:hdecode.
  - intros _. now exists phi.
  - intro hzero. exfalso.
    apply (raw_zero_neq_truthOne M hPA). exact hzero.
Qed.

(** ------------------------------------------------------------------
    The ordinary Tarski clauses produce the five local truth rows. *)

Lemma raw_standardFormulaEqualityTruth : forall M env left right,
  RawEqualityTruth M
    (rawStandardFormulaTruthValue M env (pEq left right))
    (raw_term_eval M env left) (raw_term_eval M env right).
Proof.
  intros M env left right.
  destruct (excluded_middle_informative
    (raw_term_eval M env left = raw_term_eval M env right))
    as [heq | hneq].
  - left. split; [exact heq |].
    apply rawStandardFormulaTruthValue_of_sat. exact heq.
  - right. split; [exact hneq |].
    apply rawStandardFormulaTruthValue_of_not_sat. exact hneq.
Qed.

Lemma raw_standardFormulaBotTruth : forall M env,
  rawStandardFormulaTruthValue M env pBot = raw_zero M.
Proof.
  intros. apply rawStandardFormulaTruthValue_of_not_sat. tauto.
Qed.

Lemma raw_standardFormulaImpTruth : forall
    (M : RawPAModel), RawPASatisfies M -> forall env left right,
  RawImpTruth M
    (rawStandardFormulaTruthValue M env (pImp left right))
    (rawStandardFormulaTruthValue M env left)
    (rawStandardFormulaTruthValue M env right).
Proof.
  intros M hPA env left right.
  unfold RawImpTruth.
  repeat split; try apply rawStandardFormulaTruthValue_bit.
  destruct (excluded_middle_informative (raw_formula_sat M env left))
    as [hleft | hnleft];
  destruct (excluded_middle_informative (raw_formula_sat M env right))
    as [hright | hnright].
  - right. split.
    + right. apply rawStandardFormulaTruthValue_of_sat. exact hright.
    + apply rawStandardFormulaTruthValue_of_sat. exact (fun _ => hright).
  - left. split.
    + split.
      * apply rawStandardFormulaTruthValue_of_sat. exact hleft.
      * apply rawStandardFormulaTruthValue_of_not_sat. exact hnright.
    + apply rawStandardFormulaTruthValue_of_not_sat.
      intro himp. exact (hnright (himp hleft)).
  - right. split.
    + left. apply rawStandardFormulaTruthValue_of_not_sat. exact hnleft.
    + apply rawStandardFormulaTruthValue_of_sat.
      intros h. contradiction.
  - right. split.
    + left. apply rawStandardFormulaTruthValue_of_not_sat. exact hnleft.
    + apply rawStandardFormulaTruthValue_of_sat.
      intros h. contradiction.
Qed.

Lemma raw_standardFormulaAndTruth : forall
    (M : RawPAModel), RawPASatisfies M -> forall env left right,
  RawAndTruth M
    (rawStandardFormulaTruthValue M env (pAnd left right))
    (rawStandardFormulaTruthValue M env left)
    (rawStandardFormulaTruthValue M env right).
Proof.
  intros M hPA env left right.
  unfold RawAndTruth.
  repeat split; try apply rawStandardFormulaTruthValue_bit.
  destruct (excluded_middle_informative (raw_formula_sat M env left))
    as [hleft | hnleft];
  destruct (excluded_middle_informative (raw_formula_sat M env right))
    as [hright | hnright].
  - left. split.
    + split; apply rawStandardFormulaTruthValue_of_sat; assumption.
    + apply rawStandardFormulaTruthValue_of_sat. split; assumption.
  - right. split.
    + right. apply rawStandardFormulaTruthValue_of_not_sat. exact hnright.
    + apply rawStandardFormulaTruthValue_of_not_sat.
      cbn [raw_formula_sat]. tauto.
  - right. split.
    + left. apply rawStandardFormulaTruthValue_of_not_sat. exact hnleft.
    + apply rawStandardFormulaTruthValue_of_not_sat.
      cbn [raw_formula_sat]. tauto.
  - right. split.
    + left. apply rawStandardFormulaTruthValue_of_not_sat. exact hnleft.
    + apply rawStandardFormulaTruthValue_of_not_sat.
      cbn [raw_formula_sat]. tauto.
Qed.

Lemma raw_standardFormulaOrTruth : forall
    (M : RawPAModel), RawPASatisfies M -> forall env left right,
  RawOrTruth M
    (rawStandardFormulaTruthValue M env (pOr left right))
    (rawStandardFormulaTruthValue M env left)
    (rawStandardFormulaTruthValue M env right).
Proof.
  intros M hPA env left right.
  unfold RawOrTruth.
  repeat split; try apply rawStandardFormulaTruthValue_bit.
  destruct (excluded_middle_informative (raw_formula_sat M env left))
    as [hleft | hnleft];
  destruct (excluded_middle_informative (raw_formula_sat M env right))
    as [hright | hnright].
  - left. split.
    + left. apply rawStandardFormulaTruthValue_of_sat. exact hleft.
    + apply rawStandardFormulaTruthValue_of_sat. now left.
  - left. split.
    + left. apply rawStandardFormulaTruthValue_of_sat. exact hleft.
    + apply rawStandardFormulaTruthValue_of_sat. now left.
  - left. split.
    + right. apply rawStandardFormulaTruthValue_of_sat. exact hright.
    + apply rawStandardFormulaTruthValue_of_sat. now right.
  - right. split.
    + split; apply rawStandardFormulaTruthValue_of_not_sat; assumption.
    + apply rawStandardFormulaTruthValue_of_not_sat.
      cbn [raw_formula_sat]. tauto.
Qed.

(** Every standard quantifier-free constructor has a closed row whenever
    the assignment agrees with [env] and the support/truth tables contain
    their advertised finite-vector entries. *)
Lemma raw_standardRankZeroTruth_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) limit
    assignmentCode assignmentStep truthCode truthStep supportCode supportStep,
  (forall index, index < limit ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M truthCode truthStep
      (rawNumeralValue M code) (rawStandardRankZeroTruthAt M env code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M supportCode supportStep
      (rawNumeralValue M code) (rawStandardRankZeroSupportAt M code)) ->
  forall phi, RankZeroFormula phi -> formulaCode phi < limit ->
  RawRankZeroTruthClosedStep M
    (rawQuotedFormulaCode M phi)
    (rawStandardFormulaTruthValue M env phi)
    assignmentCode assignmentStep truthCode truthStep supportCode supportStep.
Proof.
  intros M hPA env limit assignmentCode assignmentStep
    truthCode truthStep supportCode supportStep
    hassignment htruth hsupport phi hzero hbound.
  destruct phi as [left right | | left right | left right |
      left right | child | child].
  - exists (rawQuotedTermCode M left), (raw_term_eval M env left),
      (rawQuotedTermCode M right), (raw_term_eval M env right).
    left. unfold RawRankZeroEqCertifiedRow.
    split; [reflexivity |]. split.
    + apply (raw_termEvaluationCertificate_standard_of_assignment
        M hPA env limit assignmentCode assignmentStep hassignment left).
      pose proof (formulaCode_eq_left_lt left right). lia.
    + split.
      * apply (raw_termEvaluationCertificate_standard_of_assignment
          M hPA env limit assignmentCode assignmentStep hassignment right).
        pose proof (formulaCode_eq_right_lt left right). lia.
      * apply raw_standardFormulaEqualityTruth.
  - exists (raw_zero M), (raw_zero M), (raw_zero M), (raw_zero M).
    right. left. split; [reflexivity |].
    apply raw_standardFormulaBotTruth.
  - destruct (proj1 (rankZeroFormula_imp_iff left right) hzero)
      as [hleftZero hrightZero].
    exists (rawQuotedFormulaCode M left),
      (rawStandardFormulaTruthValue M env left),
      (rawQuotedFormulaCode M right),
      (rawStandardFormulaTruthValue M env right).
    right. right. left. split.
    + split; [reflexivity |]. split.
      * rewrite rawQuotedFormulaCode_standard by exact hPA.
        rewrite <- (rawStandardRankZeroTruthAt_formulaCode
          M env left hleftZero).
        apply htruth. pose proof (formulaCode_imp_left_lt left right). lia.
      * split.
        -- rewrite rawQuotedFormulaCode_standard by exact hPA.
           rewrite <- (rawStandardRankZeroTruthAt_formulaCode
             M env right hrightZero).
           apply htruth. pose proof (formulaCode_imp_right_lt left right).
           lia.
        -- apply raw_standardFormulaImpTruth. exact hPA.
    + split.
      * unfold rawFormulaCodeSupported.
        rewrite rawQuotedFormulaCode_standard by exact hPA.
        pose proof (hsupport (formulaCode left)) as hs.
        assert (hchildBound : formulaCode left < limit) by
          (pose proof (formulaCode_imp_left_lt left right); lia).
        specialize (hs hchildBound).
        rewrite (rawStandardRankZeroSupportAt_formulaCode
          M left hleftZero) in hs. exact hs.
      * split.
        -- unfold rawFormulaCodeSupported.
           rewrite rawQuotedFormulaCode_standard by exact hPA.
           pose proof (hsupport (formulaCode right)) as hs.
           assert (hchildBound : formulaCode right < limit) by
             (pose proof (formulaCode_imp_right_lt left right); lia).
           specialize (hs hchildBound).
           rewrite (rawStandardRankZeroSupportAt_formulaCode
             M right hrightZero) in hs. exact hs.
        -- split; rewrite !rawQuotedFormulaCode_standard by exact hPA;
             apply raw_lt_numeralValue_of_lt; try exact hPA.
           ++ apply formulaCode_imp_left_lt.
           ++ apply formulaCode_imp_right_lt.
  - destruct (proj1 (rankZeroFormula_and_iff left right) hzero)
      as [hleftZero hrightZero].
    exists (rawQuotedFormulaCode M left),
      (rawStandardFormulaTruthValue M env left),
      (rawQuotedFormulaCode M right),
      (rawStandardFormulaTruthValue M env right).
    right. right. right. left. split.
    + split; [reflexivity |]. split.
      * rewrite rawQuotedFormulaCode_standard by exact hPA.
        rewrite <- (rawStandardRankZeroTruthAt_formulaCode
          M env left hleftZero).
        apply htruth. pose proof (formulaCode_and_left_lt left right). lia.
      * split.
        -- rewrite rawQuotedFormulaCode_standard by exact hPA.
           rewrite <- (rawStandardRankZeroTruthAt_formulaCode
             M env right hrightZero).
           apply htruth. pose proof (formulaCode_and_right_lt left right).
           lia.
        -- apply raw_standardFormulaAndTruth. exact hPA.
    + split.
      * unfold rawFormulaCodeSupported.
        rewrite rawQuotedFormulaCode_standard by exact hPA.
        pose proof (hsupport (formulaCode left)) as hs.
        assert (hchildBound : formulaCode left < limit) by
          (pose proof (formulaCode_and_left_lt left right); lia).
        specialize (hs hchildBound).
        rewrite (rawStandardRankZeroSupportAt_formulaCode
          M left hleftZero) in hs. exact hs.
      * split.
        -- unfold rawFormulaCodeSupported.
           rewrite rawQuotedFormulaCode_standard by exact hPA.
           pose proof (hsupport (formulaCode right)) as hs.
           assert (hchildBound : formulaCode right < limit) by
             (pose proof (formulaCode_and_right_lt left right); lia).
           specialize (hs hchildBound).
           rewrite (rawStandardRankZeroSupportAt_formulaCode
             M right hrightZero) in hs. exact hs.
        -- split; rewrite !rawQuotedFormulaCode_standard by exact hPA;
             apply raw_lt_numeralValue_of_lt; try exact hPA.
           ++ apply formulaCode_and_left_lt.
           ++ apply formulaCode_and_right_lt.
  - destruct (proj1 (rankZeroFormula_or_iff left right) hzero)
      as [hleftZero hrightZero].
    exists (rawQuotedFormulaCode M left),
      (rawStandardFormulaTruthValue M env left),
      (rawQuotedFormulaCode M right),
      (rawStandardFormulaTruthValue M env right).
    right. right. right. right. split.
    + split; [reflexivity |]. split.
      * rewrite rawQuotedFormulaCode_standard by exact hPA.
        rewrite <- (rawStandardRankZeroTruthAt_formulaCode
          M env left hleftZero).
        apply htruth. pose proof (formulaCode_or_left_lt left right). lia.
      * split.
        -- rewrite rawQuotedFormulaCode_standard by exact hPA.
           rewrite <- (rawStandardRankZeroTruthAt_formulaCode
             M env right hrightZero).
           apply htruth. pose proof (formulaCode_or_right_lt left right).
           lia.
        -- apply raw_standardFormulaOrTruth. exact hPA.
    + split.
      * unfold rawFormulaCodeSupported.
        rewrite rawQuotedFormulaCode_standard by exact hPA.
        pose proof (hsupport (formulaCode left)) as hs.
        assert (hchildBound : formulaCode left < limit) by
          (pose proof (formulaCode_or_left_lt left right); lia).
        specialize (hs hchildBound).
        rewrite (rawStandardRankZeroSupportAt_formulaCode
          M left hleftZero) in hs. exact hs.
      * split.
        -- unfold rawFormulaCodeSupported.
           rewrite rawQuotedFormulaCode_standard by exact hPA.
           pose proof (hsupport (formulaCode right)) as hs.
           assert (hchildBound : formulaCode right < limit) by
             (pose proof (formulaCode_or_right_lt left right); lia).
           specialize (hs hchildBound).
           rewrite (rawStandardRankZeroSupportAt_formulaCode
             M right hrightZero) in hs. exact hs.
        -- split; rewrite !rawQuotedFormulaCode_standard by exact hPA;
             apply raw_lt_numeralValue_of_lt; try exact hPA.
           ++ apply formulaCode_or_left_lt.
           ++ apply formulaCode_or_right_lt.
  - cbn [RankZeroFormula rankZeroFormulab] in hzero. discriminate.
  - cbn [RankZeroFormula rankZeroFormulab] in hzero. discriminate.
Qed.

(** ------------------------------------------------------------------
    Finite realization with a supplied shared assignment. *)

Theorem raw_rankZeroTruthCertificateWithTables_standard_of_assignment :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) assignmentCode assignmentStep phi,
  RankZeroFormula phi ->
  (forall index, index < S (formulaCode phi) ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  exists supportCode supportStep truthCode truthStep : M,
    (forall code, code < S (formulaCode phi) ->
      RawCodedAssignmentLookup M supportCode supportStep
        (rawNumeralValue M code) (rawStandardRankZeroSupportAt M code)) /\
    (forall code, code < S (formulaCode phi) ->
      RawCodedAssignmentLookup M truthCode truthStep
        (rawNumeralValue M code)
        (rawStandardRankZeroTruthAt M env code)) /\
    RawRankZeroTruthCertificateWithTables M
      (rawQuotedFormulaCode M phi)
      (rawStandardFormulaTruthValue M env phi)
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep.
Proof.
  intros M hPA env assignmentCode assignmentStep phi hzero hassignment.
  destruct (finite_vector_beta_code M hPA
    (S (formulaCode phi)) (rawStandardRankZeroSupportAt M)) as
    [supportCode [supportStep hsupport]].
  destruct (finite_vector_beta_code M hPA
    (S (formulaCode phi)) (rawStandardRankZeroTruthAt M env)) as
    [truthCode [truthStep htruth]].
  exists supportCode, supportStep, truthCode, truthStep.
  split; [exact hsupport |]. split; [exact htruth |].
  unfold RawRankZeroTruthCertificateWithTables.
  split.
  - rewrite rawQuotedFormulaCode_standard by exact hPA.
    change (RawRankZeroTruthTraversal M
      (rawNumeralValue M (S (formulaCode phi)))
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep).
    split.
    + intros code hcode.
      destruct (raw_lt_numeralValue_cases M hPA code
        (S (formulaCode phi)) hcode) as [k [hk ->]].
      exists (rawStandardRankZeroSupportAt M k). exact (hsupport k hk).
    + split.
      * intros code hcode.
        destruct (raw_lt_numeralValue_cases M hPA code
          (S (formulaCode phi)) hcode) as [k [hk ->]].
        exists (rawStandardRankZeroTruthAt M env k). exact (htruth k hk).
      * intros code hcode hsupported.
        destruct (raw_lt_numeralValue_cases M hPA code
          (S (formulaCode phi)) hcode) as [k [hk ->]].
        assert (hsupportEntry :
            RawCodedAssignmentLookup M supportCode supportStep
              (rawNumeralValue M k) (rawStandardRankZeroSupportAt M k)).
        { exact (hsupport k hk). }
        assert (hsupportOne : rawStandardRankZeroSupportAt M k =
            rawTruthOne M).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            supportCode supportStep (rawNumeralValue M k)
            (rawStandardRankZeroSupportAt M k) (rawTruthOne M)
            hsupportEntry hsupported).
        }
        destruct (rawStandardRankZeroSupportAt_one_has_formula M hPA k
          hsupportOne) as [decoded hdecoded].
        pose proof (checkedDecodeRankZeroFormula_sound k decoded hdecoded)
          as [_ [hcanonical hdecodedZero]].
        exists (rawStandardRankZeroTruthAt M env k). split.
        -- exact (htruth k hk).
        -- pose proof (raw_standardRankZeroTruth_closed_step
             M hPA env (S (formulaCode phi))
             assignmentCode assignmentStep truthCode truthStep
             supportCode supportStep hassignment htruth hsupport
             decoded hdecodedZero) as hstep.
           assert (hdecodedBound : formulaCode decoded < S (formulaCode phi)).
           { now rewrite hcanonical. }
           specialize (hstep hdecodedBound).
           rewrite rawQuotedFormulaCode_standard in hstep by exact hPA.
           rewrite hcanonical in hstep.
           rewrite (rawStandardRankZeroTruthAt_checked
             M env k decoded hdecoded).
           exact hstep.
  - split.
    + unfold rawFormulaCodeSupported.
      rewrite rawQuotedFormulaCode_standard by exact hPA.
      pose proof (hsupport (formulaCode phi) (Nat.lt_succ_diag_r _)) as hs.
      rewrite (rawStandardRankZeroSupportAt_formulaCode M phi hzero) in hs.
      exact hs.
    + split.
      * rewrite rawQuotedFormulaCode_standard by exact hPA.
        rewrite <- (rawStandardRankZeroTruthAt_formulaCode M env phi hzero).
        exact (htruth (formulaCode phi) (Nat.lt_succ_diag_r _)).
      * apply rawStandardFormulaTruthValue_bit.
Qed.

Corollary raw_rankZeroTruthCertificate_standard_of_assignment :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) assignmentCode assignmentStep phi,
  RankZeroFormula phi ->
  (forall index, index < S (formulaCode phi) ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  RawRankZeroTruthCertificate M
    (rawQuotedFormulaCode M phi)
    (rawStandardFormulaTruthValue M env phi)
    assignmentCode assignmentStep.
Proof.
  intros M hPA env assignmentCode assignmentStep phi hzero hassignment.
  destruct (raw_rankZeroTruthCertificateWithTables_standard_of_assignment
    M hPA env assignmentCode assignmentStep phi hzero hassignment) as
    (supportCode & supportStep & truthCode & truthStep & _ & _ & hcert).
  exists supportCode, supportStep, truthCode, truthStep. exact hcert.
Qed.

(** Any certificate over the supplied standard assignment has the canonical
    semantic output.  This combines standard realization with the global
    cross-table functionality theorem; the candidate certificate may use
    completely different support and truth beta tables. *)
Theorem raw_rankZeroTruthCertificate_standard_output_of_assignment :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) assignmentCode assignmentStep phi output,
  RankZeroFormula phi ->
  (forall index, index < S (formulaCode phi) ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  RawRankZeroTruthCertificate M
    (rawQuotedFormulaCode M phi) output assignmentCode assignmentStep ->
  output = rawStandardFormulaTruthValue M env phi.
Proof.
  intros M hPA env assignmentCode assignmentStep phi output
    hzero hassignment hcert.
  apply (raw_rankZeroTruthCertificate_output_functional M hPA
    (rawQuotedFormulaCode M phi) assignmentCode assignmentStep).
  - exact hcert.
  - apply (raw_rankZeroTruthCertificate_standard_of_assignment
      M hPA env assignmentCode assignmentStep phi hzero hassignment).
Qed.

Corollary raw_rankZeroTruthCertificate_standard_one_iff :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) assignmentCode assignmentStep phi output,
  RankZeroFormula phi ->
  (forall index, index < S (formulaCode phi) ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  RawRankZeroTruthCertificate M
    (rawQuotedFormulaCode M phi) output assignmentCode assignmentStep ->
  output = rawTruthOne M <-> raw_formula_sat M env phi.
Proof.
  intros M hPA env assignmentCode assignmentStep phi output
    hzero hassignment hcert.
  rewrite (raw_rankZeroTruthCertificate_standard_output_of_assignment
    M hPA env assignmentCode assignmentStep phi output
    hzero hassignment hcert).
  apply rawStandardFormulaTruthValue_one_iff. exact hPA.
Qed.

Corollary raw_rankZeroTruthCertificate_standard_zero_iff :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) assignmentCode assignmentStep phi output,
  RankZeroFormula phi ->
  (forall index, index < S (formulaCode phi) ->
    RawCodedAssignmentLookup M assignmentCode assignmentStep
      (rawNumeralValue M index) (env index)) ->
  RawRankZeroTruthCertificate M
    (rawQuotedFormulaCode M phi) output assignmentCode assignmentStep ->
  output = raw_zero M <-> ~ raw_formula_sat M env phi.
Proof.
  intros M hPA env assignmentCode assignmentStep phi output
    hzero hassignment hcert.
  rewrite (raw_rankZeroTruthCertificate_standard_output_of_assignment
    M hPA env assignmentCode assignmentStep phi output
    hzero hassignment hcert).
  apply rawStandardFormulaTruthValue_zero_iff. exact hPA.
Qed.

(** ------------------------------------------------------------------
    One simultaneous finite assignment/support/truth realization. *)

Theorem raw_rankZeroTruthCertificateWithTables_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) phi,
  RankZeroFormula phi ->
  exists assignmentCode assignmentStep supportCode supportStep
      truthCode truthStep : M,
    RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
      (rawNumeralValue M (S (formulaCode phi))) /\
    RawRankZeroTruthCertificateWithTables M
      (rawQuotedFormulaCode M phi)
      (rawStandardFormulaTruthValue M env phi)
      assignmentCode assignmentStep truthCode truthStep
      supportCode supportStep.
Proof.
  intros M hPA env phi hzero.
  destruct (finite_vector_beta_code M hPA (S (formulaCode phi)) env) as
    [assignmentCode [assignmentStep hassignment]].
  destruct (raw_rankZeroTruthCertificateWithTables_standard_of_assignment
    M hPA env assignmentCode assignmentStep phi hzero hassignment) as
    (supportCode & supportStep & truthCode & truthStep & _ & _ & hcert).
  exists assignmentCode, assignmentStep, supportCode, supportStep,
    truthCode, truthStep. split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index
      (S (formulaCode phi)) hindex) as [k [hk ->]].
    exists (env k). exact (hassignment k hk).
  - exact hcert.
Qed.

Corollary raw_rankZeroTruthCertificate_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) phi,
  RankZeroFormula phi ->
  exists assignmentCode assignmentStep output : M,
    RawCodedAssignmentDefinedThrough M assignmentCode assignmentStep
      (rawNumeralValue M (S (formulaCode phi))) /\
    RawRankZeroTruthCertificate M
      (rawQuotedFormulaCode M phi) output assignmentCode assignmentStep /\
    (output = rawTruthOne M <-> raw_formula_sat M env phi) /\
    (output = raw_zero M <-> ~ raw_formula_sat M env phi).
Proof.
  intros M hPA env phi hzero.
  destruct (finite_vector_beta_code M hPA (S (formulaCode phi)) env) as
    [assignmentCode [assignmentStep hassignment]].
  pose proof (raw_rankZeroTruthCertificate_standard_of_assignment
    M hPA env assignmentCode assignmentStep phi hzero hassignment) as hcert.
  exists assignmentCode, assignmentStep,
    (rawStandardFormulaTruthValue M env phi).
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index
      (S (formulaCode phi)) hindex) as [k [hk ->]].
    exists (env k). exact (hassignment k hk).
  - split; [exact hcert |]. split.
    + apply rawStandardFormulaTruthValue_one_iff. exact hPA.
    + apply rawStandardFormulaTruthValue_zero_iff. exact hPA.
Qed.

(** Formula-level standard adequacy.  Variables 0--3 hold root, output,
    assignment code, and assignment step, matching the public certificate
    formula. *)
Definition rawStandardRankZeroCertificateEnv (M : RawPAModel)
    (env : nat -> M) (phi : formula)
    (assignmentCode assignmentStep : M) (tail : nat -> M) : nat -> M :=
  scons M (rawQuotedFormulaCode M phi)
    (scons M (rawStandardFormulaTruthValue M env phi)
      (scons M assignmentCode (scons M assignmentStep tail))).

Arguments rawStandardRankZeroCertificateEnv
  M env phi assignmentCode assignmentStep tail : clear implicits.

Corollary raw_sat_rankZeroTruthCertificateTermAt_standard_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (env : nat -> M) phi (tail : nat -> M),
  RankZeroFormula phi ->
  exists assignmentCode assignmentStep : M,
    raw_formula_sat M
      (rawStandardRankZeroCertificateEnv M env phi
        assignmentCode assignmentStep tail)
      (rankZeroTruthCertificateTermAt
        (tVar 0) (tVar 1) (tVar 2) (tVar 3)).
Proof.
  intros M hPA env phi tail hzero.
  destruct (finite_vector_beta_code M hPA (S (formulaCode phi)) env) as
    [assignmentCode [assignmentStep hassignment]].
  exists assignmentCode, assignmentStep.
  apply (proj2 (raw_sat_rankZeroTruthCertificateTermAt_iff M
    (rawStandardRankZeroCertificateEnv M env phi
      assignmentCode assignmentStep tail)
    (tVar 0) (tVar 1) (tVar 2) (tVar 3))).
  unfold rawStandardRankZeroCertificateEnv.
  cbn [raw_term_eval scons].
  apply (raw_rankZeroTruthCertificate_standard_of_assignment
    M hPA env assignmentCode assignmentStep phi hzero hassignment).
Qed.

End PABoundedRawCodedRankZeroTruthStandardAdequacy.
