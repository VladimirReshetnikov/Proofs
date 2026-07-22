(**
  Transparent PA-axiom witnesses in arbitrary raw models.

  The induction constructor of [PAAxiomWitness] contains a formula code.  In
  a nonstandard model that code need not denote any metatheoretic Rocq
  formula, so this file never decodes carrier elements.  Instead it composes
  transparent graphs for formula shifting, single substitution, syntactic
  free-variable bound, and iterated universal closure.

  The only external decoding below occurs in the standard-quotation proofs:
  finite beta tables are filled from ordinary Rocq syntax and then reflected
  into an arbitrary model of PA.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof CodedSyntax RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaRankTraversal
  RawCodedTermEvaluationStandardAdequacy
  RawCodedFormulaOperations RawCodedFormulaOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardRealization.

Import ListNotations.

Module PABoundedRawCodedPAAxiomWitness.

Import PA.
Import PAListCode.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedTermEvaluationStandardAdequacy.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardRealization.

(** ------------------------------------------------------------------
    A transparent graph for [Term.bound].

    Two beta tables contain the source term code and its numeric bound.  As
    with the operation traversals, malformed standard indices are filled by
    the harmless zero-term row; hence every table row is closed. *)

Definition codedTermBoundVariableRowTermAt
    (input output : term) : formula :=
  pEx (pAnd
    (termVarCodeTermAt (liftTerm 1 input) (tVar 0))
    (pEq (liftTerm 1 output) (tSucc (tVar 0)))).

Definition RawCodedTermBoundVariableRow (M : RawPAModel)
    (input output : M) : Prop :=
  exists index : M,
    input = rawTermVarCode M index /\
    output = raw_succ M index.

Lemma raw_sat_codedTermBoundVariableRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (codedTermBoundVariableRowTermAt input output) <->
  RawCodedTermBoundVariableRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold codedTermBoundVariableRowTermAt,
    RawCodedTermBoundVariableRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_termVarCodeTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermBoundZeroRowTermAt
    (input output : term) : formula :=
  pAnd (termZeroCodeTermAt input) (pEq output tZero).

Definition RawCodedTermBoundZeroRow (M : RawPAModel)
    (input output : M) : Prop :=
  input = rawTermZeroCode M /\ output = raw_zero M.

Lemma raw_sat_codedTermBoundZeroRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e (codedTermBoundZeroRowTermAt input output) <->
  RawCodedTermBoundZeroRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermBoundZeroRowTermAt,
    RawCodedTermBoundZeroRow.
  cbn [raw_formula_sat]. rewrite raw_sat_termZeroCodeTermAt_iff.
  reflexivity.
Qed.

Definition codedTermBoundSuccRowTermAt
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  operationEx3 (operationAnd4
    (Formula.ltTermAt (tVar 2) (liftTerm 3 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
      (liftTerm 3 targetCode) (liftTerm 3 targetStep)
      (tVar 2) (tVar 1) (tVar 0))
    (termSuccCodeTermAt (liftTerm 3 input) (tVar 1))
    (pEq (liftTerm 3 output) (tVar 0))).

Definition RawCodedTermBoundSuccRow (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists childIndex inputChild childBound : M,
    rawLt M childIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      childIndex inputChild childBound /\
    input = rawTermSuccCode M inputChild /\
    output = childBound.

Lemma raw_sat_codedTermBoundSuccRowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep
      index input output,
  raw_formula_sat M e
    (codedTermBoundSuccRowTermAt sourceCode sourceStep targetCode targetStep
      index input output) <->
  RawCodedTermBoundSuccRow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedTermBoundSuccRowTermAt, operationEx3, operationAnd4,
    RawCodedTermBoundSuccRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termSuccCodeTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermBoundBinaryRowTermAt
    (constructor : term -> term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  operationEx6 (operationAnd6
    (Formula.ltTermAt (tVar 5) (liftTerm 6 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 6 sourceCode) (liftTerm 6 sourceStep)
      (liftTerm 6 targetCode) (liftTerm 6 targetStep)
      (tVar 5) (tVar 4) (tVar 3))
    (Formula.ltTermAt (tVar 2) (liftTerm 6 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 6 sourceCode) (liftTerm 6 sourceStep)
      (liftTerm 6 targetCode) (liftTerm 6 targetStep)
      (tVar 2) (tVar 1) (tVar 0))
    (constructor (liftTerm 6 input) (tVar 4) (tVar 1))
    (pEq (liftTerm 6 output) (tAdd (tVar 3) (tVar 0)))).

Definition RawCodedTermBoundBinaryRow (M : RawPAModel)
    (constructor : M -> M -> M)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists leftIndex inputLeft leftBound rightIndex inputRight rightBound : M,
    rawLt M leftIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      leftIndex inputLeft leftBound /\
    rawLt M rightIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      rightIndex inputRight rightBound /\
    input = constructor inputLeft inputRight /\
    output = raw_add M leftBound rightBound.

Lemma raw_sat_codedTermBoundBinaryRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> term -> formula)
    (rawConstructor : M -> M -> M),
  (forall e' code left right,
    raw_formula_sat M e' (constructor code left right) <->
    raw_term_eval M e' code = rawConstructor
      (raw_term_eval M e' left) (raw_term_eval M e' right)) ->
  forall sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermBoundBinaryRowTermAt constructor
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermBoundBinaryRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep index input output.
  unfold codedTermBoundBinaryRowTermAt, operationEx6, operationAnd6,
    RawCodedTermBoundBinaryRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite hconstructor.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermBoundTraversalRowTermAt
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  pOr (codedTermBoundVariableRowTermAt input output)
  (pOr (codedTermBoundZeroRowTermAt input output)
  (pOr (codedTermBoundSuccRowTermAt
      sourceCode sourceStep targetCode targetStep index input output)
  (pOr (codedTermBoundBinaryRowTermAt termAddCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
    (codedTermBoundBinaryRowTermAt termMulCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)))).

Definition RawCodedTermBoundTraversalRow (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  RawCodedTermBoundVariableRow M input output \/
  RawCodedTermBoundZeroRow M input output \/
  RawCodedTermBoundSuccRow M
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedTermBoundBinaryRow M (rawTermAddCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedTermBoundBinaryRow M (rawTermMulCode M)
    sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermBoundTraversalRowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep
      index input output,
  raw_formula_sat M e
    (codedTermBoundTraversalRowTermAt
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermBoundTraversalRow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedTermBoundTraversalRowTermAt,
    RawCodedTermBoundTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedTermBoundVariableRowTermAt_iff.
  rewrite raw_sat_codedTermBoundZeroRowTermAt_iff.
  rewrite raw_sat_codedTermBoundSuccRowTermAt_iff.
  rewrite (raw_sat_codedTermBoundBinaryRowTermAt_iff M e
    termAddCodeTermAt (rawTermAddCode M)
    (raw_sat_termAddCodeTermAt_iff M)).
  rewrite (raw_sat_codedTermBoundBinaryRowTermAt_iff M e
    termMulCodeTermAt (rawTermMulCode M)
    (raw_sat_termMulCodeTermAt_iff M)).
  reflexivity.
Qed.

Definition codedTermBoundRowsTermAt
    (sourceCode sourceStep targetCode targetStep root : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 (tSucc root)))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedTermBoundTraversalRowTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawCodedTermBoundRows (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep root : M) : Prop :=
  forall index input output : M,
    rawLt M index (raw_succ M root) ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedTermBoundTraversalRow M
      sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermBoundRowsTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep root,
  raw_formula_sat M e
    (codedTermBoundRowsTermAt
      sourceCode sourceStep targetCode targetStep root) <->
  RawCodedTermBoundRows M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e root).
Proof.
  intros. unfold codedTermBoundRowsTermAt, RawCodedTermBoundRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedTermBoundTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermBoundTraceTermAt
    (sourceCode sourceStep targetCode targetStep input output : term)
    : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt
      sourceCode sourceStep (tSucc input))
    (codedAssignmentDefinedThroughTermAt
      targetCode targetStep (tSucc input))
    (codedTermOperationPairLookupTermAt
      sourceCode sourceStep targetCode targetStep input input output)
    (codedTermBoundRowsTermAt
      sourceCode sourceStep targetCode targetStep input).

Definition RawCodedTermBoundTrace (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M
    sourceCode sourceStep (raw_succ M input) /\
  RawCodedAssignmentDefinedThrough M
    targetCode targetStep (raw_succ M input) /\
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep input input output /\
  RawCodedTermBoundRows M
    sourceCode sourceStep targetCode targetStep input.

Lemma raw_sat_codedTermBoundTraceTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep input output,
  raw_formula_sat M e
    (codedTermBoundTraceTermAt
      sourceCode sourceStep targetCode targetStep input output) <->
  RawCodedTermBoundTrace M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermBoundTraceTermAt, RawCodedTermBoundTrace,
    operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  rewrite raw_sat_codedTermBoundRowsTermAt_iff.
  reflexivity.
Qed.

Definition codedTermBoundTermAt (input output : term) : formula :=
  operationEx4
    (codedTermBoundTraceTermAt
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 4 input) (liftTerm 4 output)).

Definition RawCodedTermBound (M : RawPAModel)
    (input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep : M,
    RawCodedTermBoundTrace M
      sourceCode sourceStep targetCode targetStep input output.

Lemma raw_sat_codedTermBoundTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e (codedTermBoundTermAt input output) <->
  RawCodedTermBound M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermBoundTermAt, operationEx4, RawCodedTermBound.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedTermBoundTraceTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Standard realization of the term-bound graph. *)
Definition rawStandardTermBoundSourceAt
    (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t => rawQuotedTermCode M t
  | None => rawTermZeroCode M
  end.

Definition rawStandardTermBoundTargetAt
    (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeTerm code with
  | Some t => rawNumeralValue M (Term.bound t)
  | None => raw_zero M
  end.

Lemma rawStandardTermBoundSourceAt_termCode : forall M t,
  rawStandardTermBoundSourceAt M (termCode t) = rawQuotedTermCode M t.
Proof.
  intros. unfold rawStandardTermBoundSourceAt.
  now rewrite checkedDecodeTerm_termCode.
Qed.

Lemma rawStandardTermBoundTargetAt_termCode : forall M t,
  rawStandardTermBoundTargetAt M (termCode t) =
    rawNumeralValue M (Term.bound t).
Proof.
  intros. unfold rawStandardTermBoundTargetAt.
  now rewrite checkedDecodeTerm_termCode.
Qed.

Lemma raw_standardTermBound_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    limit sourceCode sourceStep targetCode targetStep,
  (forall code, code < limit ->
    RawCodedAssignmentLookup M sourceCode sourceStep
      (rawNumeralValue M code) (rawStandardTermBoundSourceAt M code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M targetCode targetStep
      (rawNumeralValue M code) (rawStandardTermBoundTargetAt M code)) ->
  forall t, termCode t < limit ->
  RawCodedTermBoundTraversalRow M
    sourceCode sourceStep targetCode targetStep
    (rawNumeralValue M (termCode t))
    (rawQuotedTermCode M t) (rawNumeralValue M (Term.bound t)).
Proof.
  intros M hPA limit sourceCode sourceStep targetCode targetStep
    hsource htarget t ht.
  destruct t as [index | | child | left right | left right].
  - left. exists (rawNumeralValue M index). split; reflexivity.
  - right. left. split; reflexivity.
  - right. right. left.
    exists (rawNumeralValue M (termCode child)),
      (rawQuotedTermCode M child),
      (rawNumeralValue M (Term.bound child)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_succ_child_lt.
    + split.
      * split.
        -- rewrite <- rawStandardTermBoundSourceAt_termCode.
           apply hsource. pose proof (termCode_succ_child_lt child). lia.
        -- rewrite <- rawStandardTermBoundTargetAt_termCode.
           apply htarget. pose proof (termCode_succ_child_lt child). lia.
      * split; reflexivity.
  - right. right. right. left.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawNumeralValue M (Term.bound left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawNumeralValue M (Term.bound right)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_add_left_lt.
    + split.
      * split.
        -- rewrite <- rawStandardTermBoundSourceAt_termCode.
           apply hsource. pose proof (termCode_add_left_lt left right). lia.
        -- rewrite <- rawStandardTermBoundTargetAt_termCode.
           apply htarget. pose proof (termCode_add_left_lt left right). lia.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           apply termCode_add_right_lt.
        -- split.
           ++ split.
              ** rewrite <- rawStandardTermBoundSourceAt_termCode.
                 apply hsource.
                 pose proof (termCode_add_right_lt left right). lia.
              ** rewrite <- rawStandardTermBoundTargetAt_termCode.
                 apply htarget.
                 pose proof (termCode_add_right_lt left right). lia.
           ++ split; [reflexivity |].
              rewrite raw_add_numeral_values_syntax by exact hPA.
              reflexivity.
  - right. right. right. right.
    exists (rawNumeralValue M (termCode left)),
      (rawQuotedTermCode M left),
      (rawNumeralValue M (Term.bound left)),
      (rawNumeralValue M (termCode right)),
      (rawQuotedTermCode M right),
      (rawNumeralValue M (Term.bound right)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply termCode_mul_left_lt.
    + split.
      * split.
        -- rewrite <- rawStandardTermBoundSourceAt_termCode.
           apply hsource. pose proof (termCode_mul_left_lt left right). lia.
        -- rewrite <- rawStandardTermBoundTargetAt_termCode.
           apply htarget. pose proof (termCode_mul_left_lt left right). lia.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           apply termCode_mul_right_lt.
        -- split.
           ++ split.
              ** rewrite <- rawStandardTermBoundSourceAt_termCode.
                 apply hsource.
                 pose proof (termCode_mul_right_lt left right). lia.
              ** rewrite <- rawStandardTermBoundTargetAt_termCode.
                 apply htarget.
                 pose proof (termCode_mul_right_lt left right). lia.
           ++ split; [reflexivity |].
              rewrite raw_add_numeral_values_syntax by exact hPA.
              reflexivity.
Qed.

Theorem raw_codedTermBound_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall t,
  RawCodedTermBound M
    (rawQuotedTermCode M t) (rawNumeralValue M (Term.bound t)).
Proof.
  intros M hPA root.
  rewrite rawQuotedTermCode_standard by exact hPA.
  set (limit := S (termCode root)).
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermBoundSourceAt M)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardTermBoundTargetAt M)) as
    [targetCode [targetStep htarget]].
  exists sourceCode, sourceStep, targetCode, targetStep.
  unfold RawCodedTermBoundTrace.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardTermBoundSourceAt M k). apply hsource. exact hk.
  - split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
        as [k [hk ->]].
      exists (rawStandardTermBoundTargetAt M k). apply htarget. exact hk.
    + split.
      * split.
        -- pose proof (hsource (termCode root)) as hrootSource.
           specialize (hrootSource ltac:(unfold limit; lia)).
           rewrite rawStandardTermBoundSourceAt_termCode in hrootSource.
           rewrite rawQuotedTermCode_standard in hrootSource by exact hPA.
           exact hrootSource.
        -- rewrite <- rawStandardTermBoundTargetAt_termCode.
           apply htarget. unfold limit. lia.
      * intros index input output hindex [hinput houtput].
        destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
          as [k [hk ->]].
        assert (hinputCanonical : input =
            rawStandardTermBoundSourceAt M k).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceCode sourceStep (rawNumeralValue M k) input
            (rawStandardTermBoundSourceAt M k)
            hinput (hsource k hk)).
        }
        assert (houtputCanonical : output =
            rawStandardTermBoundTargetAt M k).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            targetCode targetStep (rawNumeralValue M k) output
            (rawStandardTermBoundTargetAt M k)
            houtput (htarget k hk)).
        }
        subst input. subst output.
        destruct (checkedDecodeTerm k) as [decoded |] eqn:hdecoded.
        -- pose proof (checkedDecodeTerm_sound k decoded hdecoded)
             as [_ hcanonical].
           unfold rawStandardTermBoundSourceAt,
             rawStandardTermBoundTargetAt.
           rewrite hdecoded. rewrite <- hcanonical.
           apply (raw_standardTermBound_closed_step M hPA limit
             sourceCode sourceStep targetCode targetStep hsource htarget).
           now rewrite hcanonical.
        -- unfold rawStandardTermBoundSourceAt,
             rawStandardTermBoundTargetAt.
           rewrite hdecoded. right. left. split; reflexivity.
Qed.

(** ------------------------------------------------------------------
    A transparent graph for [Formula.bound]. *)

Definition codedFormulaBoundEqRowTermAt
    (input output : term) : formula :=
  operationEx4 (operationAnd4
    (formulaEqCodeTermAt (liftTerm 4 input) (tVar 3) (tVar 1))
    (codedTermBoundTermAt (tVar 3) (tVar 2))
    (codedTermBoundTermAt (tVar 1) (tVar 0))
    (pEq (liftTerm 4 output) (tAdd (tVar 2) (tVar 0)))).

Definition RawCodedFormulaBoundEqRow (M : RawPAModel)
    (input output : M) : Prop :=
  exists leftTerm leftBound rightTerm rightBound : M,
    input = rawFormulaEqCode M leftTerm rightTerm /\
    RawCodedTermBound M leftTerm leftBound /\
    RawCodedTermBound M rightTerm rightBound /\
    output = raw_add M leftBound rightBound.

Lemma raw_sat_codedFormulaBoundEqRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e (codedFormulaBoundEqRowTermAt input output) <->
  RawCodedFormulaBoundEqRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBoundEqRowTermAt, operationEx4, operationAnd4,
    RawCodedFormulaBoundEqRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_formulaEqCodeTermAt_iff.
  setoid_rewrite raw_sat_codedTermBoundTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaBoundBotRowTermAt
    (input output : term) : formula :=
  pAnd (formulaBotCodeTermAt input) (pEq output tZero).

Definition RawCodedFormulaBoundBotRow (M : RawPAModel)
    (input output : M) : Prop :=
  input = rawFormulaBotCode M /\ output = raw_zero M.

Lemma raw_sat_codedFormulaBoundBotRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e (codedFormulaBoundBotRowTermAt input output) <->
  RawCodedFormulaBoundBotRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBoundBotRowTermAt,
    RawCodedFormulaBoundBotRow.
  cbn [raw_formula_sat]. rewrite raw_sat_formulaBotCodeTermAt_iff.
  reflexivity.
Qed.

Definition codedFormulaBoundBinaryRowTermAt
    (constructor : term -> term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  operationEx6 (operationAnd6
    (Formula.ltTermAt (tVar 5) (liftTerm 6 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 6 sourceCode) (liftTerm 6 sourceStep)
      (liftTerm 6 targetCode) (liftTerm 6 targetStep)
      (tVar 5) (tVar 4) (tVar 3))
    (Formula.ltTermAt (tVar 2) (liftTerm 6 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 6 sourceCode) (liftTerm 6 sourceStep)
      (liftTerm 6 targetCode) (liftTerm 6 targetStep)
      (tVar 2) (tVar 1) (tVar 0))
    (constructor (liftTerm 6 input) (tVar 4) (tVar 1))
    (pEq (liftTerm 6 output) (tAdd (tVar 3) (tVar 0)))).

Definition RawCodedFormulaBoundBinaryRow (M : RawPAModel)
    (constructor : M -> M -> M)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists leftIndex inputLeft leftBound rightIndex inputRight rightBound : M,
    rawLt M leftIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      leftIndex inputLeft leftBound /\
    rawLt M rightIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      rightIndex inputRight rightBound /\
    input = constructor inputLeft inputRight /\
    output = raw_add M leftBound rightBound.

Lemma raw_sat_codedFormulaBoundBinaryRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> term -> formula)
    (rawConstructor : M -> M -> M),
  (forall e' code left right,
    raw_formula_sat M e' (constructor code left right) <->
    raw_term_eval M e' code = rawConstructor
      (raw_term_eval M e' left) (raw_term_eval M e' right)) ->
  forall sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedFormulaBoundBinaryRowTermAt constructor
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedFormulaBoundBinaryRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep index input output.
  unfold codedFormulaBoundBinaryRowTermAt, operationEx6, operationAnd6,
    RawCodedFormulaBoundBinaryRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite hconstructor.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaBoundUnaryRowTermAt
    (constructor : term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  operationEx3 (operationAnd4
    (Formula.ltTermAt (tVar 2) (liftTerm 3 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
      (liftTerm 3 targetCode) (liftTerm 3 targetStep)
      (tVar 2) (tVar 1) (tVar 0))
    (constructor (liftTerm 3 input) (tVar 1))
    (pEq (liftTerm 3 output) (tVar 0))).

Definition RawCodedFormulaBoundUnaryRow (M : RawPAModel)
    (constructor : M -> M)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists childIndex inputChild childBound : M,
    rawLt M childIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      childIndex inputChild childBound /\
    input = constructor inputChild /\
    output = childBound.

Lemma raw_sat_codedFormulaBoundUnaryRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> formula) (rawConstructor : M -> M),
  (forall e' code child,
    raw_formula_sat M e' (constructor code child) <->
    raw_term_eval M e' code = rawConstructor (raw_term_eval M e' child)) ->
  forall sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedFormulaBoundUnaryRowTermAt constructor
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedFormulaBoundUnaryRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep index input output.
  unfold codedFormulaBoundUnaryRowTermAt, operationEx3, operationAnd4,
    RawCodedFormulaBoundUnaryRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite hconstructor.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaBoundTraversalRowTermAt
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  pOr (codedFormulaBoundEqRowTermAt input output)
  (pOr (codedFormulaBoundBotRowTermAt input output)
  (pOr (codedFormulaBoundBinaryRowTermAt formulaImpCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
  (pOr (codedFormulaBoundBinaryRowTermAt formulaAndCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
  (pOr (codedFormulaBoundBinaryRowTermAt formulaOrCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
  (pOr (codedFormulaBoundUnaryRowTermAt formulaAllCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
    (codedFormulaBoundUnaryRowTermAt formulaExCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)))))).

Definition RawCodedFormulaBoundTraversalRow (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  RawCodedFormulaBoundEqRow M input output \/
  RawCodedFormulaBoundBotRow M input output \/
  RawCodedFormulaBoundBinaryRow M (rawFormulaImpCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedFormulaBoundBinaryRow M (rawFormulaAndCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedFormulaBoundBinaryRow M (rawFormulaOrCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedFormulaBoundUnaryRow M (rawFormulaAllCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedFormulaBoundUnaryRow M (rawFormulaExCode M)
    sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedFormulaBoundTraversalRowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep
      index input output,
  raw_formula_sat M e
    (codedFormulaBoundTraversalRowTermAt
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedFormulaBoundTraversalRow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBoundTraversalRowTermAt,
    RawCodedFormulaBoundTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaBoundEqRowTermAt_iff.
  rewrite raw_sat_codedFormulaBoundBotRowTermAt_iff.
  rewrite (raw_sat_codedFormulaBoundBinaryRowTermAt_iff M e
    formulaImpCodeTermAt (rawFormulaImpCode M)
    (raw_sat_formulaImpCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBoundBinaryRowTermAt_iff M e
    formulaAndCodeTermAt (rawFormulaAndCode M)
    (raw_sat_formulaAndCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBoundBinaryRowTermAt_iff M e
    formulaOrCodeTermAt (rawFormulaOrCode M)
    (raw_sat_formulaOrCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBoundUnaryRowTermAt_iff M e
    formulaAllCodeTermAt (rawFormulaAllCode M)
    (raw_sat_formulaAllCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBoundUnaryRowTermAt_iff M e
    formulaExCodeTermAt (rawFormulaExCode M)
    (raw_sat_formulaExCodeTermAt_iff M)).
  reflexivity.
Qed.

Definition codedFormulaBoundRowsTermAt
    (sourceCode sourceStep targetCode targetStep root : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 (tSucc root)))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaBoundTraversalRowTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawCodedFormulaBoundRows (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep root : M) : Prop :=
  forall index input output : M,
    rawLt M index (raw_succ M root) ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedFormulaBoundTraversalRow M
      sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedFormulaBoundRowsTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep root,
  raw_formula_sat M e
    (codedFormulaBoundRowsTermAt
      sourceCode sourceStep targetCode targetStep root) <->
  RawCodedFormulaBoundRows M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e root).
Proof.
  intros. unfold codedFormulaBoundRowsTermAt, RawCodedFormulaBoundRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaBoundTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaBoundTraceTermAt
    (sourceCode sourceStep targetCode targetStep input output : term)
    : formula :=
  operationAnd4
    (codedAssignmentDefinedThroughTermAt
      sourceCode sourceStep (tSucc input))
    (codedAssignmentDefinedThroughTermAt
      targetCode targetStep (tSucc input))
    (codedTermOperationPairLookupTermAt
      sourceCode sourceStep targetCode targetStep input input output)
    (codedFormulaBoundRowsTermAt
      sourceCode sourceStep targetCode targetStep input).

Definition RawCodedFormulaBoundTrace (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M
    sourceCode sourceStep (raw_succ M input) /\
  RawCodedAssignmentDefinedThrough M
    targetCode targetStep (raw_succ M input) /\
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep input input output /\
  RawCodedFormulaBoundRows M
    sourceCode sourceStep targetCode targetStep input.

Lemma raw_sat_codedFormulaBoundTraceTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep input output,
  raw_formula_sat M e
    (codedFormulaBoundTraceTermAt
      sourceCode sourceStep targetCode targetStep input output) <->
  RawCodedFormulaBoundTrace M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBoundTraceTermAt, RawCodedFormulaBoundTrace,
    operationAnd4.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  rewrite raw_sat_codedFormulaBoundRowsTermAt_iff.
  reflexivity.
Qed.

Definition codedFormulaBoundTermAt (input output : term) : formula :=
  operationEx4
    (codedFormulaBoundTraceTermAt
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 4 input) (liftTerm 4 output)).

Definition RawCodedFormulaBound (M : RawPAModel)
    (input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep : M,
    RawCodedFormulaBoundTrace M
      sourceCode sourceStep targetCode targetStep input output.

Lemma raw_sat_codedFormulaBoundTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e (codedFormulaBoundTermAt input output) <->
  RawCodedFormulaBound M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBoundTermAt, operationEx4,
    RawCodedFormulaBound.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaBoundTraceTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** A checked decoder is used only to populate standard finite vectors. *)
Definition checkedDecodeFormula (code : nat) : option formula :=
  match decodeFormula code with
  | Some phi =>
      if formulaCode phi =? code then Some phi else None
  | None => None
  end.

Lemma checkedDecodeFormula_formulaCode : forall phi,
  checkedDecodeFormula (formulaCode phi) = Some phi.
Proof.
  intro phi. unfold checkedDecodeFormula.
  rewrite decodeFormula_formulaCode, Nat.eqb_refl. reflexivity.
Qed.

Lemma checkedDecodeFormula_sound : forall code phi,
  checkedDecodeFormula code = Some phi ->
  decodeFormula code = Some phi /\ formulaCode phi = code.
Proof.
  intros code phi. unfold checkedDecodeFormula.
  destruct (decodeFormula code) as [decoded |] eqn:hdecode;
    [|discriminate].
  destruct (formulaCode decoded =? code) eqn:hcanonical;
    [|discriminate].
  intro h. inversion h; subst decoded.
  split; [reflexivity | now apply Nat.eqb_eq].
Qed.

Definition rawStandardFormulaBoundSourceAt
    (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeFormula code with
  | Some phi => rawQuotedFormulaCode M phi
  | None => rawFormulaBotCode M
  end.

Definition rawStandardFormulaBoundTargetAt
    (M : RawPAModel) (code : nat) : M :=
  match checkedDecodeFormula code with
  | Some phi => rawNumeralValue M (Formula.bound phi)
  | None => raw_zero M
  end.

Lemma rawStandardFormulaBoundSourceAt_formulaCode : forall M phi,
  rawStandardFormulaBoundSourceAt M (formulaCode phi) =
    rawQuotedFormulaCode M phi.
Proof.
  intros. unfold rawStandardFormulaBoundSourceAt.
  now rewrite checkedDecodeFormula_formulaCode.
Qed.

Lemma rawStandardFormulaBoundTargetAt_formulaCode : forall M phi,
  rawStandardFormulaBoundTargetAt M (formulaCode phi) =
    rawNumeralValue M (Formula.bound phi).
Proof.
  intros. unfold rawStandardFormulaBoundTargetAt.
  now rewrite checkedDecodeFormula_formulaCode.
Qed.

Lemma raw_standardFormulaBound_closed_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    limit sourceCode sourceStep targetCode targetStep,
  (forall code, code < limit ->
    RawCodedAssignmentLookup M sourceCode sourceStep
      (rawNumeralValue M code) (rawStandardFormulaBoundSourceAt M code)) ->
  (forall code, code < limit ->
    RawCodedAssignmentLookup M targetCode targetStep
      (rawNumeralValue M code) (rawStandardFormulaBoundTargetAt M code)) ->
  forall phi, formulaCode phi < limit ->
  RawCodedFormulaBoundTraversalRow M
    sourceCode sourceStep targetCode targetStep
    (rawNumeralValue M (formulaCode phi))
    (rawQuotedFormulaCode M phi)
    (rawNumeralValue M (Formula.bound phi)).
Proof.
  intros M hPA limit sourceCode sourceStep targetCode targetStep
    hsource htarget phi hphi.
  destruct phi as [leftTerm rightTerm | | left right | left right |
      left right | child | child].
  - left.
    exists (rawQuotedTermCode M leftTerm),
      (rawNumeralValue M (Term.bound leftTerm)),
      (rawQuotedTermCode M rightTerm),
      (rawNumeralValue M (Term.bound rightTerm)).
    split; [reflexivity |]. split.
    + apply raw_codedTermBound_standard. exact hPA.
    + split.
      * apply raw_codedTermBound_standard. exact hPA.
      * rewrite raw_add_numeral_values_syntax by exact hPA.
        reflexivity.
  - right. left. split; reflexivity.
  - right. right. left.
    exists (rawNumeralValue M (formulaCode left)),
      (rawQuotedFormulaCode M left),
      (rawNumeralValue M (Formula.bound left)),
      (rawNumeralValue M (formulaCode right)),
      (rawQuotedFormulaCode M right),
      (rawNumeralValue M (Formula.bound right)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply formulaCode_imp_left_lt.
    + split.
      * split.
        -- rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
           apply hsource. pose proof (formulaCode_imp_left_lt left right). lia.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. pose proof (formulaCode_imp_left_lt left right). lia.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           apply formulaCode_imp_right_lt.
        -- split.
           ++ split.
              ** rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
                 apply hsource.
                 pose proof (formulaCode_imp_right_lt left right). lia.
              ** rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
                 apply htarget.
                 pose proof (formulaCode_imp_right_lt left right). lia.
           ++ split; [reflexivity |].
              rewrite raw_add_numeral_values_syntax by exact hPA.
              reflexivity.
  - right. right. right. left.
    exists (rawNumeralValue M (formulaCode left)),
      (rawQuotedFormulaCode M left),
      (rawNumeralValue M (Formula.bound left)),
      (rawNumeralValue M (formulaCode right)),
      (rawQuotedFormulaCode M right),
      (rawNumeralValue M (Formula.bound right)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply formulaCode_and_left_lt.
    + split.
      * split.
        -- rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
           apply hsource. pose proof (formulaCode_and_left_lt left right). lia.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. pose proof (formulaCode_and_left_lt left right). lia.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           apply formulaCode_and_right_lt.
        -- split.
           ++ split.
              ** rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
                 apply hsource.
                 pose proof (formulaCode_and_right_lt left right). lia.
              ** rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
                 apply htarget.
                 pose proof (formulaCode_and_right_lt left right). lia.
           ++ split; [reflexivity |].
              rewrite raw_add_numeral_values_syntax by exact hPA.
              reflexivity.
  - right. right. right. right. left.
    exists (rawNumeralValue M (formulaCode left)),
      (rawQuotedFormulaCode M left),
      (rawNumeralValue M (Formula.bound left)),
      (rawNumeralValue M (formulaCode right)),
      (rawQuotedFormulaCode M right),
      (rawNumeralValue M (Formula.bound right)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply formulaCode_or_left_lt.
    + split.
      * split.
        -- rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
           apply hsource. pose proof (formulaCode_or_left_lt left right). lia.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. pose proof (formulaCode_or_left_lt left right). lia.
      * split.
        -- apply raw_lt_numeralValue_of_lt; [exact hPA |].
           apply formulaCode_or_right_lt.
        -- split.
           ++ split.
              ** rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
                 apply hsource.
                 pose proof (formulaCode_or_right_lt left right). lia.
              ** rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
                 apply htarget.
                 pose proof (formulaCode_or_right_lt left right). lia.
           ++ split; [reflexivity |].
              rewrite raw_add_numeral_values_syntax by exact hPA.
              reflexivity.
  - right. right. right. right. right. left.
    exists (rawNumeralValue M (formulaCode child)),
      (rawQuotedFormulaCode M child),
      (rawNumeralValue M (Formula.bound child)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply formulaCode_all_child_lt.
    + split.
      * split.
        -- rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
           apply hsource. pose proof (formulaCode_all_child_lt child). lia.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. pose proof (formulaCode_all_child_lt child). lia.
      * split; reflexivity.
  - right. right. right. right. right. right.
    exists (rawNumeralValue M (formulaCode child)),
      (rawQuotedFormulaCode M child),
      (rawNumeralValue M (Formula.bound child)).
    split.
    + apply raw_lt_numeralValue_of_lt; [exact hPA |].
      apply formulaCode_ex_child_lt.
    + split.
      * split.
        -- rewrite <- rawStandardFormulaBoundSourceAt_formulaCode.
           apply hsource. pose proof (formulaCode_ex_child_lt child). lia.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. pose proof (formulaCode_ex_child_lt child). lia.
      * split; reflexivity.
Qed.

Theorem raw_codedFormulaBound_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  RawCodedFormulaBound M
    (rawQuotedFormulaCode M phi)
    (rawNumeralValue M (Formula.bound phi)).
Proof.
  intros M hPA root.
  rewrite rawQuotedFormulaCode_standard by exact hPA.
  set (limit := S (formulaCode root)).
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaBoundSourceAt M)) as
    [sourceCode [sourceStep hsource]].
  destruct (finite_vector_beta_code M hPA limit
    (rawStandardFormulaBoundTargetAt M)) as
    [targetCode [targetStep htarget]].
  exists sourceCode, sourceStep, targetCode, targetStep.
  unfold RawCodedFormulaBoundTrace.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
      as [k [hk ->]].
    exists (rawStandardFormulaBoundSourceAt M k). apply hsource. exact hk.
  - split.
    + intros index hindex.
      destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
        as [k [hk ->]].
      exists (rawStandardFormulaBoundTargetAt M k). apply htarget. exact hk.
    + split.
      * split.
        -- pose proof (hsource (formulaCode root)) as hrootSource.
           specialize (hrootSource ltac:(unfold limit; lia)).
           rewrite rawStandardFormulaBoundSourceAt_formulaCode in hrootSource.
           rewrite rawQuotedFormulaCode_standard in hrootSource by exact hPA.
           exact hrootSource.
        -- rewrite <- rawStandardFormulaBoundTargetAt_formulaCode.
           apply htarget. unfold limit. lia.
      * intros index input output hindex [hinput houtput].
        destruct (raw_lt_numeralValue_cases M hPA index limit hindex)
          as [k [hk ->]].
        assert (hinputCanonical : input =
            rawStandardFormulaBoundSourceAt M k).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            sourceCode sourceStep (rawNumeralValue M k) input
            (rawStandardFormulaBoundSourceAt M k)
            hinput (hsource k hk)).
        }
        assert (houtputCanonical : output =
            rawStandardFormulaBoundTargetAt M k).
        {
          exact (raw_codedAssignmentLookup_functional M hPA
            targetCode targetStep (rawNumeralValue M k) output
            (rawStandardFormulaBoundTargetAt M k)
            houtput (htarget k hk)).
        }
        subst input. subst output.
        destruct (checkedDecodeFormula k) as [decoded |] eqn:hdecoded.
        -- pose proof (checkedDecodeFormula_sound k decoded hdecoded)
             as [_ hcanonical].
           unfold rawStandardFormulaBoundSourceAt,
             rawStandardFormulaBoundTargetAt.
           rewrite hdecoded. rewrite <- hcanonical.
           apply (raw_standardFormulaBound_closed_step M hPA limit
             sourceCode sourceStep targetCode targetStep hsource htarget).
           now rewrite hcanonical.
        -- unfold rawStandardFormulaBoundSourceAt,
             rawStandardFormulaBoundTargetAt.
           rewrite hdecoded. right. left. split; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Standard realization of iterated universal closure.

    The raw graph itself permits a genuinely nonstandard number of closure
    steps.  For quotation adequacy we only need the finite table whose [k]th
    entry is the code of [closeN k phi]. *)

Lemma formula_closeN_succ_outside : forall count phi,
  Formula.closeN (S count) phi = pAll (Formula.closeN count phi).
Proof.
  induction count as [|count IH]; intro phi; cbn [Formula.closeN].
  - reflexivity.
  - exact (IH (pAll phi)).
Qed.

Definition rawStandardUniversalClosureAt
    (M : RawPAModel) (phi : formula) (index : nat) : M :=
  rawQuotedFormulaCode M (Formula.closeN index phi).

Theorem raw_codedUniversalClosure_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall count phi,
  RawCodedUniversalClosure M
    (rawNumeralValue M count)
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M (Formula.closeN count phi)).
Proof.
  intros M hPA count phi.
  destruct (finite_vector_beta_code M hPA (S count)
    (rawStandardUniversalClosureAt M phi)) as
    [code [step hlookup]].
  exists code, step.
  unfold RawCodedUniversalClosureTrace.
  split.
  - intros index hindex.
    destruct (raw_lt_numeralValue_cases M hPA index (S count) hindex)
      as [k [hk ->]].
    exists (rawStandardUniversalClosureAt M phi k).
    apply hlookup. exact hk.
  - split.
    + change (RawCodedAssignmentLookup M code step
        (rawNumeralValue M 0) (rawStandardUniversalClosureAt M phi 0)).
      apply hlookup. lia.
    + split.
      * change (RawCodedAssignmentLookup M code step
          (rawNumeralValue M count)
          (rawStandardUniversalClosureAt M phi count)).
        apply hlookup. lia.
      * split.
        -- intros index current next hindex hcurrent hnext.
           destruct (raw_lt_numeralValue_cases M hPA index count hindex)
             as [k [hk ->]].
           assert (hcurrentCanonical : current =
               rawStandardUniversalClosureAt M phi k).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               code step (rawNumeralValue M k) current
               (rawStandardUniversalClosureAt M phi k)
               hcurrent (hlookup k ltac:(lia))).
           }
           assert (hnextCanonical : next =
               rawStandardUniversalClosureAt M phi (S k)).
           {
             exact (raw_codedAssignmentLookup_functional M hPA
               code step (rawNumeralValue M (S k)) next
               (rawStandardUniversalClosureAt M phi (S k))
               hnext (hlookup (S k) ltac:(lia))).
           }
           subst current. subst next.
           unfold rawStandardUniversalClosureAt.
           rewrite formula_closeN_succ_outside. reflexivity.
        -- change (rawLe M (rawNumeralValue M 0)
             (rawNumeralValue M count)).
           apply rawLe_numerals_of_le; [exact hPA | lia].
Qed.

(** The PA successor instance is obtained from the available single-variable
    operation by first opening space above variable zero.  This identity is
    the small but important capture-avoidance seam in the construction. *)
Lemma standardFormulaShift_one_one_then_substitute_succ : forall phi,
  standardFormulaSingleSubstitution (tSucc (tVar 0)) 0
    (standardFormulaShift 1 1 phi) =
  Formula.subst Formula.substSuccVar phi.
Proof.
  intro phi.
  rewrite standardFormulaSingleSubstitution_zero,
    standardFormulaShift_as_rename, Formula.subst_rename.
  apply Formula.subst_ext. intros [|index].
  - reflexivity.
  - unfold standardShiftRenaming, Formula.instTerm,
      Formula.substSuccVar. cbn.
    destruct (index <? 0) eqn:hnegative.
    + apply Nat.ltb_lt in hnegative. lia.
    + f_equal. lia.
Qed.

(** ------------------------------------------------------------------
    The transparent graph for an induction witness. *)

Definition axiomWitnessEx9 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body)))))))).

Definition axiomWitnessAnd10
    (a b c d f g h i j k : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f
    (pAnd g (pAnd h (pAnd i (pAnd j k)))))))).

(** The nine internal codes, from outermost to innermost existential, are:
    shifted source, successor instance, zero instance, universal source,
    step implication, universal step, premise, induction body, and closure
    count.  Every equality below is itself imposed by a transparent syntax
    constructor; no carrier element is decoded. *)
Definition codedPAAxiomInductionTermAt
    (source axiom : term) : formula :=
  axiomWitnessEx9 (axiomWitnessAnd10
    (codedFormulaShiftTermAt (Term.numeral 1) (Term.numeral 1)
      (liftTerm 9 source) (tVar 8))
    (codedFormulaSingleSubstitutionTermAt
      (Term.numeral (termCode (tSucc (tVar 0))))
      (tVar 8) (tVar 7))
    (codedFormulaSingleSubstitutionTermAt
      (Term.numeral (termCode tZero))
      (liftTerm 9 source) (tVar 6))
    (formulaAllCodeTermAt (tVar 5) (liftTerm 9 source))
    (formulaImpCodeTermAt (tVar 4) (liftTerm 9 source) (tVar 7))
    (formulaAllCodeTermAt (tVar 3) (tVar 4))
    (formulaAndCodeTermAt (tVar 2) (tVar 6) (tVar 3))
    (formulaImpCodeTermAt (tVar 1) (tVar 2) (tVar 5))
    (codedFormulaBoundTermAt (tVar 1) (tVar 0))
    (codedUniversalClosureTermAt (tVar 0) (tVar 1)
      (liftTerm 9 axiom))).

Definition RawCodedPAAxiomInduction (M : RawPAModel)
    (source axiom : M) : Prop :=
  exists shifted successorInstance zeroInstance sourceAll
      stepImp stepAll premise body closureCount : M,
    RawCodedFormulaShift M
      (rawNumeralValue M 1) (rawNumeralValue M 1)
      source shifted /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode (tSucc (tVar 0))))
      shifted successorInstance /\
    RawCodedFormulaSingleSubstitution M
      (rawNumeralValue M (termCode tZero)) source zeroInstance /\
    sourceAll = rawFormulaAllCode M source /\
    stepImp = rawFormulaImpCode M source successorInstance /\
    stepAll = rawFormulaAllCode M stepImp /\
    premise = rawFormulaAndCode M zeroInstance stepAll /\
    body = rawFormulaImpCode M premise sourceAll /\
    RawCodedFormulaBound M body closureCount /\
    RawCodedUniversalClosure M closureCount body axiom.

Arguments RawCodedPAAxiomInduction M source axiom : clear implicits.

Lemma raw_axiomWitness_eval_liftTerm_nine : forall (M : RawPAModel)
    a b c d f g h i j (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d
      (scons M f (scons M g (scons M h (scons M i (scons M j e)))))))))
    (liftTerm 9 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g h i j e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 9) with
    (S (S (S (S (S (S (S (S (S index))))))))) by lia.
  reflexivity.
Qed.

Lemma raw_sat_codedPAAxiomInductionTermAt_iff : forall
    (M : RawPAModel) e source axiom,
  raw_formula_sat M e (codedPAAxiomInductionTermAt source axiom) <->
  RawCodedPAAxiomInduction M
    (raw_term_eval M e source) (raw_term_eval M e axiom).
Proof.
  intros M e source axiom.
  unfold codedPAAxiomInductionTermAt, axiomWitnessEx9,
    axiomWitnessAnd10, RawCodedPAAxiomInduction.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaShiftTermAt_iff.
  repeat setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  setoid_rewrite raw_sat_formulaAllCodeTermAt_iff.
  setoid_rewrite raw_sat_formulaImpCodeTermAt_iff.
  setoid_rewrite raw_sat_formulaAndCodeTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaBoundTermAt_iff.
  setoid_rewrite raw_sat_codedUniversalClosureTermAt_iff.
  repeat setoid_rewrite raw_axiomWitness_eval_liftTerm_nine.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    The complete seven-way PA-axiom witness relation. *)

Definition codedPAAxiomFiniteWitnessTermAt
    (tag : nat) (axiomFormula : formula)
    (witness axiom : term) : formula :=
  pAnd
    (codeList1TermAt witness (Term.numeral tag))
    (pEq axiom
      (Term.numeral (formulaCode (Formula.sealPA axiomFormula)))).

Definition RawCodedPAAxiomFiniteWitness (M : RawPAModel)
    (tag : nat) (axiomFormula : formula)
    (witness axiom : M) : Prop :=
  witness = rawCodeList1 M (rawNumeralValue M tag) /\
  axiom = rawNumeralValue M
    (formulaCode (Formula.sealPA axiomFormula)).

Lemma raw_sat_codedPAAxiomFiniteWitnessTermAt_iff : forall
    (M : RawPAModel) e tag axiomFormula witness axiom,
  raw_formula_sat M e
    (codedPAAxiomFiniteWitnessTermAt tag axiomFormula witness axiom) <->
  RawCodedPAAxiomFiniteWitness M tag axiomFormula
    (raw_term_eval M e witness) (raw_term_eval M e axiom).
Proof.
  intros. unfold codedPAAxiomFiniteWitnessTermAt,
    RawCodedPAAxiomFiniteWitness.
  cbn [raw_formula_sat].
  rewrite raw_sat_codeList1TermAt_iff, !raw_term_eval_numeral.
  reflexivity.
Qed.

Definition codedPAAxiomWitnessTermAt
    (witness axiom : term) : formula :=
  pOr
    (codedPAAxiomFiniteWitnessTermAt
      0 Formula.succInj witness axiom)
  (pOr
    (codedPAAxiomFiniteWitnessTermAt
      1 Formula.zeroNotSucc witness axiom)
  (pOr
    (codedPAAxiomFiniteWitnessTermAt
      2 Formula.addZero witness axiom)
  (pOr
    (codedPAAxiomFiniteWitnessTermAt
      3 Formula.addSucc witness axiom)
  (pOr
    (codedPAAxiomFiniteWitnessTermAt
      4 Formula.mulZero witness axiom)
  (pOr
    (codedPAAxiomFiniteWitnessTermAt
      5 Formula.mulSucc witness axiom)
    (pEx (pAnd
      (codeList2TermAt (liftTerm 1 witness)
        (Term.numeral 6) (tVar 0))
      (codedPAAxiomInductionTermAt
        (tVar 0) (liftTerm 1 axiom))))))))).

Definition RawCodedPAAxiomWitness (M : RawPAModel)
    (witness axiom : M) : Prop :=
  RawCodedPAAxiomFiniteWitness M 0 Formula.succInj witness axiom \/
  RawCodedPAAxiomFiniteWitness M 1 Formula.zeroNotSucc witness axiom \/
  RawCodedPAAxiomFiniteWitness M 2 Formula.addZero witness axiom \/
  RawCodedPAAxiomFiniteWitness M 3 Formula.addSucc witness axiom \/
  RawCodedPAAxiomFiniteWitness M 4 Formula.mulZero witness axiom \/
  RawCodedPAAxiomFiniteWitness M 5 Formula.mulSucc witness axiom \/
  exists source : M,
    witness = rawCodeList2 M (rawNumeralValue M 6) source /\
    RawCodedPAAxiomInduction M source axiom.

Arguments RawCodedPAAxiomWitness M witness axiom : clear implicits.

Lemma raw_sat_codedPAAxiomWitnessTermAt_iff : forall
    (M : RawPAModel) e witness axiom,
  raw_formula_sat M e (codedPAAxiomWitnessTermAt witness axiom) <->
  RawCodedPAAxiomWitness M
    (raw_term_eval M e witness) (raw_term_eval M e axiom).
Proof.
  intros M e witness axiom.
  unfold codedPAAxiomWitnessTermAt, RawCodedPAAxiomWitness.
  cbn [raw_formula_sat].
  repeat setoid_rewrite raw_sat_codedPAAxiomFiniteWitnessTermAt_iff.
  setoid_rewrite raw_sat_codeList2TermAt_iff.
  setoid_rewrite raw_sat_codedPAAxiomInductionTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_one.
  repeat setoid_rewrite raw_term_eval_numeral.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Standard quotation adequacy. *)

Definition standardPAAxiomInductionShifted (phi : formula) : formula :=
  standardFormulaShift 1 1 phi.

Definition standardPAAxiomInductionSuccessorInstance
    (phi : formula) : formula :=
  standardFormulaSingleSubstitution (tSucc (tVar 0)) 0
    (standardPAAxiomInductionShifted phi).

Definition standardPAAxiomInductionZeroInstance
    (phi : formula) : formula :=
  standardFormulaSingleSubstitution tZero 0 phi.

Definition standardPAAxiomInductionBody (phi : formula) : formula :=
  pImp
    (pAnd (standardPAAxiomInductionZeroInstance phi)
      (pAll (pImp phi
        (standardPAAxiomInductionSuccessorInstance phi))))
    (pAll phi).

Lemma standardPAAxiomInductionBody_eq : forall phi,
  standardPAAxiomInductionBody phi = Formula.inductionForm phi.
Proof.
  intro phi.
  unfold standardPAAxiomInductionBody,
    standardPAAxiomInductionZeroInstance,
    standardPAAxiomInductionSuccessorInstance,
    standardPAAxiomInductionShifted, Formula.inductionForm.
  rewrite standardFormulaShift_one_one_then_substitute_succ.
  rewrite standardFormulaSingleSubstitution_zero.
  rewrite <- Formula.substZero_eq_instTerm. reflexivity.
Qed.

Theorem raw_codedPAAxiomInduction_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  RawCodedPAAxiomInduction M
    (rawQuotedFormulaCode M phi)
    (rawQuotedFormulaCode M
      (Formula.sealPA (Formula.inductionForm phi))).
Proof.
  intros M hPA phi.
  rewrite <- standardPAAxiomInductionBody_eq.
  unfold Formula.sealPA.
  exists
    (rawQuotedFormulaCode M (standardPAAxiomInductionShifted phi)),
    (rawQuotedFormulaCode M
      (standardPAAxiomInductionSuccessorInstance phi)),
    (rawQuotedFormulaCode M
      (standardPAAxiomInductionZeroInstance phi)),
    (rawQuotedFormulaCode M (pAll phi)),
    (rawQuotedFormulaCode M
      (pImp phi (standardPAAxiomInductionSuccessorInstance phi))),
    (rawQuotedFormulaCode M
      (pAll (pImp phi
        (standardPAAxiomInductionSuccessorInstance phi)))),
    (rawQuotedFormulaCode M
      (pAnd (standardPAAxiomInductionZeroInstance phi)
        (pAll (pImp phi
          (standardPAAxiomInductionSuccessorInstance phi))))),
    (rawQuotedFormulaCode M (standardPAAxiomInductionBody phi)),
    (rawNumeralValue M (Formula.bound
      (standardPAAxiomInductionBody phi))).
  split.
  - unfold standardPAAxiomInductionShifted.
    apply raw_codedFormulaShift_standard. exact hPA.
  - split.
    + rewrite <- rawQuotedTermCode_standard by exact hPA.
      unfold standardPAAxiomInductionSuccessorInstance.
      apply raw_codedFormulaSingleSubstitution_standard_recursive.
      exact hPA.
    + split.
      * rewrite <- rawQuotedTermCode_standard by exact hPA.
        unfold standardPAAxiomInductionZeroInstance.
        apply raw_codedFormulaSingleSubstitution_standard_recursive.
        exact hPA.
      * split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split; [reflexivity |].
        split.
        -- apply raw_codedFormulaBound_standard. exact hPA.
        -- apply raw_codedUniversalClosure_standard. exact hPA.
Qed.

Lemma raw_codedPAAxiomFiniteWitness_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tag axiomFormula,
  RawCodedPAAxiomFiniteWitness M tag axiomFormula
    (rawNumeralValue M (PAListCode.listCode [tag]))
    (rawQuotedFormulaCode M (Formula.sealPA axiomFormula)).
Proof.
  intros M hPA tag axiomFormula. split.
  - unfold rawCodeList1. symmetry.
    change (rawListCode M (map (rawNumeralValue M) [tag]) =
      rawNumeralValue M (PAListCode.listCode [tag])).
    apply rawListCode_standard. exact hPA.
  - apply rawQuotedFormulaCode_standard. exact hPA.
Qed.

(** Every metatheoretic [PAAxiomWitness], including every source formula for
    induction, is accepted by the arbitrary-model graph at its standard
    numeral code.  No standardness assumption is made about the ambient
    model beyond the PA axioms themselves. *)
Theorem raw_codedPAAxiomWitness_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall witness,
  RawCodedPAAxiomWitness M
    (rawNumeralValue M (axiomWitnessCode witness))
    (rawQuotedFormulaCode M (witnessedAxiom witness)).
Proof.
  intros M hPA witness. destruct witness as
    [| | | | | |phi]; cbn [axiomWitnessCode witnessedAxiom].
  - left. apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. left.
    apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. right. left.
    apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. right. right. left.
    apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. right. right. right. left.
    apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. right. right. right. right. left.
    apply raw_codedPAAxiomFiniteWitness_standard. exact hPA.
  - right. right. right. right. right. right.
    exists (rawQuotedFormulaCode M phi). split.
    + rewrite rawQuotedFormulaCode_standard by exact hPA.
      unfold rawCodeList2. symmetry.
      change (rawListCode M
        (map (rawNumeralValue M) [6; formulaCode phi]) =
        rawNumeralValue M (PAListCode.listCode [6; formulaCode phi])).
      apply rawListCode_standard. exact hPA.
    + apply raw_codedPAAxiomInduction_standard. exact hPA.
Qed.

Corollary raw_sat_codedPAAxiomWitnessTermAt_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall e witness,
  raw_formula_sat M e
    (codedPAAxiomWitnessTermAt
      (Term.numeral (axiomWitnessCode witness))
      (Term.numeral (formulaCode (witnessedAxiom witness)))).
Proof.
  intros M hPA e witness.
  apply (proj2 (raw_sat_codedPAAxiomWitnessTermAt_iff M e _ _)).
  rewrite !raw_term_eval_numeral.
  rewrite <- rawQuotedFormulaCode_standard by exact hPA.
  apply raw_codedPAAxiomWitness_standard. exact hPA.
Qed.

End PABoundedRawCodedPAAxiomWitness.
