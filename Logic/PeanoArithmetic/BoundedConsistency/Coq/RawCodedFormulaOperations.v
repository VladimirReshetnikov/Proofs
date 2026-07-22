(**
  Transparent operations on formula codes in arbitrary models of PA.

  The executable decoders in [CodedSyntax] are useful in the standard model,
  but they cannot be applied to a nonstandard carrier element.  This file
  therefore presents code operations by genuine PA formulae and beta-coded
  traces.  Every recursive edge points to a strictly earlier row.  The raw
  semantics are stated over law-free models; PA hypotheses enter only for
  beta functionality, constructor separation, and definable induction.

  There are two deliberately explicit layers:

  - negation and iterated universal closure operate directly on formula
    constructor codes;
  - renaming and single-variable opening use term-operation certificates at
    equality atoms.  A later formula traversal may cite those certificates
    rather than pretending that arbitrary term payloads can be transformed
    without a term-syntax witness.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency PolynomialPairInjectivity RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedAssignment
  RawCodedFormulaRankStep RawCodedFormulaRankStepFunctionality
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization
  RawCodedFormulaRankTotality.

Import ListNotations.

Module PABoundedRawCodedFormulaOperations.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedConsistency.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankStepFunctionality.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.
Import PABoundedRawCodedFormulaRankTotality.

Definition operationAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition operationAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition operationAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition operationAnd6 (a b c d f g : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f g)))).

Definition operationEx2 (body : formula) : formula := pEx (pEx body).
Definition operationEx3 (body : formula) : formula := pEx (pEx (pEx body)).
Definition operationEx4 (body : formula) : formula :=
  pEx (pEx (pEx (pEx body))).
Definition operationEx6 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx body))))).

(** ------------------------------------------------------------------
    Negation.  [pImp phi pBot] is the project's primitive presentation of
    logical negation. *)

Definition rawFormulaBotCodeTerm : term :=
  codeList1Term (Term.numeral 1).

Definition codedFormulaNegationTermAt
    (input output : term) : formula :=
  formulaImpCodeTermAt output input rawFormulaBotCodeTerm.

Definition RawCodedFormulaNegation (M : RawPAModel)
    (input output : M) : Prop :=
  output = rawFormulaImpCode M input (rawFormulaBotCode M).

Arguments RawCodedFormulaNegation M input output : clear implicits.

Lemma raw_eval_rawFormulaBotCodeTerm : forall (M : RawPAModel) e,
  raw_term_eval M e rawFormulaBotCodeTerm = rawFormulaBotCode M.
Proof. reflexivity. Qed.

Lemma raw_sat_codedFormulaNegationTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) input output,
  raw_formula_sat M e (codedFormulaNegationTermAt input output) <->
  RawCodedFormulaNegation M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e input output.
  unfold codedFormulaNegationTermAt, RawCodedFormulaNegation.
  rewrite raw_sat_formulaImpCodeTermAt_iff.
  rewrite raw_eval_rawFormulaBotCodeTerm. reflexivity.
Qed.

Theorem raw_codedFormulaNegation_functional : forall (M : RawPAModel),
  forall input output output',
  RawCodedFormulaNegation M input output ->
  RawCodedFormulaNegation M input output' -> output = output'.
Proof. intros M input output output' -> ->. reflexivity. Qed.

Theorem raw_codedFormulaNegation_constructor_inversion : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall input output left right,
  RawCodedFormulaNegation M input output ->
  output = rawFormulaImpCode M left right ->
  input = left /\ right = rawFormulaBotCode M.
Proof.
  intros M hPA input output left right hneg himp.
  unfold RawCodedFormulaNegation in hneg.
  pose proof (raw_listNode_injective_of_pair_injective M hPA
    (raw_pair_injective_of_proof polynomialPairInjectivityProof M hPA))
    as hnode.
  pose proof (raw_codeList3_injective M hnode
    (rawNumeralValue M 2) input (rawFormulaBotCode M)
    (rawNumeralValue M 2) left right) as hinjective.
  destruct (hinjective (eq_trans (eq_sym hneg) himp))
    as [_ [hleft hright]]. split; [exact hleft | symmetry; exact hright].
Qed.

(** ------------------------------------------------------------------
    Iterated universal closure.

    Row zero is [input].  Row [S i] is the universal constructor applied to
    row [i], and row [count] is [output].  This convention makes count zero
    the identity operation and permits model-internal, nonstandard counts. *)

Definition codedUniversalClosureRowsTermAt
    (code step count : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 count))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 3 code) (liftTerm 3 step)
          (tVar 2) (tVar 1))
        (pImp
          (codedAssignmentLookupTermAt
            (liftTerm 3 code) (liftTerm 3 step)
            (tSucc (tVar 2)) (tVar 0))
          (formulaAllCodeTermAt (tVar 0) (tVar 1))))))).

Definition RawCodedUniversalClosureRows (M : RawPAModel)
    (code step count : M) : Prop :=
  forall index current next : M,
    rawLt M index count ->
    RawCodedAssignmentLookup M code step index current ->
    RawCodedAssignmentLookup M code step (raw_succ M index) next ->
    next = rawFormulaAllCode M current.

Arguments RawCodedUniversalClosureRows M code step count
  : clear implicits.

Lemma raw_operation_eval_liftTerm_three : forall (M : RawPAModel)
    a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e)))
    (liftTerm 3 t) = raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 3) with (S (S (S i))) by lia. reflexivity.
Qed.

Lemma raw_sat_codedUniversalClosureRowsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code step count,
  raw_formula_sat M e
    (codedUniversalClosureRowsTermAt code step count) <->
  RawCodedUniversalClosureRows M
    (raw_term_eval M e code) (raw_term_eval M e step)
    (raw_term_eval M e count).
Proof.
  intros M e code step count.
  unfold codedUniversalClosureRowsTermAt,
    RawCodedUniversalClosureRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_formulaAllCodeTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedUniversalClosureTraceTermAt
    (code step count input output : term) : formula :=
  operationAnd5
    (codedAssignmentDefinedThroughTermAt code step (tSucc count))
    (codedAssignmentLookupTermAt code step tZero input)
    (codedAssignmentLookupTermAt code step count output)
    (codedUniversalClosureRowsTermAt code step count)
    (Formula.leTermAt tZero count).

Definition RawCodedUniversalClosureTrace (M : RawPAModel)
    (code step count input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M code step (raw_succ M count) /\
  RawCodedAssignmentLookup M code step (raw_zero M) input /\
  RawCodedAssignmentLookup M code step count output /\
  RawCodedUniversalClosureRows M code step count /\
  rawLe M (raw_zero M) count.

Arguments RawCodedUniversalClosureTrace M code step count input output
  : clear implicits.

Lemma raw_sat_codedUniversalClosureTraceTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code step count input output,
  raw_formula_sat M e
    (codedUniversalClosureTraceTermAt code step count input output) <->
  RawCodedUniversalClosureTrace M
    (raw_term_eval M e code) (raw_term_eval M e step)
    (raw_term_eval M e count) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedUniversalClosureTraceTermAt,
    RawCodedUniversalClosureTrace, operationAnd5.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff.
  rewrite raw_sat_codedUniversalClosureRowsTermAt_iff.
  rewrite raw_sat_leTermAt_iff_rank. reflexivity.
Qed.

Definition codedUniversalClosureTermAt
    (count input output : term) : formula :=
  operationEx2
    (codedUniversalClosureTraceTermAt
      (tVar 1) (tVar 0)
      (liftTerm 2 count) (liftTerm 2 input) (liftTerm 2 output)).

Definition RawCodedUniversalClosure (M : RawPAModel)
    (count input output : M) : Prop :=
  exists code step : M,
    RawCodedUniversalClosureTrace M code step count input output.

Arguments RawCodedUniversalClosure M count input output : clear implicits.

Lemma raw_sat_codedUniversalClosureTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) count input output,
  raw_formula_sat M e
    (codedUniversalClosureTermAt count input output) <->
  RawCodedUniversalClosure M
    (raw_term_eval M e count) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e count input output.
  unfold codedUniversalClosureTermAt, operationEx2,
    RawCodedUniversalClosure.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedUniversalClosureTraceTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem raw_codedUniversalClosure_zero : forall (M : RawPAModel),
  RawPASatisfies M -> forall input output,
  RawCodedUniversalClosure M (raw_zero M) input output ->
  output = input.
Proof.
  intros M hPA input output
    (code & step & [_ [hinput [houtput _]]]).
  exact (raw_codedAssignmentLookup_functional M hPA
    code step (raw_zero M) output input houtput hinput).
Qed.

Theorem raw_codedUniversalClosure_succ_inversion : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall count input output,
  RawCodedUniversalClosure M (raw_succ M count) input output ->
  exists previous,
    RawCodedUniversalClosure M count input previous /\
    output = rawFormulaAllCode M previous.
Proof.
  intros M hPA count input output
    (code & step & hdefined & hinput & houtput & hrows & hzeroLe).
  assert (hcountSucc : rawLt M count (raw_succ M count)).
  { exact (raw_assignment_lt_self_succ M hPA count). }
  assert (hcountDefined : rawLt M count
      (raw_succ M (raw_succ M count))).
  {
    exact (raw_assignment_lt_trans M hPA count (raw_succ M count)
      (raw_succ M (raw_succ M count)) hcountSucc
      (raw_assignment_lt_self_succ M hPA (raw_succ M count))).
  }
  destruct (hdefined count hcountDefined) as [previous hprevious].
  exists previous. split.
  - exists code, step. repeat split.
    + intros index hindex.
      exact (hdefined index
        (raw_assignment_lt_trans M hPA index (raw_succ M count)
          (raw_succ M (raw_succ M count)) hindex
          (raw_assignment_lt_self_succ M hPA (raw_succ M count)))).
    + exact hinput.
    + exact hprevious.
    + intros index current next hindex hcurrent hnext.
      exact (hrows index current next
        (raw_assignment_lt_trans M hPA index count (raw_succ M count)
          hindex hcountSucc) hcurrent hnext).
    + apply raw_rank_zero_le. exact hPA.
  - exact (hrows count previous output hcountSucc hprevious houtput).
Qed.

(** ------------------------------------------------------------------
    Synchronized term-operation traces.

    These traces are the explicit atomic premise used by formula renaming
    and opening.  They do not rely on a decoder. *)

Definition codedTermOperationPairLookupTermAt
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  pAnd
    (codedAssignmentLookupTermAt sourceCode sourceStep index input)
    (codedAssignmentLookupTermAt targetCode targetStep index output).

Definition RawCodedTermOperationPairLookup (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  RawCodedAssignmentLookup M sourceCode sourceStep index input /\
  RawCodedAssignmentLookup M targetCode targetStep index output.

Arguments RawCodedTermOperationPairLookup
  M sourceCode sourceStep targetCode targetStep index input output
  : clear implicits.

Lemma raw_sat_codedTermOperationPairLookupTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermOperationPairLookupTermAt
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermOperationPairLookup M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedTermOperationPairLookupTermAt,
    RawCodedTermOperationPairLookup.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff. reflexivity.
Qed.

Lemma raw_operation_eval_liftTerm_one : forall (M : RawPAModel)
    a (e : nat -> M) t,
  raw_term_eval M (scons M a e) (liftTerm 1 t) = raw_term_eval M e t.
Proof.
  intros M a e t. unfold liftTerm. rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_operation_eval_liftTerm_six : forall (M : RawPAModel)
    a b c d f g (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c
      (scons M d (scons M f (scons M g e))))))
    (liftTerm 6 t) = raw_term_eval M e t.
Proof.
  intros M a b c d f g e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 6) with (S (S (S (S (S (S i)))))) by lia.
  reflexivity.
Qed.

(** Shift by [amount] above [cutoff].  The special case amount one is the
    de Bruijn renaming used by universal introduction. *)
Definition codedShiftedIndexTermAt
    (cutoff amount inputIndex outputIndex : term) : formula :=
  pOr
    (pAnd (Formula.ltTermAt inputIndex cutoff)
      (pEq outputIndex inputIndex))
    (pAnd (Formula.leTermAt cutoff inputIndex)
      (pEq outputIndex (tAdd inputIndex amount))).

Definition RawShiftedIndex (M : RawPAModel)
    (cutoff amount inputIndex outputIndex : M) : Prop :=
  (rawLt M inputIndex cutoff /\ outputIndex = inputIndex) \/
  (rawLe M cutoff inputIndex /\
    outputIndex = raw_add M inputIndex amount).

Arguments RawShiftedIndex M cutoff amount inputIndex outputIndex
  : clear implicits.

Lemma raw_sat_codedShiftedIndexTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    cutoff amount inputIndex outputIndex,
  raw_formula_sat M e
    (codedShiftedIndexTermAt cutoff amount inputIndex outputIndex) <->
  RawShiftedIndex M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e inputIndex) (raw_term_eval M e outputIndex).
Proof.
  intros. unfold codedShiftedIndexTermAt, RawShiftedIndex.
  cbn [raw_formula_sat].
  rewrite raw_sat_ltTermAt_iff, raw_sat_leTermAt_iff_rank.
  reflexivity.
Qed.

Definition codedTermShiftVariableRowTermAt
    (cutoff amount input output : term) : formula :=
  operationEx2 (operationAnd3
    (termVarCodeTermAt (liftTerm 2 input) (tVar 1))
    (termVarCodeTermAt (liftTerm 2 output) (tVar 0))
    (codedShiftedIndexTermAt
      (liftTerm 2 cutoff) (liftTerm 2 amount) (tVar 1) (tVar 0))).

Definition RawCodedTermShiftVariableRow (M : RawPAModel)
    (cutoff amount input output : M) : Prop :=
  exists inputIndex outputIndex : M,
    input = rawTermVarCode M inputIndex /\
    output = rawTermVarCode M outputIndex /\
    RawShiftedIndex M cutoff amount inputIndex outputIndex.

Arguments RawCodedTermShiftVariableRow
  M cutoff amount input output : clear implicits.

Lemma raw_sat_codedTermShiftVariableRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) cutoff amount input output,
  raw_formula_sat M e
    (codedTermShiftVariableRowTermAt cutoff amount input output) <->
  RawCodedTermShiftVariableRow M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e cutoff amount input output.
  unfold codedTermShiftVariableRowTermAt, operationEx2, operationAnd3,
    RawCodedTermShiftVariableRow.
  cbn [raw_formula_sat]. split.
  - intros (ii & oi & hin & hout & hindex).
    exists ii, oi.
    rewrite raw_sat_termVarCodeTermAt_iff in hin, hout.
    rewrite raw_sat_codedShiftedIndexTermAt_iff in hindex.
    repeat rewrite raw_rankTraversal_eval_liftTerm_two in hin, hout, hindex.
    cbn [raw_term_eval scons] in hin, hout, hindex.
    rewrite raw_rankTraversal_eval_liftTerm_two in hindex.
    split; [exact hin |]. split; [exact hout | exact hindex].
  - intros (ii & oi & hin & hout & hindex). exists ii, oi.
    rewrite raw_sat_termVarCodeTermAt_iff,
      raw_sat_termVarCodeTermAt_iff,
      raw_sat_codedShiftedIndexTermAt_iff.
    repeat rewrite raw_rankTraversal_eval_liftTerm_two.
    cbn [raw_term_eval scons].
    split; [exact hin |]. split; [exact hout | exact hindex].
Qed.

(** Opening at [cutoff] with an already capture-avoiding lifted replacement.
    Variables below the cutoff are fixed, the cutoff variable is replaced,
    and variables above it are decremented. *)
Definition codedTermOpeningVariableRowTermAt
    (cutoff liftedReplacement input output : term) : formula :=
  pEx (pAnd
    (termVarCodeTermAt (liftTerm 1 input) (tVar 0))
    (pOr
      (pAnd (Formula.ltTermAt (tVar 0) (liftTerm 1 cutoff))
        (termVarCodeTermAt (liftTerm 1 output) (tVar 0)))
      (pOr
        (pAnd (pEq (tVar 0) (liftTerm 1 cutoff))
          (pEq (liftTerm 1 output) (liftTerm 1 liftedReplacement)))
        (pEx (operationAnd3
          (pEq (liftTerm 1 (tVar 0)) (tSucc (tVar 0)))
          (Formula.ltTermAt (liftTerm 1 (liftTerm 1 cutoff))
            (liftTerm 1 (tVar 0)))
          (termVarCodeTermAt
            (liftTerm 1 (liftTerm 1 output)) (tVar 0))))))).

Definition RawCodedTermOpeningVariableRow (M : RawPAModel)
    (cutoff liftedReplacement input output : M) : Prop :=
  exists inputIndex : M,
    input = rawTermVarCode M inputIndex /\
    ((rawLt M inputIndex cutoff /\
        output = rawTermVarCode M inputIndex) \/
     (inputIndex = cutoff /\ output = liftedReplacement) \/
     (exists predecessor : M,
        inputIndex = raw_succ M predecessor /\
        rawLt M cutoff inputIndex /\
        output = rawTermVarCode M predecessor)).

Arguments RawCodedTermOpeningVariableRow
  M cutoff liftedReplacement input output : clear implicits.

Lemma raw_sat_codedTermOpeningVariableRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    cutoff liftedReplacement input output,
  raw_formula_sat M e
    (codedTermOpeningVariableRowTermAt
      cutoff liftedReplacement input output) <->
  RawCodedTermOpeningVariableRow M
    (raw_term_eval M e cutoff)
    (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e cutoff liftedReplacement input output.
  unfold codedTermOpeningVariableRowTermAt,
    RawCodedTermOpeningVariableRow, operationAnd3.
  cbn [raw_formula_sat]. split.
  - intros [ii [hin hcases]].
    rewrite raw_sat_termVarCodeTermAt_iff in hin.
    rewrite raw_operation_eval_liftTerm_one in hin.
    cbn [raw_term_eval scons] in hin.
    exists ii. split; [exact hin |].
    destruct hcases as [hlow | hrest].
    {
      left. destruct hlow as [hlt hout]. split.
      - apply (proj1 (raw_sat_ltTermAt_iff _ _ _ _)) in hlt.
        rewrite raw_operation_eval_liftTerm_one in hlt.
        cbn [raw_term_eval scons] in hlt. exact hlt.
      - rewrite raw_sat_termVarCodeTermAt_iff in hout.
        rewrite raw_operation_eval_liftTerm_one in hout.
        cbn [raw_term_eval scons] in hout. exact hout.
    }
    destruct hrest as [heqcase | hhigh].
    {
      right. left. destruct heqcase as [heq hout]. split.
      - rewrite raw_operation_eval_liftTerm_one in heq.
        cbn [raw_term_eval scons] in heq. exact heq.
      - repeat rewrite raw_operation_eval_liftTerm_one in hout.
        cbn [raw_term_eval scons] in hout. exact hout.
    }
    right. right. destruct hhigh as [pred [heq [hlt hout]]].
    exists pred. split.
    + repeat rewrite raw_operation_eval_liftTerm_one in heq.
      cbn [raw_term_eval scons] in heq. exact heq.
    + split.
      * apply (proj1 (raw_sat_ltTermAt_iff _ _ _ _)) in hlt.
        repeat rewrite raw_operation_eval_liftTerm_one in hlt.
        cbn [raw_term_eval scons] in hlt. exact hlt.
      * rewrite raw_sat_termVarCodeTermAt_iff in hout.
        repeat rewrite raw_operation_eval_liftTerm_one in hout.
        cbn [raw_term_eval scons] in hout. exact hout.
  - intros [ii [hin hcases]]. exists ii. split.
    + rewrite raw_sat_termVarCodeTermAt_iff,
        raw_operation_eval_liftTerm_one.
      cbn [raw_term_eval scons]. exact hin.
    + destruct hcases as [hlow | hrest].
      {
        left. destruct hlow as [hlt hout]. split.
        - apply (proj2 (raw_sat_ltTermAt_iff _ _ _ _)).
          rewrite raw_operation_eval_liftTerm_one.
          cbn [raw_term_eval scons]. exact hlt.
        - rewrite raw_sat_termVarCodeTermAt_iff,
            raw_operation_eval_liftTerm_one.
          cbn [raw_term_eval scons]. exact hout.
      }
      destruct hrest as [heqcase | hhigh].
      {
        right. left. destruct heqcase as [heq hout]. split.
        - rewrite raw_operation_eval_liftTerm_one.
          cbn [raw_term_eval scons]. exact heq.
        - repeat rewrite raw_operation_eval_liftTerm_one.
          cbn [raw_term_eval scons]. exact hout.
      }
      right. right. destruct hhigh as [pred [heq [hlt hout]]].
      exists pred. split.
      * repeat rewrite raw_operation_eval_liftTerm_one.
        cbn [raw_term_eval scons]. exact heq.
      * split.
        -- apply (proj2 (raw_sat_ltTermAt_iff _ _ _ _)).
           repeat rewrite raw_operation_eval_liftTerm_one.
           cbn [raw_term_eval scons]. exact hlt.
        -- rewrite raw_sat_termVarCodeTermAt_iff.
           repeat rewrite raw_operation_eval_liftTerm_one.
           cbn [raw_term_eval scons]. exact hout.
Qed.

(** Recursive constructor rows are shared by shifting and opening. *)
Definition codedTermZeroOperationRowTermAt
    (input output : term) : formula :=
  pAnd (termZeroCodeTermAt input) (termZeroCodeTermAt output).

Definition codedTermSuccOperationRowTermAt
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  operationEx3 (operationAnd4
    (Formula.ltTermAt (tVar 2) (liftTerm 3 index))
    (codedTermOperationPairLookupTermAt
      (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
      (liftTerm 3 targetCode) (liftTerm 3 targetStep)
      (tVar 2) (tVar 1) (tVar 0))
    (termSuccCodeTermAt (liftTerm 3 input) (tVar 1))
    (termSuccCodeTermAt (liftTerm 3 output) (tVar 0))).

Definition codedTermBinaryOperationRowTermAt
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
    (constructor (liftTerm 6 output) (tVar 3) (tVar 0))).

Definition RawCodedTermZeroOperationRow (M : RawPAModel)
    (input output : M) : Prop :=
  input = rawTermZeroCode M /\ output = rawTermZeroCode M.

Definition RawCodedTermSuccOperationRow (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists childIndex inputChild outputChild : M,
    rawLt M childIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      childIndex inputChild outputChild /\
    input = rawTermSuccCode M inputChild /\
    output = rawTermSuccCode M outputChild.

Definition RawCodedTermBinaryOperationRow (M : RawPAModel)
    (constructor : M -> M -> M)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  exists leftIndex inputLeft outputLeft rightIndex inputRight outputRight : M,
    rawLt M leftIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      leftIndex inputLeft outputLeft /\
    rawLt M rightIndex index /\
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep
      rightIndex inputRight outputRight /\
    input = constructor inputLeft inputRight /\
    output = constructor outputLeft outputRight.

Lemma raw_sat_codedTermZeroOperationRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (codedTermZeroOperationRowTermAt input output) <->
  RawCodedTermZeroOperationRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermZeroOperationRowTermAt,
    RawCodedTermZeroOperationRow.
  cbn [raw_formula_sat]. rewrite !raw_sat_termZeroCodeTermAt_iff.
  reflexivity.
Qed.

Lemma raw_sat_codedTermSuccOperationRowTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep
    index input output,
  raw_formula_sat M e
    (codedTermSuccOperationRowTermAt
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermSuccOperationRow M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e sourceCode sourceStep targetCode targetStep index input output.
  unfold codedTermSuccOperationRowTermAt, operationEx3, operationAnd4,
    RawCodedTermSuccOperationRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_termSuccCodeTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_sat_codedTermBinaryOperationRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> term -> formula)
    (rawConstructor : M -> M -> M),
  (forall e' code left right,
    raw_formula_sat M e' (constructor code left right) <->
    raw_term_eval M e' code = rawConstructor
      (raw_term_eval M e' left) (raw_term_eval M e' right)) ->
  forall sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermBinaryOperationRowTermAt constructor
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermBinaryOperationRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep index input output.
  unfold codedTermBinaryOperationRowTermAt, operationEx6, operationAnd6,
    RawCodedTermBinaryOperationRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite hconstructor.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermOperationTraversalRowTermAt
    (variableRow : term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep index input output : term)
    : formula :=
  pOr (variableRow input output)
  (pOr (codedTermZeroOperationRowTermAt input output)
  (pOr (codedTermSuccOperationRowTermAt
      sourceCode sourceStep targetCode targetStep index input output)
  (pOr (codedTermBinaryOperationRowTermAt termAddCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)
    (codedTermBinaryOperationRowTermAt termMulCodeTermAt
      sourceCode sourceStep targetCode targetStep index input output)))).

Definition RawCodedTermOperationTraversalRow (M : RawPAModel)
    (variableRow : M -> M -> Prop)
    (sourceCode sourceStep targetCode targetStep index input output : M)
    : Prop :=
  variableRow input output \/
  RawCodedTermZeroOperationRow M input output \/
  RawCodedTermSuccOperationRow M
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedTermBinaryOperationRow M (rawTermAddCode M)
    sourceCode sourceStep targetCode targetStep index input output \/
  RawCodedTermBinaryOperationRow M (rawTermMulCode M)
    sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermOperationTraversalRowTermAt_iff : forall
    (M : RawPAModel) e
    (variableRow : term -> term -> formula)
    (rawVariableRow : M -> M -> Prop),
  (forall e' input output,
    raw_formula_sat M e' (variableRow input output) <->
    rawVariableRow
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall sourceCode sourceStep targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermOperationTraversalRowTermAt variableRow
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermOperationTraversalRow M rawVariableRow
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros M e variableRow rawVariableRow hvariable
    sourceCode sourceStep targetCode targetStep index input output.
  unfold codedTermOperationTraversalRowTermAt,
    RawCodedTermOperationTraversalRow.
  cbn [raw_formula_sat]. rewrite hvariable.
  rewrite raw_sat_codedTermZeroOperationRowTermAt_iff.
  rewrite raw_sat_codedTermSuccOperationRowTermAt_iff.
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termAddCodeTermAt (rawTermAddCode M)
    (raw_sat_termAddCodeTermAt_iff M)).
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termMulCodeTermAt (rawTermMulCode M)
    (raw_sat_termMulCodeTermAt_iff M)).
  reflexivity.
Qed.

(** Specializations of the generic term row. *)
Definition codedTermShiftTraversalRowTermAt
    (cutoff amount sourceCode sourceStep targetCode targetStep
      index input output : term) : formula :=
  codedTermOperationTraversalRowTermAt
    (codedTermShiftVariableRowTermAt cutoff amount)
    sourceCode sourceStep targetCode targetStep index input output.

Definition RawCodedTermShiftTraversalRow (M : RawPAModel)
    (cutoff amount sourceCode sourceStep targetCode targetStep
      index input output : M) : Prop :=
  RawCodedTermOperationTraversalRow M
    (RawCodedTermShiftVariableRow M cutoff amount)
    sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermShiftTraversalRowTermAt_iff : forall
    (M : RawPAModel) e cutoff amount sourceCode sourceStep
    targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermShiftTraversalRowTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermShiftTraversalRow M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedTermShiftTraversalRowTermAt,
    codedTermOperationTraversalRowTermAt,
    RawCodedTermShiftTraversalRow,
    RawCodedTermOperationTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedTermShiftVariableRowTermAt_iff.
  rewrite raw_sat_codedTermZeroOperationRowTermAt_iff.
  rewrite raw_sat_codedTermSuccOperationRowTermAt_iff.
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termAddCodeTermAt (rawTermAddCode M)
    (raw_sat_termAddCodeTermAt_iff M)).
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termMulCodeTermAt (rawTermMulCode M)
    (raw_sat_termMulCodeTermAt_iff M)).
  reflexivity.
Qed.

Definition codedTermOpeningTraversalRowTermAt
    (cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      index input output : term) : formula :=
  codedTermOperationTraversalRowTermAt
    (codedTermOpeningVariableRowTermAt cutoff liftedReplacement)
    sourceCode sourceStep targetCode targetStep index input output.

Definition RawCodedTermOpeningTraversalRow (M : RawPAModel)
    (cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      index input output : M) : Prop :=
  RawCodedTermOperationTraversalRow M
    (RawCodedTermOpeningVariableRow M cutoff liftedReplacement)
    sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermOpeningTraversalRowTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement sourceCode sourceStep
    targetCode targetStep index input output,
  raw_formula_sat M e
    (codedTermOpeningTraversalRowTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep index input output) <->
  RawCodedTermOpeningTraversalRow M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedTermOpeningTraversalRowTermAt,
    codedTermOperationTraversalRowTermAt,
    RawCodedTermOpeningTraversalRow,
    RawCodedTermOperationTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedTermOpeningVariableRowTermAt_iff.
  rewrite raw_sat_codedTermZeroOperationRowTermAt_iff.
  rewrite raw_sat_codedTermSuccOperationRowTermAt_iff.
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termAddCodeTermAt (rawTermAddCode M)
    (raw_sat_termAddCodeTermAt_iff M)).
  rewrite (raw_sat_codedTermBinaryOperationRowTermAt_iff M e
    termMulCodeTermAt (rawTermMulCode M)
    (raw_sat_termMulCodeTermAt_iff M)).
  reflexivity.
Qed.

(** A generic three-binder row wrapper. *)
Definition codedTermOperationRowsTermAt
    (row : term -> term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep bound : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (row (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawCodedTermOperationRows (M : RawPAModel)
    (row : M -> M -> M -> Prop)
    (sourceCode sourceStep targetCode targetStep bound : M) : Prop :=
  forall index input output : M,
    rawLt M index bound ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    row index input output.

Lemma raw_sat_codedTermOperationRowsTermAt_iff : forall
    (M : RawPAModel) e
    (row : term -> term -> term -> formula)
    (rawRow : M -> M -> M -> Prop),
  (forall e' index input output,
    raw_formula_sat M e' (row index input output) <->
    rawRow (raw_term_eval M e' index)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall sourceCode sourceStep targetCode targetStep bound,
  raw_formula_sat M e
    (codedTermOperationRowsTermAt row
      sourceCode sourceStep targetCode targetStep bound) <->
  RawCodedTermOperationRows M rawRow
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros M e row rawRow hrow
    sourceCode sourceStep targetCode targetStep bound.
  unfold codedTermOperationRowsTermAt, RawCodedTermOperationRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite hrow.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** This wrapper is written out because its traversal row also refers to
    the six parameters outside the three universal binders.  Keeping those
    lifts here makes the de Bruijn bookkeeping visible and avoids silently
    lifting the table parameters twice through a generic wrapper. *)
Definition codedTermShiftRowsTermAt
    (cutoff amount sourceCode sourceStep targetCode targetStep bound : term)
    : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedTermShiftTraversalRowTermAt
          (liftTerm 3 cutoff) (liftTerm 3 amount)
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawCodedTermShiftRows (M : RawPAModel)
    (cutoff amount sourceCode sourceStep targetCode targetStep bound : M)
    : Prop :=
  forall index input output : M,
    rawLt M index bound ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedTermShiftTraversalRow M cutoff amount
      sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermShiftRowsTermAt_iff : forall
    (M : RawPAModel) e cutoff amount sourceCode sourceStep
    targetCode targetStep bound,
  raw_formula_sat M e
    (codedTermShiftRowsTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep bound) <->
  RawCodedTermShiftRows M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold codedTermShiftRowsTermAt,
    RawCodedTermShiftRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedTermShiftTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermOpeningRowsTermAt
    (cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 2) (liftTerm 3 bound))
      (pImp
        (codedTermOperationPairLookupTermAt
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0))
        (codedTermOpeningTraversalRowTermAt
          (liftTerm 3 cutoff) (liftTerm 3 liftedReplacement)
          (liftTerm 3 sourceCode) (liftTerm 3 sourceStep)
          (liftTerm 3 targetCode) (liftTerm 3 targetStep)
          (tVar 2) (tVar 1) (tVar 0)))))).

Definition RawCodedTermOpeningRows (M : RawPAModel)
    (cutoff liftedReplacement sourceCode sourceStep
      targetCode targetStep bound : M) : Prop :=
  forall index input output : M,
    rawLt M index bound ->
    RawCodedTermOperationPairLookup M
      sourceCode sourceStep targetCode targetStep index input output ->
    RawCodedTermOpeningTraversalRow M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep index input output.

Lemma raw_sat_codedTermOpeningRowsTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement sourceCode sourceStep
    targetCode targetStep bound,
  raw_formula_sat M e
    (codedTermOpeningRowsTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound) <->
  RawCodedTermOpeningRows M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound).
Proof.
  intros. unfold codedTermOpeningRowsTermAt,
    RawCodedTermOpeningRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermShiftTraceTermAt
    (cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output : term) : formula :=
  operationAnd6
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (Formula.ltTermAt rootIndex bound)
    (codedTermOperationPairLookupTermAt
      sourceCode sourceStep targetCode targetStep rootIndex input output)
    (codedTermShiftRowsTermAt cutoff amount
      sourceCode sourceStep targetCode targetStep bound)
    (Formula.leTermAt tZero cutoff).

Definition RawCodedTermShiftTrace (M : RawPAModel)
    (cutoff amount sourceCode sourceStep targetCode targetStep
      bound rootIndex input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  rawLt M rootIndex bound /\
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output /\
  RawCodedTermShiftRows M cutoff amount
    sourceCode sourceStep targetCode targetStep bound /\
  rawLe M (raw_zero M) cutoff.

Lemma raw_sat_codedTermShiftTraceTermAt_iff : forall
    (M : RawPAModel) e cutoff amount sourceCode sourceStep
    targetCode targetStep bound rootIndex input output,
  raw_formula_sat M e
    (codedTermShiftTraceTermAt cutoff amount sourceCode sourceStep
      targetCode targetStep bound rootIndex input output) <->
  RawCodedTermShiftTrace M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermShiftTraceTermAt,
    RawCodedTermShiftTrace, operationAnd6.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  rewrite raw_sat_codedTermShiftRowsTermAt_iff.
  rewrite raw_sat_leTermAt_iff_rank. reflexivity.
Qed.

Definition codedTermOpeningTraceTermAt
    (cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input output : term) : formula :=
  operationAnd5
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (Formula.ltTermAt rootIndex bound)
    (codedTermOperationPairLookupTermAt
      sourceCode sourceStep targetCode targetStep rootIndex input output)
    (codedTermOpeningRowsTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep bound).

Definition RawCodedTermOpeningTrace (M : RawPAModel)
    (cutoff liftedReplacement sourceCode sourceStep targetCode targetStep
      bound rootIndex input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  rawLt M rootIndex bound /\
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output /\
  RawCodedTermOpeningRows M cutoff liftedReplacement
    sourceCode sourceStep targetCode targetStep bound.

Lemma raw_sat_codedTermOpeningTraceTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement sourceCode sourceStep
    targetCode targetStep bound rootIndex input output,
  raw_formula_sat M e
    (codedTermOpeningTraceTermAt cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output) <->
  RawCodedTermOpeningTrace M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermOpeningTraceTermAt,
    RawCodedTermOpeningTrace, operationAnd5.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_codedTermOperationPairLookupTermAt_iff.
  rewrite raw_sat_codedTermOpeningRowsTermAt_iff. reflexivity.
Qed.

Definition codedTermShiftTermAt
    (cutoff amount input output : term) : formula :=
  operationEx6
    (codedTermShiftTraceTermAt
      (liftTerm 6 cutoff) (liftTerm 6 amount)
      (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 6 input) (liftTerm 6 output)).

Definition RawCodedTermShift (M : RawPAModel)
    (cutoff amount input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep bound rootIndex : M,
    RawCodedTermShiftTrace M cutoff amount
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output.

Lemma raw_sat_codedTermShiftTermAt_iff : forall
    (M : RawPAModel) e cutoff amount input output,
  raw_formula_sat M e
    (codedTermShiftTermAt cutoff amount input output) <->
  RawCodedTermShift M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermShiftTermAt, operationEx6,
    RawCodedTermShift.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedTermShiftTraceTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedTermOpeningTermAt
    (cutoff liftedReplacement input output : term) : formula :=
  operationEx6
    (codedTermOpeningTraceTermAt
      (liftTerm 6 cutoff) (liftTerm 6 liftedReplacement)
      (tVar 5) (tVar 4) (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 6 input) (liftTerm 6 output)).

Definition RawCodedTermOpening (M : RawPAModel)
    (cutoff liftedReplacement input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep bound rootIndex : M,
    RawCodedTermOpeningTrace M cutoff liftedReplacement
      sourceCode sourceStep targetCode targetStep
      bound rootIndex input output.

Lemma raw_sat_codedTermOpeningTermAt_iff : forall
    (M : RawPAModel) e cutoff liftedReplacement input output,
  raw_formula_sat M e
    (codedTermOpeningTermAt cutoff liftedReplacement input output) <->
  RawCodedTermOpening M
    (raw_term_eval M e cutoff) (raw_term_eval M e liftedReplacement)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedTermOpeningTermAt, operationEx6,
    RawCodedTermOpening.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedTermOpeningTraceTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_six.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem raw_codedTermShift_same_trace_root_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output',
  RawCodedTermShiftTrace M cutoff amount
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output' ->
  output = output'.
Proof.
  intros M hPA cutoff amount sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output'
    [_ [_ [_ [[_ houtput] _]]]] [_ houtput'].
  exact (raw_codedAssignmentLookup_functional M hPA
    targetCode targetStep rootIndex output output' houtput houtput').
Qed.

Theorem raw_codedTermOpening_same_trace_root_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall cutoff replacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output',
  RawCodedTermOpeningTrace M cutoff replacement
    sourceCode sourceStep targetCode targetStep
    bound rootIndex input output ->
  RawCodedTermOperationPairLookup M
    sourceCode sourceStep targetCode targetStep rootIndex input output' ->
  output = output'.
Proof.
  intros M hPA cutoff replacement sourceCode sourceStep targetCode targetStep
    bound rootIndex input output output'
    [_ [_ [_ [[_ houtput] _]]]] [_ houtput'].
  exact (raw_codedAssignmentLookup_functional M hPA
    targetCode targetStep rootIndex output output' houtput houtput').
Qed.

(** ------------------------------------------------------------------
    Formula-operation traces.

    A third beta table stores binder depth.  Binary children retain their
    parent's depth; quantified children use its successor.  Equality atoms
    invoke an explicit term operation, so arbitrary term-code payloads are
    never transformed by fiat. *)

Definition operationAnd7 (a b c d f g h : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g h))))).

Definition operationAnd8 (a b c d f g h i : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f (pAnd g (pAnd h i)))))).

Definition codedFormulaOperationTripleLookupTermAt
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : term) : formula :=
  pAnd
    (codedAssignmentLookupTermAt sourceCode sourceStep index input)
    (pAnd
      (codedAssignmentLookupTermAt targetCode targetStep index output)
      (codedAssignmentLookupTermAt depthCode depthStep index depth)).

Definition RawCodedFormulaOperationTripleLookup (M : RawPAModel)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : M) : Prop :=
  RawCodedAssignmentLookup M sourceCode sourceStep index input /\
  RawCodedAssignmentLookup M targetCode targetStep index output /\
  RawCodedAssignmentLookup M depthCode depthStep index depth.

Arguments RawCodedFormulaOperationTripleLookup
  M sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth : clear implicits.

Lemma raw_sat_codedFormulaOperationTripleLookupTermAt_iff : forall
    (M : RawPAModel) e sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth,
  raw_formula_sat M e
    (codedFormulaOperationTripleLookupTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth) <->
  RawCodedFormulaOperationTripleLookup M
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output) (raw_term_eval M e depth).
Proof.
  intros. unfold codedFormulaOperationTripleLookupTermAt,
    RawCodedFormulaOperationTripleLookup.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff. reflexivity.
Qed.

Definition codedFormulaEqOperationRowTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter depth input output : term) : formula :=
  operationEx4 (operationAnd4
    (formulaEqCodeTermAt (liftTerm 4 input) (tVar 3) (tVar 1))
    (formulaEqCodeTermAt (liftTerm 4 output) (tVar 2) (tVar 0))
    (atom (liftTerm 4 parameter) (liftTerm 4 depth)
      (tVar 3) (tVar 2))
    (atom (liftTerm 4 parameter) (liftTerm 4 depth)
      (tVar 1) (tVar 0))).

Definition RawCodedFormulaEqOperationRow (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter depth input output : M) : Prop :=
  exists inputLeft outputLeft inputRight outputRight : M,
    input = rawFormulaEqCode M inputLeft inputRight /\
    output = rawFormulaEqCode M outputLeft outputRight /\
    atom parameter depth inputLeft outputLeft /\
    atom parameter depth inputRight outputRight.

Lemma raw_sat_codedFormulaEqOperationRowTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall parameter depth input output,
  raw_formula_sat M e
    (codedFormulaEqOperationRowTermAt atom parameter depth input output) <->
  RawCodedFormulaEqOperationRow M rawAtom
    (raw_term_eval M e parameter) (raw_term_eval M e depth)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e atom rawAtom hatom parameter depth input output.
  unfold codedFormulaEqOperationRowTermAt, operationEx4, operationAnd4,
    RawCodedFormulaEqOperationRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_formulaEqCodeTermAt_iff.
  setoid_rewrite hatom.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaBotOperationRowTermAt
    (input output : term) : formula :=
  pAnd (formulaBotCodeTermAt input) (formulaBotCodeTermAt output).

Definition RawCodedFormulaBotOperationRow (M : RawPAModel)
    (input output : M) : Prop :=
  input = rawFormulaBotCode M /\ output = rawFormulaBotCode M.

Lemma raw_sat_codedFormulaBotOperationRowTermAt_iff : forall
    (M : RawPAModel) e input output,
  raw_formula_sat M e
    (codedFormulaBotOperationRowTermAt input output) <->
  RawCodedFormulaBotOperationRow M
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaBotOperationRowTermAt,
    RawCodedFormulaBotOperationRow.
  cbn [raw_formula_sat]. rewrite !raw_sat_formulaBotCodeTermAt_iff.
  reflexivity.
Qed.

Definition codedFormulaBinaryOperationRowTermAt
    (constructor : term -> term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : term) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx
    (operationAnd8
      (Formula.ltTermAt (tVar 7) (liftTerm 8 index))
      (codedFormulaOperationTripleLookupTermAt
        (liftTerm 8 sourceCode) (liftTerm 8 sourceStep)
        (liftTerm 8 targetCode) (liftTerm 8 targetStep)
        (liftTerm 8 depthCode) (liftTerm 8 depthStep)
        (tVar 7) (tVar 6) (tVar 5) (tVar 4))
      (pEq (tVar 4) (liftTerm 8 depth))
      (Formula.ltTermAt (tVar 3) (liftTerm 8 index))
      (codedFormulaOperationTripleLookupTermAt
        (liftTerm 8 sourceCode) (liftTerm 8 sourceStep)
        (liftTerm 8 targetCode) (liftTerm 8 targetStep)
        (liftTerm 8 depthCode) (liftTerm 8 depthStep)
        (tVar 3) (tVar 2) (tVar 1) (tVar 0))
      (pEq (tVar 0) (liftTerm 8 depth))
      (constructor (liftTerm 8 input) (tVar 6) (tVar 2))
      (constructor (liftTerm 8 output) (tVar 5) (tVar 1)))))))))).

Definition RawCodedFormulaBinaryOperationRow (M : RawPAModel)
    (constructor : M -> M -> M)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : M) : Prop :=
  exists leftIndex inputLeft outputLeft leftDepth
    rightIndex inputRight outputRight rightDepth : M,
    rawLt M leftIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      leftIndex inputLeft outputLeft leftDepth /\
    leftDepth = depth /\
    rawLt M rightIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rightIndex inputRight outputRight rightDepth /\
    rightDepth = depth /\
    input = constructor inputLeft inputRight /\
    output = constructor outputLeft outputRight.

Lemma raw_sat_codedFormulaBinaryOperationRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> term -> formula)
    (rawConstructor : M -> M -> M),
  (forall e' code left right,
    raw_formula_sat M e' (constructor code left right) <->
    raw_term_eval M e' code = rawConstructor
      (raw_term_eval M e' left) (raw_term_eval M e' right)) ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth,
  raw_formula_sat M e
    (codedFormulaBinaryOperationRowTermAt constructor
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth) <->
  RawCodedFormulaBinaryOperationRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output) (raw_term_eval M e depth).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth.
  unfold codedFormulaBinaryOperationRowTermAt, operationAnd8,
    RawCodedFormulaBinaryOperationRow.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite hconstructor.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_eight.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaUnaryOperationRowTermAt
    (constructor : term -> term -> formula)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : term) : formula :=
  operationEx4 (operationAnd5
    (Formula.ltTermAt (tVar 3) (liftTerm 4 index))
    (codedFormulaOperationTripleLookupTermAt
      (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
      (liftTerm 4 targetCode) (liftTerm 4 targetStep)
      (liftTerm 4 depthCode) (liftTerm 4 depthStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (pEq (tVar 0) (tSucc (liftTerm 4 depth)))
    (constructor (liftTerm 4 input) (tVar 2))
    (constructor (liftTerm 4 output) (tVar 1))).

Definition RawCodedFormulaUnaryOperationRow (M : RawPAModel)
    (constructor : M -> M)
    (sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : M) : Prop :=
  exists childIndex inputChild outputChild childDepth : M,
    rawLt M childIndex index /\
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      childIndex inputChild outputChild childDepth /\
    childDepth = raw_succ M depth /\
    input = constructor inputChild /\
    output = constructor outputChild.

Lemma raw_sat_codedFormulaUnaryOperationRowTermAt_iff : forall
    (M : RawPAModel) e
    (constructor : term -> term -> formula)
    (rawConstructor : M -> M),
  (forall e' code child,
    raw_formula_sat M e' (constructor code child) <->
    raw_term_eval M e' code = rawConstructor (raw_term_eval M e' child)) ->
  forall sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth,
  raw_formula_sat M e
    (codedFormulaUnaryOperationRowTermAt constructor
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth) <->
  RawCodedFormulaUnaryOperationRow M rawConstructor
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output) (raw_term_eval M e depth).
Proof.
  intros M e constructor rawConstructor hconstructor
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth.
  unfold codedFormulaUnaryOperationRowTermAt, operationEx4, operationAnd5,
    RawCodedFormulaUnaryOperationRow.
  cbn [raw_formula_sat]. split.
  - intros (ci & inputChild & outputChild & childDepth &
      hlt & hlookup & hdepth & hinput & houtput).
    exists ci, inputChild, outputChild, childDepth.
    split.
    + apply (proj1 (raw_sat_ltTermAt_iff _ _ _ _)) in hlt.
      rewrite raw_rankTraversal_eval_liftTerm_four in hlt.
      cbn [raw_term_eval scons] in hlt. exact hlt.
    + split.
      * rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff
          in hlookup.
        repeat rewrite raw_rankTraversal_eval_liftTerm_four in hlookup.
        cbn [raw_term_eval scons] in hlookup. exact hlookup.
      * split.
        -- cbn [raw_term_eval scons] in hdepth.
           etransitivity; [exact hdepth |].
           f_equal. apply raw_rankTraversal_eval_liftTerm_four.
        -- split.
           ++ apply (proj1 (hconstructor _ _ _)) in hinput.
              rewrite raw_rankTraversal_eval_liftTerm_four in hinput.
              cbn [raw_term_eval scons] in hinput. exact hinput.
           ++ apply (proj1 (hconstructor _ _ _)) in houtput.
              rewrite raw_rankTraversal_eval_liftTerm_four in houtput.
              cbn [raw_term_eval scons] in houtput. exact houtput.
  - intros (ci & inputChild & outputChild & childDepth &
      hlt & hlookup & hdepth & hinput & houtput).
    exists ci, inputChild, outputChild, childDepth.
    split.
    + apply (proj2 (raw_sat_ltTermAt_iff _ _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hlt.
    + split.
      * rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
        repeat rewrite raw_rankTraversal_eval_liftTerm_four.
        cbn [raw_term_eval scons]. exact hlookup.
      * split.
        -- cbn [raw_term_eval scons].
           etransitivity; [exact hdepth |].
           f_equal. symmetry. apply raw_rankTraversal_eval_liftTerm_four.
        -- split.
           ++ apply (proj2 (hconstructor _ _ _)).
              rewrite raw_rankTraversal_eval_liftTerm_four.
              cbn [raw_term_eval scons]. exact hinput.
           ++ apply (proj2 (hconstructor _ _ _)).
              rewrite raw_rankTraversal_eval_liftTerm_four.
              cbn [raw_term_eval scons]. exact houtput.
Qed.

Definition codedFormulaOperationTraversalRowTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : term) : formula :=
  pOr (codedFormulaEqOperationRowTermAt atom parameter depth input output)
  (pOr (codedFormulaBotOperationRowTermAt input output)
  (pOr (codedFormulaBinaryOperationRowTermAt formulaImpCodeTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth)
  (pOr (codedFormulaBinaryOperationRowTermAt formulaAndCodeTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth)
  (pOr (codedFormulaBinaryOperationRowTermAt formulaOrCodeTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth)
  (pOr (codedFormulaUnaryOperationRowTermAt formulaAllCodeTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth)
    (codedFormulaUnaryOperationRowTermAt formulaExCodeTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth)))))).

Definition RawCodedFormulaOperationTraversalRow (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth : M) : Prop :=
  RawCodedFormulaEqOperationRow M atom parameter depth input output \/
  RawCodedFormulaBotOperationRow M input output \/
  RawCodedFormulaBinaryOperationRow M (rawFormulaImpCode M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth \/
  RawCodedFormulaBinaryOperationRow M (rawFormulaAndCode M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth \/
  RawCodedFormulaBinaryOperationRow M (rawFormulaOrCode M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth \/
  RawCodedFormulaUnaryOperationRow M (rawFormulaAllCode M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth \/
  RawCodedFormulaUnaryOperationRow M (rawFormulaExCode M)
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    index input output depth.

Lemma raw_sat_codedFormulaOperationTraversalRowTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep index input output depth,
  raw_formula_sat M e
    (codedFormulaOperationTraversalRowTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth) <->
  RawCodedFormulaOperationTraversalRow M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e index) (raw_term_eval M e input)
    (raw_term_eval M e output) (raw_term_eval M e depth).
Proof.
  intros M e atom rawAtom hatom parameter sourceCode sourceStep
    targetCode targetStep depthCode depthStep index input output depth.
  unfold codedFormulaOperationTraversalRowTermAt,
    RawCodedFormulaOperationTraversalRow.
  cbn [raw_formula_sat].
  rewrite (raw_sat_codedFormulaEqOperationRowTermAt_iff
    M e atom rawAtom hatom).
  rewrite raw_sat_codedFormulaBotOperationRowTermAt_iff.
  rewrite (raw_sat_codedFormulaBinaryOperationRowTermAt_iff M e
    formulaImpCodeTermAt (rawFormulaImpCode M)
    (raw_sat_formulaImpCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBinaryOperationRowTermAt_iff M e
    formulaAndCodeTermAt (rawFormulaAndCode M)
    (raw_sat_formulaAndCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBinaryOperationRowTermAt_iff M e
    formulaOrCodeTermAt (rawFormulaOrCode M)
    (raw_sat_formulaOrCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaUnaryOperationRowTermAt_iff M e
    formulaAllCodeTermAt (rawFormulaAllCode M)
    (raw_sat_formulaAllCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaUnaryOperationRowTermAt_iff M e
    formulaExCodeTermAt (rawFormulaExCode M)
    (raw_sat_formulaExCodeTermAt_iff M)).
  reflexivity.
Qed.

(** Atomic specializations. *)
Definition codedFormulaShiftAtomTermAt
    (amount depth input output : term) : formula :=
  codedTermShiftTermAt depth amount input output.

Definition RawCodedFormulaShiftAtom (M : RawPAModel)
    (amount depth input output : M) : Prop :=
  RawCodedTermShift M depth amount input output.

Lemma raw_sat_codedFormulaShiftAtomTermAt_iff : forall
    (M : RawPAModel) e amount depth input output,
  raw_formula_sat M e
    (codedFormulaShiftAtomTermAt amount depth input output) <->
  RawCodedFormulaShiftAtom M
    (raw_term_eval M e amount) (raw_term_eval M e depth)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof. intros. apply raw_sat_codedTermShiftTermAt_iff. Qed.

Definition codedFormulaSubstitutionAtomTermAt
    (replacement depth input output : term) : formula :=
  pEx (pAnd
    (codedTermShiftTermAt tZero (liftTerm 1 depth)
      (liftTerm 1 replacement) (tVar 0))
    (codedTermOpeningTermAt (liftTerm 1 depth) (tVar 0)
      (liftTerm 1 input) (liftTerm 1 output))).

Definition RawCodedFormulaSubstitutionAtom (M : RawPAModel)
    (replacement depth input output : M) : Prop :=
  exists liftedReplacement : M,
    RawCodedTermShift M (raw_zero M) depth
      replacement liftedReplacement /\
    RawCodedTermOpening M depth liftedReplacement input output.

Lemma raw_sat_codedFormulaSubstitutionAtomTermAt_iff : forall
    (M : RawPAModel) e replacement depth input output,
  raw_formula_sat M e
    (codedFormulaSubstitutionAtomTermAt replacement depth input output) <->
  RawCodedFormulaSubstitutionAtom M
    (raw_term_eval M e replacement) (raw_term_eval M e depth)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaSubstitutionAtomTermAt,
    RawCodedFormulaSubstitutionAtom.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedTermShiftTermAt_iff.
  setoid_rewrite raw_sat_codedTermOpeningTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition operationEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

Definition codedFormulaOperationRowsTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound : term) : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 bound))
      (pImp
        (codedFormulaOperationTripleLookupTermAt
          (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
          (liftTerm 4 targetCode) (liftTerm 4 targetStep)
          (liftTerm 4 depthCode) (liftTerm 4 depthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaOperationTraversalRowTermAt atom
          (liftTerm 4 parameter)
          (liftTerm 4 sourceCode) (liftTerm 4 sourceStep)
          (liftTerm 4 targetCode) (liftTerm 4 targetStep)
          (liftTerm 4 depthCode) (liftTerm 4 depthStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))))))).

Definition RawCodedFormulaOperationRows (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound : M) : Prop :=
  forall index input output depth : M,
    rawLt M index bound ->
    RawCodedFormulaOperationTripleLookup M
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth ->
    RawCodedFormulaOperationTraversalRow M atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      index input output depth.

Lemma raw_sat_codedFormulaOperationRowsTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall parameter sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound,
  raw_formula_sat M e
    (codedFormulaOperationRowsTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep bound) <->
  RawCodedFormulaOperationRows M rawAtom
    (raw_term_eval M e parameter)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound).
Proof.
  intros M e atom rawAtom hatom parameter sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound.
  unfold codedFormulaOperationRowsTermAt, RawCodedFormulaOperationRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  setoid_rewrite (raw_sat_codedFormulaOperationTraversalRowTermAt_iff
    M _ atom rawAtom hatom).
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaOperationTraceTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex input output : term) : formula :=
  operationAnd6
    (codedAssignmentDefinedThroughTermAt sourceCode sourceStep bound)
    (codedAssignmentDefinedThroughTermAt targetCode targetStep bound)
    (codedAssignmentDefinedThroughTermAt depthCode depthStep bound)
    (Formula.ltTermAt rootIndex bound)
    (codedFormulaOperationTripleLookupTermAt
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      rootIndex input output rootDepth)
    (codedFormulaOperationRowsTermAt atom parameter
      sourceCode sourceStep targetCode targetStep depthCode depthStep bound).

Definition RawCodedFormulaOperationTrace (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter rootDepth sourceCode sourceStep targetCode targetStep
      depthCode depthStep bound rootIndex input output : M) : Prop :=
  RawCodedAssignmentDefinedThrough M sourceCode sourceStep bound /\
  RawCodedAssignmentDefinedThrough M targetCode targetStep bound /\
  RawCodedAssignmentDefinedThrough M depthCode depthStep bound /\
  rawLt M rootIndex bound /\
  RawCodedFormulaOperationTripleLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    rootIndex input output rootDepth /\
  RawCodedFormulaOperationRows M atom parameter
    sourceCode sourceStep targetCode targetStep depthCode depthStep bound.

Lemma raw_sat_codedFormulaOperationTraceTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall parameter rootDepth sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex input output,
  raw_formula_sat M e
    (codedFormulaOperationTraceTermAt atom parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output) <->
  RawCodedFormulaOperationTrace M rawAtom
    (raw_term_eval M e parameter) (raw_term_eval M e rootDepth)
    (raw_term_eval M e sourceCode) (raw_term_eval M e sourceStep)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e depthCode) (raw_term_eval M e depthStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e atom rawAtom hatom parameter rootDepth sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound rootIndex input output.
  unfold codedFormulaOperationTraceTermAt,
    RawCodedFormulaOperationTrace, operationAnd6.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_codedFormulaOperationTripleLookupTermAt_iff.
  rewrite (raw_sat_codedFormulaOperationRowsTermAt_iff
    M e atom rawAtom hatom).
  reflexivity.
Qed.

Lemma raw_operation_eval_liftTerm_eight : forall (M : RawPAModel)
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

Definition codedFormulaOperationTermAt
    (atom : term -> term -> term -> term -> formula)
    (parameter rootDepth input output : term) : formula :=
  operationEx8
    (codedFormulaOperationTraceTermAt atom
      (liftTerm 8 parameter) (liftTerm 8 rootDepth)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 8 input) (liftTerm 8 output)).

Definition RawCodedFormulaOperation (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop)
    (parameter rootDepth input output : M) : Prop :=
  exists sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex : M,
    RawCodedFormulaOperationTrace M atom parameter rootDepth
      sourceCode sourceStep targetCode targetStep depthCode depthStep
      bound rootIndex input output.

Lemma raw_sat_codedFormulaOperationTermAt_iff : forall
    (M : RawPAModel) e
    (atom : term -> term -> term -> term -> formula)
    (rawAtom : M -> M -> M -> M -> Prop),
  (forall e' parameter depth input output,
    raw_formula_sat M e' (atom parameter depth input output) <->
    rawAtom (raw_term_eval M e' parameter) (raw_term_eval M e' depth)
      (raw_term_eval M e' input) (raw_term_eval M e' output)) ->
  forall parameter rootDepth input output,
  raw_formula_sat M e
    (codedFormulaOperationTermAt atom parameter rootDepth input output) <->
  RawCodedFormulaOperation M rawAtom
    (raw_term_eval M e parameter) (raw_term_eval M e rootDepth)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros M e atom rawAtom hatom parameter rootDepth input output.
  unfold codedFormulaOperationTermAt, operationEx8,
    RawCodedFormulaOperation.
  cbn [raw_formula_sat].
  setoid_rewrite (raw_sat_codedFormulaOperationTraceTermAt_iff
    M _ atom rawAtom hatom).
  repeat setoid_rewrite raw_operation_eval_liftTerm_eight.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaShiftTermAt
    (cutoff amount input output : term) : formula :=
  codedFormulaOperationTermAt codedFormulaShiftAtomTermAt
    amount cutoff input output.

Definition RawCodedFormulaShift (M : RawPAModel)
    (cutoff amount input output : M) : Prop :=
  RawCodedFormulaOperation M (RawCodedFormulaShiftAtom M)
    amount cutoff input output.

Lemma raw_sat_codedFormulaShiftTermAt_iff : forall
    (M : RawPAModel) e cutoff amount input output,
  raw_formula_sat M e
    (codedFormulaShiftTermAt cutoff amount input output) <->
  RawCodedFormulaShift M
    (raw_term_eval M e cutoff) (raw_term_eval M e amount)
    (raw_term_eval M e input) (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaShiftTermAt, RawCodedFormulaShift.
  apply (raw_sat_codedFormulaOperationTermAt_iff
    M e codedFormulaShiftAtomTermAt (RawCodedFormulaShiftAtom M)).
  exact (raw_sat_codedFormulaShiftAtomTermAt_iff M).
Qed.

Definition codedFormulaSingleSubstitutionTermAt
    (replacement input output : term) : formula :=
  codedFormulaOperationTermAt codedFormulaSubstitutionAtomTermAt
    replacement tZero input output.

Definition RawCodedFormulaSingleSubstitution (M : RawPAModel)
    (replacement input output : M) : Prop :=
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    replacement (raw_zero M) input output.

Lemma raw_sat_codedFormulaSingleSubstitutionTermAt_iff : forall
    (M : RawPAModel) e replacement input output,
  raw_formula_sat M e
    (codedFormulaSingleSubstitutionTermAt replacement input output) <->
  RawCodedFormulaSingleSubstitution M
    (raw_term_eval M e replacement) (raw_term_eval M e input)
    (raw_term_eval M e output).
Proof.
  intros. unfold codedFormulaSingleSubstitutionTermAt,
    RawCodedFormulaSingleSubstitution.
  rewrite (raw_sat_codedFormulaOperationTermAt_iff M e
    codedFormulaSubstitutionAtomTermAt
    (RawCodedFormulaSubstitutionAtom M)
    (raw_sat_codedFormulaSubstitutionAtomTermAt_iff M)).
  reflexivity.
Qed.

Theorem raw_codedFormulaOperation_same_trace_root_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall atom parameter rootDepth sourceCode sourceStep targetCode targetStep
    depthCode depthStep bound rootIndex input output output',
  RawCodedFormulaOperationTrace M atom parameter rootDepth
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    bound rootIndex input output ->
  RawCodedFormulaOperationTripleLookup M
    sourceCode sourceStep targetCode targetStep depthCode depthStep
    rootIndex input output' rootDepth ->
  output = output'.
Proof.
  intros M hPA atom parameter rootDepth sourceCode sourceStep
    targetCode targetStep depthCode depthStep bound rootIndex
    input output output' htrace hlookup.
  destruct htrace as [_ [_ [_ [_ [hroot _]]]]].
  destruct hroot as [_ [houtput _]].
  destruct hlookup as [_ [houtput' _]].
  exact (raw_codedAssignmentLookup_functional M hPA
    targetCode targetStep rootIndex output output' houtput houtput').
Qed.

(** Negation exchanges the positive and negative hierarchy ranks.  The
    theorem is conditional only on the two ordinary rank certificates; rank
    totality for well-formed codes supplies those certificates separately. *)
Theorem raw_codedFormulaNegation_rank_switch : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall input output sigma pi outputSigma outputPi,
  RawCodedFormulaNegation M input output ->
  RawCodedFormulaRank M input sigma pi ->
  RawCodedFormulaRank M output outputSigma outputPi ->
  outputSigma = pi /\ outputPi = sigma.
Proof.
  intros M hPA input output sigma pi outputSigma outputPi
    hneg hinputRank
    (formulaCode & formulaStep & sigmaCode & sigmaStep & piCode & piStep &
      bound & rootIndex & htraversal).
  pose proof (raw_codedFormulaRankTraversal_root_row M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex output outputSigma outputPi htraversal) as hrow.
  apply raw_codedFormulaRankTraversalRow_shape_iff in hrow.
  destruct hrow as [shape [hshapeCode hshapeRank]].
  assert (hshape : shape =
      rawShapeImp input (rawFormulaBotCode M)).
  {
    apply (rawCodedFormulaShapeCode_injective
      polynomialPairInjectivityProof M hPA).
    cbn [rawCodedFormulaShapeCode].
    exact (eq_trans (eq_sym hshapeCode) hneg).
  }
  subst shape.
  cbn [RawCodedFormulaShapeRankRow] in hshapeRank.
  destruct hshapeRank as
    (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
      hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
  pose proof (raw_rank_child_certificate M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex output outputSigma outputPi htraversal
    leftIndex input leftSigma leftPi hleftIndex hleftLookup)
    as hleftRank.
  pose proof (raw_rank_child_certificate M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex output outputSigma outputPi htraversal
    rightIndex (rawFormulaBotCode M) rightSigma rightPi
    hrightIndex hrightLookup) as hrightRank.
  destruct (raw_codedFormulaRank_functional M hPA
    input leftSigma leftPi sigma pi hleftRank hinputRank)
    as [hleftSigma hleftPi].
  change (RawCodedFormulaRank M
    (rawQuotedFormulaCode M pBot) rightSigma rightPi) in hrightRank.
  destruct (raw_codedFormulaRank_standard_sound
    polynomialPairInjectivityProof M hPA pBot rightSigma rightPi hrightRank)
    as [hrightSigma hrightPi].
  cbn [sigmaRank piRank] in hrightSigma, hrightPi.
  subst leftSigma. subst leftPi. subst rightSigma. subst rightPi.
  destruct hrank as [houtputSigma houtputPi].
  split.
  - exact (raw_max_relation_functional M hPA
      outputSigma pi pi (raw_zero M) houtputSigma
      (or_intror (conj (raw_rank_zero_le M hPA pi) eq_refl))).
  - exact (raw_max_relation_functional M hPA
      outputPi sigma sigma (raw_zero M) houtputPi
      (or_intror (conj (raw_rank_zero_le M hPA sigma) eq_refl))).
Qed.

(** These named properties are the exact remaining cross-trace rank seam
    for arbitrary nonstandard operations.  They introduce no axiom: clients
    that need rank preservation can state precisely which operation premise
    they have established.  Same-trace output functionality above is
    unconditional. *)
Definition RawCodedFormulaOperationRankPreserving (M : RawPAModel)
    (atom : M -> M -> M -> M -> Prop) : Prop :=
  forall parameter rootDepth input output sigma pi outputSigma outputPi : M,
    RawCodedFormulaOperation M atom parameter rootDepth input output ->
    RawCodedFormulaRank M input sigma pi ->
    RawCodedFormulaRank M output outputSigma outputPi ->
    outputSigma = sigma /\ outputPi = pi.

Definition RawCodedFormulaShiftRankPreserving (M : RawPAModel) : Prop :=
  forall cutoff amount input output sigma pi outputSigma outputPi : M,
    RawCodedFormulaShift M cutoff amount input output ->
    RawCodedFormulaRank M input sigma pi ->
    RawCodedFormulaRank M output outputSigma outputPi ->
    outputSigma = sigma /\ outputPi = pi.

Definition RawCodedFormulaSingleSubstitutionRankPreserving
    (M : RawPAModel) : Prop :=
  forall replacement input output sigma pi outputSigma outputPi : M,
    RawCodedFormulaSingleSubstitution M replacement input output ->
    RawCodedFormulaRank M input sigma pi ->
    RawCodedFormulaRank M output outputSigma outputPi ->
    outputSigma = sigma /\ outputPi = pi.

Lemma raw_codedFormulaShift_rank_preserving_of_generic : forall
    (M : RawPAModel),
  RawCodedFormulaOperationRankPreserving M
    (RawCodedFormulaShiftAtom M) ->
  RawCodedFormulaShiftRankPreserving M.
Proof.
  intros M h. unfold RawCodedFormulaShiftRankPreserving,
    RawCodedFormulaShift.
  intros cutoff amount input output sigma pi outputSigma outputPi.
  exact (h amount cutoff input output sigma pi outputSigma outputPi).
Qed.

Lemma raw_codedFormulaSingleSubstitution_rank_preserving_of_generic : forall
    (M : RawPAModel),
  RawCodedFormulaOperationRankPreserving M
    (RawCodedFormulaSubstitutionAtom M) ->
  RawCodedFormulaSingleSubstitutionRankPreserving M.
Proof.
  intros M h. unfold RawCodedFormulaSingleSubstitutionRankPreserving,
    RawCodedFormulaSingleSubstitution.
  intros replacement input output sigma pi outputSigma outputPi.
  exact (h replacement (raw_zero M) input output
    sigma pi outputSigma outputPi).
Qed.

(** Functionality of iterated universal closure is not a meta-level
    induction over the carrier.  The invariant below is itself a PA formula,
    so [raw_definable_induction] applies also to nonstandard PA models. *)
Definition codedUniversalClosureFunctionalAtTermAt
    (count : term) : formula :=
  pAll (pAll (pAll
    (pImp
      (codedUniversalClosureTermAt
        (liftTerm 3 count) (tVar 2) (tVar 1))
      (pImp
        (codedUniversalClosureTermAt
          (liftTerm 3 count) (tVar 2) (tVar 0))
        (pEq (tVar 1) (tVar 0)))))).

Definition RawCodedUniversalClosureFunctionalAt (M : RawPAModel)
    (count : M) : Prop :=
  forall input output output' : M,
    RawCodedUniversalClosure M count input output ->
    RawCodedUniversalClosure M count input output' ->
    output = output'.

Lemma raw_sat_codedUniversalClosureFunctionalAtTermAt_iff : forall
    (M : RawPAModel) e count,
  raw_formula_sat M e
    (codedUniversalClosureFunctionalAtTermAt count) <->
  RawCodedUniversalClosureFunctionalAt M (raw_term_eval M e count).
Proof.
  intros. unfold codedUniversalClosureFunctionalAtTermAt,
    RawCodedUniversalClosureFunctionalAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedUniversalClosureTermAt_iff.
  repeat setoid_rewrite raw_operation_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_codedUniversalClosure_functional_zero : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedUniversalClosureFunctionalAt M (raw_zero M).
Proof.
  intros M hPA input output output' houtput houtput'.
  transitivity input.
  - exact (raw_codedUniversalClosure_zero M hPA input output houtput).
  - symmetry.
    exact (raw_codedUniversalClosure_zero M hPA input output' houtput').
Qed.

Lemma raw_codedUniversalClosure_functional_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall count,
  RawCodedUniversalClosureFunctionalAt M count ->
  RawCodedUniversalClosureFunctionalAt M (raw_succ M count).
Proof.
  intros M hPA count hcurrent input output output' houtput houtput'.
  destruct (raw_codedUniversalClosure_succ_inversion
    M hPA count input output houtput) as [previous [hprevious ->]].
  destruct (raw_codedUniversalClosure_succ_inversion
    M hPA count input output' houtput') as [previous' [hprevious' ->]].
  f_equal. exact (hcurrent input previous previous' hprevious hprevious').
Qed.

Theorem raw_codedUniversalClosure_functional_at_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall count,
  RawCodedUniversalClosureFunctionalAt M count.
Proof.
  intros M hPA.
  set (parameterEnv := fun _ : nat => raw_zero M).
  set (phi := codedUniversalClosureFunctionalAtTermAt (tVar 0)).
  assert (hall : forall count,
      raw_formula_sat M (scons M count parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedUniversalClosureFunctionalAtTermAt_iff
        M (scons M (raw_zero M) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons].
      exact (raw_codedUniversalClosure_functional_zero M hPA).
    - intros count hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedUniversalClosureFunctionalAtTermAt_iff
          M (scons M count parameterEnv) (tVar 0)) hcurrentSat)
        as hcurrent.
      apply (proj2
        (raw_sat_codedUniversalClosureFunctionalAtTermAt_iff
          M (scons M (raw_succ M count) parameterEnv) (tVar 0))).
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedUniversalClosure_functional_succ
        M hPA count hcurrent).
  }
  intro count. unfold phi in hall.
  apply (proj1
    (raw_sat_codedUniversalClosureFunctionalAtTermAt_iff
      M (scons M count parameterEnv) (tVar 0))).
  exact (hall count).
Qed.

Corollary raw_codedUniversalClosure_functional : forall
    (M : RawPAModel), RawPASatisfies M -> forall count input output output',
  RawCodedUniversalClosure M count input output ->
  RawCodedUniversalClosure M count input output' ->
  output = output'.
Proof.
  intros M hPA count.
  exact (raw_codedUniversalClosure_functional_at_all M hPA count).
Qed.

Definition codedUniversalClosureFunctionalFormula : formula :=
  pAll (codedUniversalClosureFunctionalAtTermAt (tVar 0)).

Lemma raw_sat_codedUniversalClosureFunctionalFormula_iff : forall
    (M : RawPAModel) e,
  raw_formula_sat M e codedUniversalClosureFunctionalFormula <->
  forall count : M, RawCodedUniversalClosureFunctionalAt M count.
Proof.
  intros. unfold codedUniversalClosureFunctionalFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedUniversalClosureFunctionalAtTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedUniversalClosureFunctionalFormula_sentence :
  Formula.Sentence codedUniversalClosureFunctionalFormula.
Proof.
  intros k hfree. unfold codedUniversalClosureFunctionalFormula,
    codedUniversalClosureFunctionalAtTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedUniversalClosureFunctionalFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedUniversalClosureFunctionalFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_codedUniversalClosureFunctionalFormula_iff M e)).
  exact (raw_codedUniversalClosure_functional_at_all M hPA).
Qed.

Theorem PA_proves_codedUniversalClosureFunctionalFormula :
  Formula.BProv Formula.Ax_s []
    codedUniversalClosureFunctionalFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedUniversalClosureFunctionalFormula_sentence.
  - exact codedUniversalClosureFunctionalFormula_raw_valid.
Qed.


End PABoundedRawCodedFormulaOperations.
