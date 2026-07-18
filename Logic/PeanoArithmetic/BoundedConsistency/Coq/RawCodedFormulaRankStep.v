(**
  One-step raw semantics for coded formula well-formedness and hierarchy rank.

  This is the local transition layer for a future beta-traced traversal of a
  possibly nonstandard formula code.  Each row simultaneously checks the
  transparent polynomial constructor equation and computes the constructor's
  sigma/pi rank pair from already-certified child ranks.  No selected graph
  formula and no external recursion over a model element is used here.

  The next layer can order such rows by decreasing child code, store them in
  beta sequences, and use [raw_definable_induction] to certify every row.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors.

Import ListNotations.

Module PABoundedRawCodedFormulaRankStep.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.

(** ------------------------------------------------------------------
    A transparent maximum relation. *)

Definition maxTermAt (out left right : term) : formula :=
  pOr
    (pAnd (Formula.leTermAt left right) (pEq out right))
    (pAnd (Formula.leTermAt right left) (pEq out left)).

Definition RawMax (M : RawPAModel) (out left right : M) : Prop :=
  (rawLe M left right /\ out = right) \/
  (rawLe M right left /\ out = left).

Arguments RawMax M out left right : clear implicits.

Lemma raw_sat_leTermAt_iff_rank : forall (M : RawPAModel)
    (a b : term) (e : nat -> M),
  raw_formula_sat M e (Formula.leTermAt a b) <->
  rawLe M (raw_term_eval M e a) (raw_term_eval M e b).
Proof.
  intros M a b e.
  unfold Formula.leTermAt, rawLe.
  cbn [raw_formula_sat raw_term_eval].
  split.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [d h]. exists d.
    repeat rewrite raw_term_eval_rename_succ.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_maxTermAt_iff : forall (M : RawPAModel) e out left right,
  raw_formula_sat M e (maxTermAt out left right) <->
  RawMax M (raw_term_eval M e out)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros M e out left right.
  unfold maxTermAt, RawMax. cbn [raw_formula_sat].
  rewrite !raw_sat_leTermAt_iff_rank. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Rank equations for the seven formula constructors. *)

Definition formulaRankZeroTermAt (sigma pi : term) : formula :=
  pAnd (pEq sigma tZero) (pEq pi tZero).

Definition formulaRankImpTermAt
    (sigma pi leftSigma leftPi rightSigma rightPi : term) : formula :=
  pAnd
    (maxTermAt sigma leftPi rightSigma)
    (maxTermAt pi leftSigma rightPi).

Definition formulaRankAndOrTermAt
    (sigma pi leftSigma leftPi rightSigma rightPi : term) : formula :=
  pAnd
    (maxTermAt sigma leftSigma rightSigma)
    (maxTermAt pi leftPi rightPi).

(** Under the existential, variable zero is the shared [max 1 childPi]
    value and every caller-supplied term is shifted past it. *)
Definition formulaRankAllTermAt
    (sigma pi childSigma childPi : term) : formula :=
  pEx (pAnd3
    (maxTermAt (tVar 0) (Term.numeral 1) (liftTerm 1 childPi))
    (pEq (liftTerm 1 pi) (tVar 0))
    (pEq (liftTerm 1 sigma) (tSucc (tVar 0)))).

(** Dually, existential rank uses [max 1 childSigma]. *)
Definition formulaRankExTermAt
    (sigma pi childSigma childPi : term) : formula :=
  pEx (pAnd3
    (maxTermAt (tVar 0) (Term.numeral 1) (liftTerm 1 childSigma))
    (pEq (liftTerm 1 sigma) (tVar 0))
    (pEq (liftTerm 1 pi) (tSucc (tVar 0)))).

Definition RawFormulaRankZero (M : RawPAModel) (sigma pi : M) : Prop :=
  sigma = raw_zero M /\ pi = raw_zero M.

Definition RawFormulaRankImp (M : RawPAModel)
    (sigma pi leftSigma leftPi rightSigma rightPi : M) : Prop :=
  RawMax M sigma leftPi rightSigma /\
  RawMax M pi leftSigma rightPi.

Definition RawFormulaRankAndOr (M : RawPAModel)
    (sigma pi leftSigma leftPi rightSigma rightPi : M) : Prop :=
  RawMax M sigma leftSigma rightSigma /\
  RawMax M pi leftPi rightPi.

Definition RawFormulaRankAll (M : RawPAModel)
    (sigma pi childSigma childPi : M) : Prop :=
  exists base : M,
    RawMax M base (rawNumeralValue M 1) childPi /\
    pi = base /\ sigma = raw_succ M base.

Definition RawFormulaRankEx (M : RawPAModel)
    (sigma pi childSigma childPi : M) : Prop :=
  exists base : M,
    RawMax M base (rawNumeralValue M 1) childSigma /\
    sigma = base /\ pi = raw_succ M base.

Arguments RawFormulaRankZero M sigma pi : clear implicits.
Arguments RawFormulaRankImp M sigma pi leftSigma leftPi rightSigma rightPi
  : clear implicits.
Arguments RawFormulaRankAndOr M sigma pi leftSigma leftPi rightSigma rightPi
  : clear implicits.
Arguments RawFormulaRankAll M sigma pi childSigma childPi : clear implicits.
Arguments RawFormulaRankEx M sigma pi childSigma childPi : clear implicits.

Lemma raw_eval_liftTerm_one_rank : forall (M : RawPAModel)
    x (e : nat -> M) t,
  raw_term_eval M (scons M x e) (liftTerm 1 t) =
  raw_term_eval M e t.
Proof.
  intros M x e t. unfold liftTerm.
  rewrite raw_term_eval_rename.
  apply raw_term_eval_ext. intro i.
  replace (i + 1) with (S i) by lia. reflexivity.
Qed.

Lemma raw_sat_formulaRankZeroTermAt_iff : forall (M : RawPAModel)
    e sigma pi,
  raw_formula_sat M e (formulaRankZeroTermAt sigma pi) <->
  RawFormulaRankZero M (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof. reflexivity. Qed.

Lemma raw_sat_formulaRankImpTermAt_iff : forall (M : RawPAModel)
    e sigma pi leftSigma leftPi rightSigma rightPi,
  raw_formula_sat M e
    (formulaRankImpTermAt sigma pi leftSigma leftPi rightSigma rightPi) <->
  RawFormulaRankImp M (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e leftSigma) (raw_term_eval M e leftPi)
    (raw_term_eval M e rightSigma) (raw_term_eval M e rightPi).
Proof.
  intros. unfold formulaRankImpTermAt, RawFormulaRankImp.
  cbn [raw_formula_sat]. rewrite !raw_sat_maxTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaRankAndOrTermAt_iff : forall (M : RawPAModel)
    e sigma pi leftSigma leftPi rightSigma rightPi,
  raw_formula_sat M e
    (formulaRankAndOrTermAt sigma pi
      leftSigma leftPi rightSigma rightPi) <->
  RawFormulaRankAndOr M (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e leftSigma) (raw_term_eval M e leftPi)
    (raw_term_eval M e rightSigma) (raw_term_eval M e rightPi).
Proof.
  intros. unfold formulaRankAndOrTermAt, RawFormulaRankAndOr.
  cbn [raw_formula_sat]. rewrite !raw_sat_maxTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaRankAllTermAt_iff : forall (M : RawPAModel)
    e sigma pi childSigma childPi,
  raw_formula_sat M e
    (formulaRankAllTermAt sigma pi childSigma childPi) <->
  RawFormulaRankAll M (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e childSigma) (raw_term_eval M e childPi).
Proof.
  intros M e sigma pi childSigma childPi.
  unfold formulaRankAllTermAt, RawFormulaRankAll, pAnd3.
  cbn [raw_formula_sat]. split.
  - intros [base [hmax [hpi hsigma]]]. exists base.
    rewrite raw_sat_maxTermAt_iff in hmax.
    rewrite raw_term_eval_numeral in hmax.
    repeat rewrite raw_eval_liftTerm_one_rank in hmax, hpi, hsigma.
    cbn [raw_term_eval scons] in hpi, hsigma.
    repeat split; assumption.
  - intros [base [hmax [hpi hsigma]]]. exists base.
    split.
    + rewrite raw_sat_maxTermAt_iff.
      rewrite raw_term_eval_numeral.
      rewrite raw_eval_liftTerm_one_rank. exact hmax.
    + split.
      * rewrite raw_eval_liftTerm_one_rank.
        cbn [raw_term_eval scons]. exact hpi.
      * rewrite raw_eval_liftTerm_one_rank.
        cbn [raw_term_eval scons]. exact hsigma.
Qed.

Lemma raw_sat_formulaRankExTermAt_iff : forall (M : RawPAModel)
    e sigma pi childSigma childPi,
  raw_formula_sat M e
    (formulaRankExTermAt sigma pi childSigma childPi) <->
  RawFormulaRankEx M (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e childSigma) (raw_term_eval M e childPi).
Proof.
  intros M e sigma pi childSigma childPi.
  unfold formulaRankExTermAt, RawFormulaRankEx, pAnd3.
  cbn [raw_formula_sat]. split.
  - intros [base [hmax [hsigma hpi]]]. exists base.
    rewrite raw_sat_maxTermAt_iff in hmax.
    rewrite raw_term_eval_numeral in hmax.
    repeat rewrite raw_eval_liftTerm_one_rank in hmax, hsigma, hpi.
    cbn [raw_term_eval scons] in hsigma, hpi.
    repeat split; assumption.
  - intros [base [hmax [hsigma hpi]]]. exists base.
    split.
    + rewrite raw_sat_maxTermAt_iff.
      rewrite raw_term_eval_numeral.
      rewrite raw_eval_liftTerm_one_rank. exact hmax.
    + split.
      * rewrite raw_eval_liftTerm_one_rank.
        cbn [raw_term_eval scons]. exact hsigma.
      * rewrite raw_eval_liftTerm_one_rank.
        cbn [raw_term_eval scons]. exact hpi.
Qed.

(** ------------------------------------------------------------------
    Constructor-and-rank rows.  Child codes and child ranks are explicit row
    inputs; a later trace layer is responsible for linking them to earlier
    certified rows. *)

Definition formulaEqRankStepTermAt
    (code sigma pi left right : term) : formula :=
  pAnd (formulaEqCodeTermAt code left right)
    (formulaRankZeroTermAt sigma pi).

Definition formulaBotRankStepTermAt
    (code sigma pi : term) : formula :=
  pAnd (formulaBotCodeTermAt code)
    (formulaRankZeroTermAt sigma pi).

Definition formulaImpRankStepTermAt
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : term)
    : formula :=
  pAnd (formulaImpCodeTermAt code left right)
    (formulaRankImpTermAt sigma pi
      leftSigma leftPi rightSigma rightPi).

Definition formulaAndRankStepTermAt
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : term)
    : formula :=
  pAnd (formulaAndCodeTermAt code left right)
    (formulaRankAndOrTermAt sigma pi
      leftSigma leftPi rightSigma rightPi).

Definition formulaOrRankStepTermAt
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : term)
    : formula :=
  pAnd (formulaOrCodeTermAt code left right)
    (formulaRankAndOrTermAt sigma pi
      leftSigma leftPi rightSigma rightPi).

Definition formulaAllRankStepTermAt
    (code sigma pi child childSigma childPi : term) : formula :=
  pAnd (formulaAllCodeTermAt code child)
    (formulaRankAllTermAt sigma pi childSigma childPi).

Definition formulaExRankStepTermAt
    (code sigma pi child childSigma childPi : term) : formula :=
  pAnd (formulaExCodeTermAt code child)
    (formulaRankExTermAt sigma pi childSigma childPi).

Definition RawFormulaEqRankStep (M : RawPAModel)
    (code sigma pi left right : M) : Prop :=
  code = rawFormulaEqCode M left right /\
  RawFormulaRankZero M sigma pi.

Definition RawFormulaBotRankStep (M : RawPAModel)
    (code sigma pi : M) : Prop :=
  code = rawFormulaBotCode M /\ RawFormulaRankZero M sigma pi.

Definition RawFormulaImpRankStep (M : RawPAModel)
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : M)
    : Prop :=
  code = rawFormulaImpCode M left right /\
  RawFormulaRankImp M sigma pi leftSigma leftPi rightSigma rightPi.

Definition RawFormulaAndRankStep (M : RawPAModel)
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : M)
    : Prop :=
  code = rawFormulaAndCode M left right /\
  RawFormulaRankAndOr M sigma pi leftSigma leftPi rightSigma rightPi.

Definition RawFormulaOrRankStep (M : RawPAModel)
    (code sigma pi left leftSigma leftPi right rightSigma rightPi : M)
    : Prop :=
  code = rawFormulaOrCode M left right /\
  RawFormulaRankAndOr M sigma pi leftSigma leftPi rightSigma rightPi.

Definition RawFormulaAllRankStep (M : RawPAModel)
    (code sigma pi child childSigma childPi : M) : Prop :=
  code = rawFormulaAllCode M child /\
  RawFormulaRankAll M sigma pi childSigma childPi.

Definition RawFormulaExRankStep (M : RawPAModel)
    (code sigma pi child childSigma childPi : M) : Prop :=
  code = rawFormulaExCode M child /\
  RawFormulaRankEx M sigma pi childSigma childPi.

Lemma raw_sat_formulaEqRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi left right,
  raw_formula_sat M e
    (formulaEqRankStepTermAt code sigma pi left right) <->
  RawFormulaEqRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e left) (raw_term_eval M e right).
Proof.
  intros. unfold formulaEqRankStepTermAt, RawFormulaEqRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaEqCodeTermAt_iff.
  rewrite raw_sat_formulaRankZeroTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaBotRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi,
  raw_formula_sat M e (formulaBotRankStepTermAt code sigma pi) <->
  RawFormulaBotRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros. unfold formulaBotRankStepTermAt, RawFormulaBotRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaBotCodeTermAt_iff.
  rewrite raw_sat_formulaRankZeroTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaImpRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi left leftSigma leftPi right rightSigma rightPi,
  raw_formula_sat M e
    (formulaImpRankStepTermAt code sigma pi
      left leftSigma leftPi right rightSigma rightPi) <->
  RawFormulaImpRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e left) (raw_term_eval M e leftSigma)
    (raw_term_eval M e leftPi) (raw_term_eval M e right)
    (raw_term_eval M e rightSigma) (raw_term_eval M e rightPi).
Proof.
  intros. unfold formulaImpRankStepTermAt, RawFormulaImpRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaImpCodeTermAt_iff.
  rewrite raw_sat_formulaRankImpTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaAndRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi left leftSigma leftPi right rightSigma rightPi,
  raw_formula_sat M e
    (formulaAndRankStepTermAt code sigma pi
      left leftSigma leftPi right rightSigma rightPi) <->
  RawFormulaAndRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e left) (raw_term_eval M e leftSigma)
    (raw_term_eval M e leftPi) (raw_term_eval M e right)
    (raw_term_eval M e rightSigma) (raw_term_eval M e rightPi).
Proof.
  intros. unfold formulaAndRankStepTermAt, RawFormulaAndRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaAndCodeTermAt_iff.
  rewrite raw_sat_formulaRankAndOrTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaOrRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi left leftSigma leftPi right rightSigma rightPi,
  raw_formula_sat M e
    (formulaOrRankStepTermAt code sigma pi
      left leftSigma leftPi right rightSigma rightPi) <->
  RawFormulaOrRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e left) (raw_term_eval M e leftSigma)
    (raw_term_eval M e leftPi) (raw_term_eval M e right)
    (raw_term_eval M e rightSigma) (raw_term_eval M e rightPi).
Proof.
  intros. unfold formulaOrRankStepTermAt, RawFormulaOrRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaOrCodeTermAt_iff.
  rewrite raw_sat_formulaRankAndOrTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaAllRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi child childSigma childPi,
  raw_formula_sat M e
    (formulaAllRankStepTermAt code sigma pi child childSigma childPi) <->
  RawFormulaAllRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e child) (raw_term_eval M e childSigma)
    (raw_term_eval M e childPi).
Proof.
  intros. unfold formulaAllRankStepTermAt, RawFormulaAllRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaAllCodeTermAt_iff.
  rewrite raw_sat_formulaRankAllTermAt_iff. reflexivity.
Qed.

Lemma raw_sat_formulaExRankStepTermAt_iff : forall (M : RawPAModel)
    e code sigma pi child childSigma childPi,
  raw_formula_sat M e
    (formulaExRankStepTermAt code sigma pi child childSigma childPi) <->
  RawFormulaExRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi)
    (raw_term_eval M e child) (raw_term_eval M e childSigma)
    (raw_term_eval M e childPi).
Proof.
  intros. unfold formulaExRankStepTermAt, RawFormulaExRankStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_formulaExCodeTermAt_iff.
  rewrite raw_sat_formulaRankExTermAt_iff. reflexivity.
Qed.

(** Standard values satisfy the transparent maximum relation.  This is the
    arithmetic base needed to show that genuine quoted syntax receives the
    same rank pair as [sigmaRank]/[piRank]. *)
Lemma rawLe_numerals_of_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b,
  a <= b -> rawLe M (rawNumeralValue M a) (rawNumeralValue M b).
Proof.
  intros M hPA a b hab.
  exists (rawNumeralValue M (b - a)).
  rewrite raw_add_numeral_values_syntax by exact hPA.
  f_equal. lia.
Qed.

Lemma RawMax_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall a b,
  RawMax M (rawNumeralValue M (Nat.max a b))
    (rawNumeralValue M a) (rawNumeralValue M b).
Proof.
  intros M hPA a b.
  destruct (Nat.le_ge_cases a b) as [hab | hba].
  - left. split.
    + apply rawLe_numerals_of_le; assumption.
    + now rewrite Nat.max_r.
  - right. split.
    + apply rawLe_numerals_of_le; assumption.
    + now rewrite Nat.max_l.
Qed.

End PABoundedRawCodedFormulaRankStep.
