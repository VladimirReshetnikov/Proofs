(**
  Beta-coded global traversals for coded formula hierarchy ranks.

  A traversal consists of three Goedel-beta tables with a common row index:
  one table stores formula codes, and the other two store their sigma and pi
  ranks.  A non-atomic row may use only rows at strictly smaller indices for
  its immediate children.  Thus a certificate is a model-internal postorder
  traversal; its bound and all of its rows may be nonstandard.

  The definitions below are genuine first-order PA formulae.  Their exact
  semantics are proved for arbitrary law-free [RawPAModel] structures, while
  functionality of beta lookup and prefix restriction use [RawPASatisfies].
  No totality assertion is made: existence of a traversal for every
  nonstandard formula code is isolated explicitly at the end of the file.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedSyntax RawCodedSyntaxConstructors
  RawCodedSyntaxConstructorSeparation RawCodedFormulaRankStep
  RawCodedFormulaRankStepFunctionality RawCodedAssignment.

Import ListNotations.

Module PABoundedRawCodedFormulaRankTraversal.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedSyntaxConstructorSeparation.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankStepFunctionality.
Import PABoundedRawCodedAssignment.

(** Small right-associated connectives keep the row formulae readable. *)
Definition rankTraversalAnd3 (a b c : formula) : formula :=
  pAnd a (pAnd b c).

Definition rankTraversalAnd4 (a b c d : formula) : formula :=
  pAnd a (pAnd b (pAnd c d)).

Definition rankTraversalAnd5 (a b c d f : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d f))).

Definition rankTraversalAnd6 (a b c d f g : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f g)))).

Definition rankTraversalEx2 (body : formula) : formula :=
  pEx (pEx body).

Definition rankTraversalEx4 (body : formula) : formula :=
  pEx (pEx (pEx (pEx body))).

Definition rankTraversalEx8 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx (pEx (pEx body))))))).

(** Raw evaluation commutes with lifting past the witness blocks used by a
    two-child row.  These are raw-model versions of the standard-model lift
    lemmas in [ListFormulas]. *)
Lemma raw_rankTraversal_eval_liftTerm_two : forall (M : RawPAModel)
    a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 2) with (S (S i)) by lia. reflexivity.
Qed.

Lemma raw_rankTraversal_eval_liftTerm_four : forall (M : RawPAModel)
    a b c d (e : nat -> M) t,
  raw_term_eval M
    (scons M a (scons M b (scons M c (scons M d e))))
    (liftTerm 4 t) = raw_term_eval M e t.
Proof.
  intros M a b c d e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro i.
  replace (i + 4) with (S (S (S (S i)))) by lia. reflexivity.
Qed.

Lemma raw_rankTraversal_eval_liftTerm_eight : forall (M : RawPAModel)
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
    Synchronized lookup in the three row tables. *)

Definition codedFormulaRankTripleLookupTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  pAnd
    (codedAssignmentLookupTermAt formulaCode formulaStep index code)
    (pAnd
      (codedAssignmentLookupTermAt sigmaCode sigmaStep index sigma)
      (codedAssignmentLookupTermAt piCode piStep index pi)).

Definition RawCodedFormulaRankTripleLookup (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : M) : Prop :=
  RawCodedAssignmentLookup M formulaCode formulaStep index code /\
  RawCodedAssignmentLookup M sigmaCode sigmaStep index sigma /\
  RawCodedAssignmentLookup M piCode piStep index pi.

Arguments RawCodedFormulaRankTripleLookup
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi : clear implicits.

Lemma raw_sat_codedFormulaRankTripleLookupTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaRankTripleLookupTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaRankTripleLookup M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros. unfold codedFormulaRankTripleLookupTermAt,
    RawCodedFormulaRankTripleLookup.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentLookupTermAt_iff. reflexivity.
Qed.

Theorem raw_codedFormulaRankTripleLookup_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi code' sigma' pi',
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi ->
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code' sigma' pi' ->
  code = code' /\ sigma = sigma' /\ pi = pi'.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi code' sigma' pi'
    [hcode [hsigma hpi]] [hcode' [hsigma' hpi']].
  repeat split.
  - exact (raw_codedAssignmentLookup_functional M hPA
      formulaCode formulaStep index code code' hcode hcode').
  - exact (raw_codedAssignmentLookup_functional M hPA
      sigmaCode sigmaStep index sigma sigma' hsigma hsigma').
  - exact (raw_codedAssignmentLookup_functional M hPA
      piCode piStep index pi pi' hpi hpi').
Qed.

(** ------------------------------------------------------------------
    Locally certified postorder rows.

    The eight witnesses of a binary row, from outermost to innermost, are
    left index/code/sigma/pi and right index/code/sigma/pi.  At the body they
    consequently occupy variables seven down to zero.  Unary rows use the
    analogous four-variable block. *)

Definition codedFormulaEqRankTraversalRowTermAt
    (code sigma pi : term) : formula :=
  rankTraversalEx2
    (formulaEqRankStepTermAt
      (liftTerm 2 code) (liftTerm 2 sigma) (liftTerm 2 pi)
      (tVar 1) (tVar 0)).

Definition codedFormulaBotRankTraversalRowTermAt
    (code sigma pi : term) : formula :=
  formulaBotRankStepTermAt code sigma pi.

Definition codedFormulaImpRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  rankTraversalEx8 (rankTraversalAnd5
    (Formula.ltTermAt (tVar 7) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4))
    (Formula.ltTermAt (tVar 3) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (formulaImpRankStepTermAt
      (liftTerm 8 code) (liftTerm 8 sigma) (liftTerm 8 pi)
      (tVar 6) (tVar 5) (tVar 4)
      (tVar 2) (tVar 1) (tVar 0))).

Definition codedFormulaAndRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  rankTraversalEx8 (rankTraversalAnd5
    (Formula.ltTermAt (tVar 7) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4))
    (Formula.ltTermAt (tVar 3) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (formulaAndRankStepTermAt
      (liftTerm 8 code) (liftTerm 8 sigma) (liftTerm 8 pi)
      (tVar 6) (tVar 5) (tVar 4)
      (tVar 2) (tVar 1) (tVar 0))).

Definition codedFormulaOrRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  rankTraversalEx8 (rankTraversalAnd5
    (Formula.ltTermAt (tVar 7) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 7) (tVar 6) (tVar 5) (tVar 4))
    (Formula.ltTermAt (tVar 3) (liftTerm 8 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 8 formulaCode) (liftTerm 8 formulaStep)
      (liftTerm 8 sigmaCode) (liftTerm 8 sigmaStep)
      (liftTerm 8 piCode) (liftTerm 8 piStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (formulaOrRankStepTermAt
      (liftTerm 8 code) (liftTerm 8 sigma) (liftTerm 8 pi)
      (tVar 6) (tVar 5) (tVar 4)
      (tVar 2) (tVar 1) (tVar 0))).

Definition codedFormulaAllRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  rankTraversalEx4 (rankTraversalAnd3
    (Formula.ltTermAt (tVar 3) (liftTerm 4 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
      (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
      (liftTerm 4 piCode) (liftTerm 4 piStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (formulaAllRankStepTermAt
      (liftTerm 4 code) (liftTerm 4 sigma) (liftTerm 4 pi)
      (tVar 2) (tVar 1) (tVar 0))).

Definition codedFormulaExRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  rankTraversalEx4 (rankTraversalAnd3
    (Formula.ltTermAt (tVar 3) (liftTerm 4 index))
    (codedFormulaRankTripleLookupTermAt
      (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
      (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
      (liftTerm 4 piCode) (liftTerm 4 piStep)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0))
    (formulaExRankStepTermAt
      (liftTerm 4 code) (liftTerm 4 sigma) (liftTerm 4 pi)
      (tVar 2) (tVar 1) (tVar 0))).

(** Seven-way local row relation. *)
Definition codedFormulaRankTraversalRowTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : term) : formula :=
  pOr (codedFormulaEqRankTraversalRowTermAt code sigma pi)
  (pOr (codedFormulaBotRankTraversalRowTermAt code sigma pi)
  (pOr (codedFormulaImpRankTraversalRowTermAt
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi)
  (pOr (codedFormulaAndRankTraversalRowTermAt
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi)
  (pOr (codedFormulaOrRankTraversalRowTermAt
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi)
  (pOr (codedFormulaAllRankTraversalRowTermAt
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi)
    (codedFormulaExRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi)))))).

Definition RawCodedFormulaEqRankTraversalRow (M : RawPAModel)
    (code sigma pi : M) : Prop :=
  exists left right : M,
    RawFormulaEqRankStep M code sigma pi left right.

Definition RawCodedFormulaBinaryRankTraversalRow (M : RawPAModel)
    (stepRelation : M -> M -> M -> M -> M -> M -> M -> M -> M -> Prop)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : M) : Prop :=
  exists leftIndex left leftSigma leftPi
    rightIndex right rightSigma rightPi : M,
    rawLt M leftIndex index /\
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      leftIndex left leftSigma leftPi /\
    rawLt M rightIndex index /\
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      rightIndex right rightSigma rightPi /\
    stepRelation code sigma pi
      left leftSigma leftPi right rightSigma rightPi.

Definition RawCodedFormulaUnaryRankTraversalRow (M : RawPAModel)
    (stepRelation : M -> M -> M -> M -> M -> M -> Prop)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : M) : Prop :=
  exists childIndex child childSigma childPi : M,
    rawLt M childIndex index /\
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      childIndex child childSigma childPi /\
    stepRelation code sigma pi child childSigma childPi.

Definition RawCodedFormulaRankTraversalRow (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi : M) : Prop :=
  RawCodedFormulaEqRankTraversalRow M code sigma pi \/
  RawFormulaBotRankStep M code sigma pi \/
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaImpRankStep M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi \/
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaAndRankStep M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi \/
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaOrRankStep M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi \/
  RawCodedFormulaUnaryRankTraversalRow M (RawFormulaAllRankStep M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi \/
  RawCodedFormulaUnaryRankTraversalRow M (RawFormulaExRankStep M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.

Arguments RawCodedFormulaRankTraversalRow
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi : clear implicits.

(** Semantic helper lemmas for the seven row branches. *)
Lemma raw_sat_codedFormulaEqRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code sigma pi,
  raw_formula_sat M e
    (codedFormulaEqRankTraversalRowTermAt code sigma pi) <->
  RawCodedFormulaEqRankTraversalRow M
    (raw_term_eval M e code) (raw_term_eval M e sigma)
    (raw_term_eval M e pi).
Proof.
  intros M e code sigma pi.
  unfold codedFormulaEqRankTraversalRowTermAt,
    rankTraversalEx2, RawCodedFormulaEqRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros [left [right hstep]]. exists left, right.
    apply (proj1 (raw_sat_formulaEqRankStepTermAt_iff M
      (scons M right (scons M left e)) _ _ _ _ _)) in hstep.
    repeat rewrite raw_rankTraversal_eval_liftTerm_two in hstep.
    cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros [left [right hstep]]. exists left, right.
    apply (proj2 (raw_sat_formulaEqRankStepTermAt_iff M
      (scons M right (scons M left e)) _ _ _ _ _)).
    repeat rewrite raw_rankTraversal_eval_liftTerm_two.
    cbn [raw_term_eval scons]. exact hstep.
Qed.

Lemma raw_sat_codedFormulaBotRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code sigma pi,
  raw_formula_sat M e
    (codedFormulaBotRankTraversalRowTermAt code sigma pi) <->
  RawFormulaBotRankStep M (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros. unfold codedFormulaBotRankTraversalRowTermAt.
  apply raw_sat_formulaBotRankStepTermAt_iff.
Qed.

Lemma raw_sat_codedFormulaImpRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaImpRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaImpRankStep M)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold codedFormulaImpRankTraversalRowTermAt, rankTraversalEx8,
    rankTraversalAnd5, RawCodedFormulaBinaryRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltl.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltl.
      cbn [raw_term_eval scons] in hltl. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookl.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookl.
      cbn [raw_term_eval scons] in hlookl. exact hlookl.
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltr.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltr.
      cbn [raw_term_eval scons] in hltr. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookr.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookr.
      cbn [raw_term_eval scons] in hlookr. exact hlookr.
    + rewrite raw_sat_formulaImpRankStepTermAt_iff in hstep.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookl.
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookr.
    + rewrite raw_sat_formulaImpRankStepTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Lemma raw_sat_codedFormulaAndRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaAndRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaAndRankStep M)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold codedFormulaAndRankTraversalRowTermAt, rankTraversalEx8,
    rankTraversalAnd5, RawCodedFormulaBinaryRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltl.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltl.
      cbn [raw_term_eval scons] in hltl. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookl.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookl.
      cbn [raw_term_eval scons] in hlookl. exact hlookl.
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltr.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltr.
      cbn [raw_term_eval scons] in hltr. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookr.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookr.
      cbn [raw_term_eval scons] in hlookr. exact hlookr.
    + rewrite raw_sat_formulaAndRankStepTermAt_iff in hstep.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookl.
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookr.
    + rewrite raw_sat_formulaAndRankStepTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Lemma raw_sat_codedFormulaOrRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaOrRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaBinaryRankTraversalRow M (RawFormulaOrRankStep M)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold codedFormulaOrRankTraversalRowTermAt, rankTraversalEx8,
    rankTraversalAnd5, RawCodedFormulaBinaryRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltl.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltl.
      cbn [raw_term_eval scons] in hltl. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookl.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookl.
      cbn [raw_term_eval scons] in hlookl. exact hlookl.
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hltr.
      rewrite raw_rankTraversal_eval_liftTerm_eight in hltr.
      cbn [raw_term_eval scons] in hltr. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookr.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hlookr.
      cbn [raw_term_eval scons] in hlookr. exact hlookr.
    + rewrite raw_sat_formulaOrRankStepTermAt_iff in hstep.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros (li & lc & ls & lp & ri & rc & rs & rp &
      hltl & hlookl & hltr & hlookr & hstep).
    exists li, lc, ls, lp, ri, rc, rs, rp.
    split; [| split; [| split; [| split]]].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltl.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookl.
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hltr.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hlookr.
    + rewrite raw_sat_formulaOrRankStepTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_eight.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Lemma raw_sat_codedFormulaAllRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaAllRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaUnaryRankTraversalRow M (RawFormulaAllRankStep M)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold codedFormulaAllRankTraversalRowTermAt, rankTraversalEx4,
    rankTraversalAnd3, RawCodedFormulaUnaryRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros (ci & child & cs & cp & hlt & hlookup & hstep).
    exists ci, child, cs, cp. split; [|split].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hlt.
      rewrite raw_rankTraversal_eval_liftTerm_four in hlt.
      cbn [raw_term_eval scons] in hlt. exact hlt.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookup.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hlookup.
      cbn [raw_term_eval scons] in hlookup. exact hlookup.
    + rewrite raw_sat_formulaAllRankStepTermAt_iff in hstep.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros (ci & child & cs & cp & hlt & hlookup & hstep).
    exists ci, child, cs, cp. split; [|split].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hlt.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hlookup.
    + rewrite raw_sat_formulaAllRankStepTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Lemma raw_sat_codedFormulaExRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaExRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaUnaryRankTraversalRow M (RawFormulaExRankStep M)
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold codedFormulaExRankTraversalRowTermAt, rankTraversalEx4,
    rankTraversalAnd3, RawCodedFormulaUnaryRankTraversalRow.
  cbn [raw_formula_sat]. split.
  - intros (ci & child & cs & cp & hlt & hlookup & hstep).
    exists ci, child, cs, cp. split; [|split].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hlt.
      rewrite raw_rankTraversal_eval_liftTerm_four in hlt.
      cbn [raw_term_eval scons] in hlt. exact hlt.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff in hlookup.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hlookup.
      cbn [raw_term_eval scons] in hlookup. exact hlookup.
    + rewrite raw_sat_formulaExRankStepTermAt_iff in hstep.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hstep.
      cbn [raw_term_eval scons] in hstep. exact hstep.
  - intros (ci & child & cs & cp & hlt & hlookup & hstep).
    exists ci, child, cs, cp. split; [|split].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hlt.
    + rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hlookup.
    + rewrite raw_sat_formulaExRankStepTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hstep.
Qed.

Theorem raw_sat_codedFormulaRankTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  raw_formula_sat M e
    (codedFormulaRankTraversalRowTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi) <->
  RawCodedFormulaRankTraversalRow M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e index) (raw_term_eval M e code)
    (raw_term_eval M e sigma) (raw_term_eval M e pi).
Proof.
  intros. unfold codedFormulaRankTraversalRowTermAt,
    RawCodedFormulaRankTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaEqRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaBotRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaImpRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaAndRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaOrRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaAllRankTraversalRowTermAt_iff.
  rewrite raw_sat_codedFormulaExRankTraversalRowTermAt_iff.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The model-internal global traversal. *)

Definition codedFormulaRankTraversalRowsTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound : term)
    : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 bound))
      (pImp
        (codedFormulaRankTripleLookupTermAt
          (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
          (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
          (liftTerm 4 piCode) (liftTerm 4 piStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (codedFormulaRankTraversalRowTermAt
          (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
          (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
          (liftTerm 4 piCode) (liftTerm 4 piStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))))))).

Definition RawCodedFormulaRankTraversalRows (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound : M)
    : Prop :=
  forall index code sigma pi : M,
    rawLt M index bound ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi ->
    RawCodedFormulaRankTraversalRow M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi.

Arguments RawCodedFormulaRankTraversalRows
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound
  : clear implicits.

Lemma raw_sat_codedFormulaRankTraversalRowsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound,
  raw_formula_sat M e
    (codedFormulaRankTraversalRowsTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound) <->
  RawCodedFormulaRankTraversalRows M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound.
  unfold codedFormulaRankTraversalRowsTermAt,
    RawCodedFormulaRankTraversalRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaRankTraversalTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi : term) : formula :=
  rankTraversalAnd6
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (codedAssignmentDefinedThroughTermAt sigmaCode sigmaStep bound)
    (codedAssignmentDefinedThroughTermAt piCode piStep bound)
    (Formula.ltTermAt rootIndex bound)
    (codedFormulaRankTripleLookupTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      rootIndex root sigma pi)
    (codedFormulaRankTraversalRowsTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound).

Definition RawCodedFormulaRankTraversal (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi : M) : Prop :=
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  RawCodedAssignmentDefinedThrough M sigmaCode sigmaStep bound /\
  RawCodedAssignmentDefinedThrough M piCode piStep bound /\
  rawLt M rootIndex bound /\
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    rootIndex root sigma pi /\
  RawCodedFormulaRankTraversalRows M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound.

Arguments RawCodedFormulaRankTraversal
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi : clear implicits.

Theorem raw_sat_codedFormulaRankTraversalTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  raw_formula_sat M e
    (codedFormulaRankTraversalTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi) <->
  RawCodedFormulaRankTraversal M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e root) (raw_term_eval M e sigma)
    (raw_term_eval M e pi).
Proof.
  intros. unfold codedFormulaRankTraversalTermAt,
    RawCodedFormulaRankTraversal, rankTraversalAnd6.
  cbn [raw_formula_sat].
  rewrite !raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
  rewrite raw_sat_codedFormulaRankTraversalRowsTermAt_iff.
  reflexivity.
Qed.

(** Existential closure: [root,sigma,pi] are the public graph arguments;
    eight witnesses choose the three beta-table pairs, the row bound, and
    the designated root index. *)
Definition codedFormulaRankTermAt (root sigma pi : term) : formula :=
  rankTraversalEx8
    (codedFormulaRankTraversalTermAt
      (tVar 7) (tVar 6) (tVar 5) (tVar 4)
      (tVar 3) (tVar 2) (tVar 1) (tVar 0)
      (liftTerm 8 root) (liftTerm 8 sigma) (liftTerm 8 pi)).

Definition RawCodedFormulaRank (M : RawPAModel)
    (root sigma pi : M) : Prop :=
  exists formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex : M,
    RawCodedFormulaRankTraversal M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex root sigma pi.

Arguments RawCodedFormulaRank M root sigma pi : clear implicits.

Theorem raw_sat_codedFormulaRankTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) root sigma pi,
  raw_formula_sat M e (codedFormulaRankTermAt root sigma pi) <->
  RawCodedFormulaRank M
    (raw_term_eval M e root) (raw_term_eval M e sigma)
    (raw_term_eval M e pi).
Proof.
  intros M e root sigma pi.
  unfold codedFormulaRankTermAt, rankTraversalEx8,
    RawCodedFormulaRank.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaRankTraversalTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_eight.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Functionality and output facts available without totality. *)

Theorem raw_codedFormulaRankTraversal_row_exists_unique : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi ->
  forall index, rawLt M index bound ->
  exists code sigma pi,
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi /\
    RawCodedFormulaRankTraversalRow M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi /\
    forall code' sigma' pi',
      RawCodedFormulaRankTripleLookup M
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        index code' sigma' pi' ->
      code = code' /\ sigma = sigma' /\ pi = pi'.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root rootSigma rootPi
    [hcodeDefined [hsigmaDefined [hpiDefined
      [_ [_ hrows]]]]] index hindex.
  destruct (hcodeDefined index hindex) as [code hcode].
  destruct (hsigmaDefined index hindex) as [sigma hsigma].
  destruct (hpiDefined index hindex) as [pi hpi].
  assert (hlookup : RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi).
  { repeat split; assumption. }
  exists code, sigma, pi. split; [exact hlookup |]. split.
  - exact (hrows index code sigma pi hindex hlookup).
  - intros code' sigma' pi' hlookup'.
    exact (raw_codedFormulaRankTripleLookup_functional M hPA
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi code' sigma' pi' hlookup hlookup').
Qed.

Corollary raw_codedFormulaRankTraversal_root_row : forall
    (M : RawPAModel)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  RawCodedFormulaRankTraversalRow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    rootIndex root sigma pi.
Proof.
  intros M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi
    [_ [_ [_ [hroot [hlookup hrows]]]]].
  exact (hrows rootIndex root sigma pi hroot hlookup).
Qed.

Theorem raw_codedFormulaRankTraversal_root_output_functional : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi sigma' pi',
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    rootIndex root sigma' pi' ->
  sigma = sigma' /\ pi = pi'.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi sigma' pi'
    [_ [_ [_ [_ [hrootLookup _]]]]] hother.
  destruct (raw_codedFormulaRankTripleLookup_functional M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    rootIndex root sigma pi root sigma' pi' hrootLookup hother)
    as [_ [hsigma hpi]].
  split; assumption.
Qed.

(** Any earlier certified row can itself be exposed as the root of the same
    tables, restricted to its successor prefix.  This is the structural
    induction bridge needed by later standard-code soundness proofs. *)
Theorem raw_codedFormulaRankTraversal_restrict_to_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  forall index code rowSigma rowPi,
    rawLt M index bound ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code rowSigma rowPi ->
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    (raw_succ M index) index code rowSigma rowPi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi
    [hcodeDefined [hsigmaDefined [hpiDefined
      [_ [_ hrows]]]]] index code rowSigma rowPi hindex hlookup.
  assert (hbelow : forall x,
      rawLt M x (raw_succ M index) -> rawLt M x bound).
  {
    intros x hx.
    destruct (raw_lt_succ_cases M hPA x index hx) as [hxi | ->].
    - exact (raw_assignment_lt_trans M hPA x index bound hxi hindex).
    - exact hindex.
  }
  split; [| split; [| split; [| split; [| split]]]].
  - intros x hx. exact (hcodeDefined x (hbelow x hx)).
  - intros x hx. exact (hsigmaDefined x (hbelow x hx)).
  - intros x hx. exact (hpiDefined x (hbelow x hx)).
  - exact (raw_assignment_lt_self_succ M hPA index).
  - exact hlookup.
  - intros x rowCode s p hx hrowLookup.
    exact (hrows x rowCode s p (hbelow x hx) hrowLookup).
Qed.

(** ------------------------------------------------------------------
    Constructor views and standard-code rank soundness. *)

(** A shape records exactly the immediate payload of one formula
    constructor.  Recursive children are still carrier elements: this is
    essential when the row itself is nonstandard. *)
Inductive RawCodedFormulaShape (M : RawPAModel) : Type :=
| rawShapeEq : M -> M -> RawCodedFormulaShape M
| rawShapeBot : RawCodedFormulaShape M
| rawShapeImp : M -> M -> RawCodedFormulaShape M
| rawShapeAnd : M -> M -> RawCodedFormulaShape M
| rawShapeOr : M -> M -> RawCodedFormulaShape M
| rawShapeAll : M -> RawCodedFormulaShape M
| rawShapeEx : M -> RawCodedFormulaShape M.

Arguments rawShapeEq {M} left right.
Arguments rawShapeBot {M}.
Arguments rawShapeImp {M} left right.
Arguments rawShapeAnd {M} left right.
Arguments rawShapeOr {M} left right.
Arguments rawShapeAll {M} child.
Arguments rawShapeEx {M} child.

Definition rawCodedFormulaShapeCode (M : RawPAModel)
    (shape : RawCodedFormulaShape M) : M :=
  match shape with
  | rawShapeEq leftChild rightChild =>
      rawFormulaEqCode M leftChild rightChild
  | rawShapeBot => rawFormulaBotCode M
  | rawShapeImp leftChild rightChild =>
      rawFormulaImpCode M leftChild rightChild
  | rawShapeAnd leftChild rightChild =>
      rawFormulaAndCode M leftChild rightChild
  | rawShapeOr leftChild rightChild =>
      rawFormulaOrCode M leftChild rightChild
  | rawShapeAll child => rawFormulaAllCode M child
  | rawShapeEx child => rawFormulaExCode M child
  end.

Definition RawCodedFormulaShapeRankRow (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index : M) (shape : RawCodedFormulaShape M) (sigma pi : M) : Prop :=
  match shape with
  | rawShapeEq _ _ => RawFormulaRankZero M sigma pi
  | rawShapeBot => RawFormulaRankZero M sigma pi
  | rawShapeImp leftChild rightChild =>
      exists leftIndex leftSigma leftPi rightIndex rightSigma rightPi,
        rawLt M leftIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          leftIndex leftChild leftSigma leftPi /\
        rawLt M rightIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          rightIndex rightChild rightSigma rightPi /\
        RawFormulaRankImp M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeAnd leftChild rightChild =>
      exists leftIndex leftSigma leftPi rightIndex rightSigma rightPi,
        rawLt M leftIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          leftIndex leftChild leftSigma leftPi /\
        rawLt M rightIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          rightIndex rightChild rightSigma rightPi /\
        RawFormulaRankAndOr M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeOr leftChild rightChild =>
      exists leftIndex leftSigma leftPi rightIndex rightSigma rightPi,
        rawLt M leftIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          leftIndex leftChild leftSigma leftPi /\
        rawLt M rightIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          rightIndex rightChild rightSigma rightPi /\
        RawFormulaRankAndOr M sigma pi
          leftSigma leftPi rightSigma rightPi
  | rawShapeAll child =>
      exists childIndex childSigma childPi,
        rawLt M childIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          childIndex child childSigma childPi /\
        RawFormulaRankAll M sigma pi childSigma childPi
  | rawShapeEx child =>
      exists childIndex childSigma childPi,
        rawLt M childIndex index /\
        RawCodedFormulaRankTripleLookup M
          formulaCode formulaStep sigmaCode sigmaStep piCode piStep
          childIndex child childSigma childPi /\
        RawFormulaRankEx M sigma pi childSigma childPi
  end.

Arguments RawCodedFormulaShapeRankRow
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index shape sigma pi : clear implicits.

(** The seven-way formula row is equivalently one uniquely parsable shape
    plus its child links and rank equation.  Uniqueness of the shape code is
    proved separately below. *)
Theorem raw_codedFormulaRankTraversalRow_shape_iff : forall
    (M : RawPAModel)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi,
  RawCodedFormulaRankTraversalRow M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi <->
  exists shape : RawCodedFormulaShape M,
    code = rawCodedFormulaShapeCode M shape /\
    RawCodedFormulaShapeRankRow M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index shape sigma pi.
Proof.
  intros M formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    index code sigma pi.
  unfold RawCodedFormulaRankTraversalRow,
    RawCodedFormulaEqRankTraversalRow,
    RawCodedFormulaBinaryRankTraversalRow,
    RawCodedFormulaUnaryRankTraversalRow.
  split.
  - intros [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
    + destruct heq as [left [right [hcode hrank]]].
      exists (rawShapeEq left right). split; assumption.
    + destruct hbot as [hcode hrank].
      exists rawShapeBot. split; assumption.
    + destruct himp as
        (li & left & ls & lp & ri & right & rs & rp &
          hli & hleft & hri & hright & hcode & hrank).
      exists (rawShapeImp left right). split; [exact hcode |].
      exists li, ls, lp, ri, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright | exact hrank].
    + destruct hand as
        (li & left & ls & lp & ri & right & rs & rp &
          hli & hleft & hri & hright & hcode & hrank).
      exists (rawShapeAnd left right). split; [exact hcode |].
      exists li, ls, lp, ri, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright | exact hrank].
    + destruct hor as
        (li & left & ls & lp & ri & right & rs & rp &
          hli & hleft & hri & hright & hcode & hrank).
      exists (rawShapeOr left right). split; [exact hcode |].
      exists li, ls, lp, ri, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright | exact hrank].
    + destruct hall as
        (ci & child & cs & cp & hci & hchild & hcode & hrank).
      exists (rawShapeAll child). split; [exact hcode |].
      exists ci, cs, cp.
      split; [exact hci |].
      split; [exact hchild | exact hrank].
    + destruct hex as
        (ci & child & cs & cp & hci & hchild & hcode & hrank).
      exists (rawShapeEx child). split; [exact hcode |].
      exists ci, cs, cp.
      split; [exact hci |].
      split; [exact hchild | exact hrank].
  - intros [shape [hcode hrank]]. destruct shape as
      [left right | | left right | left right | left right | child | child];
      cbn [rawCodedFormulaShapeCode RawCodedFormulaShapeRankRow] in *.
    + left. exists left, right. split; assumption.
    + right. left. split; assumption.
    + right. right. left.
      destruct hrank as
        (li & ls & lp & ri & rs & rp & hli & hleft & hri & hright & hrank).
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright |].
      split; assumption.
    + right. right. right. left.
      destruct hrank as
        (li & ls & lp & ri & rs & rp & hli & hleft & hri & hright & hrank).
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright |].
      split; assumption.
    + right. right. right. right. left.
      destruct hrank as
        (li & ls & lp & ri & rs & rp & hli & hleft & hri & hright & hrank).
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleft |].
      split; [exact hri |].
      split; [exact hright |].
      split; assumption.
    + right. right. right. right. right. left.
      destruct hrank as (ci & cs & cp & hci & hchild & hrank).
      exists ci, child, cs, cp.
      split; [exact hci |].
      split; [exact hchild |].
      split; assumption.
    + right. right. right. right. right. right.
      destruct hrank as (ci & cs & cp & hci & hchild & hrank).
      exists ci, child, cs, cp.
      split; [exact hci |].
      split; [exact hchild |].
      split; assumption.
Qed.

(** The missing arity-one/arity-three separation fact follows by inspecting
    the first tail of the polynomial list code. *)
Lemma raw_codeList1_neq_codeList3_traversal : forall (M : RawPAModel),
  RawPASatisfies M -> RawListNodeInjective M -> forall a b c d,
  rawCodeList1 M a <> rawCodeList3 M b c d.
Proof.
  intros M hPA hnode a b c d heq.
  unfold rawCodeList1, rawCodeList3, rawListCode in heq.
  pose proof (proj2 (hnode a (raw_zero M) b
    (rawListNode M c (rawListNode M d (raw_zero M))) heq)) as hzero.
  exact (raw_zero_not_succ_syntax M hPA
    (rawPolynomialPair M c (rawListNode M d (raw_zero M))) hzero).
Qed.

(** Constructor shapes are injectively coded once the explicit polynomial
    pair proof is supplied. *)
Theorem rawCodedFormulaShapeCode_injective :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall left right : RawCodedFormulaShape M,
    rawCodedFormulaShapeCode M left =
    rawCodedFormulaShapeCode M right ->
    left = right.
Proof.
  intros hpairProof M hPA left right hcode.
  pose proof (raw_listNode_injective_of_pair_injective M hPA
    (raw_pair_injective_of_proof hpairProof M hPA)) as hnode.
  destruct left, right;
    cbn [rawCodedFormulaShapeCode rawFormulaEqCode rawFormulaBotCode
      rawFormulaImpCode rawFormulaAndCode rawFormulaOrCode
      rawFormulaAllCode rawFormulaExCode] in hcode |- *.
  all: try (pose proof (raw_codeList3_injective M hnode
      _ _ _ _ _ _ hcode) as [_ [hleft hright]];
    subst; reflexivity).
  all: try (pose proof (raw_codeList2_injective M hnode
      _ _ _ _ hcode) as [_ hchild]; subst; reflexivity).
  all: try reflexivity.
  all: try (exfalso; exact (raw_codeList1_neq_codeList2
      M hPA hnode _ _ _ hcode)).
  all: try (exfalso; exact (raw_codeList1_neq_codeList2
      M hPA hnode _ _ _ (eq_sym hcode))).
  all: try (exfalso; exact (raw_codeList2_neq_codeList3
      M hPA hnode _ _ _ _ _ hcode)).
  all: try (exfalso; exact (raw_codeList2_neq_codeList3
      M hPA hnode _ _ _ _ _ (eq_sym hcode))).
  all: try (exfalso; exact (raw_codeList1_neq_codeList3_traversal
      M hPA hnode _ _ _ _ hcode)).
  all: try (exfalso; exact (raw_codeList1_neq_codeList3_traversal
      M hPA hnode _ _ _ _ (eq_sym hcode))).
  all: try (pose proof (rawNumeralValue_injective M hPA _ _
      (proj1 (raw_codeList3_injective M hnode
        _ _ _ _ _ _ hcode))) as htag;
    discriminate).
  all: pose proof (rawNumeralValue_injective M hPA _ _
      (proj1 (raw_codeList2_injective M hnode
        _ _ _ _ hcode))) as htag;
    discriminate.
Qed.

Definition rawQuotedFormulaShape (M : RawPAModel) (phi : formula)
    : RawCodedFormulaShape M :=
  match phi with
  | pEq leftTerm rightTerm =>
      rawShapeEq (rawQuotedTermCode M leftTerm)
        (rawQuotedTermCode M rightTerm)
  | pBot => rawShapeBot
  | pImp leftFormula rightFormula =>
      rawShapeImp (rawQuotedFormulaCode M leftFormula)
        (rawQuotedFormulaCode M rightFormula)
  | pAnd leftFormula rightFormula =>
      rawShapeAnd (rawQuotedFormulaCode M leftFormula)
        (rawQuotedFormulaCode M rightFormula)
  | pOr leftFormula rightFormula =>
      rawShapeOr (rawQuotedFormulaCode M leftFormula)
        (rawQuotedFormulaCode M rightFormula)
  | pAll child => rawShapeAll (rawQuotedFormulaCode M child)
  | pEx child => rawShapeEx (rawQuotedFormulaCode M child)
  end.

Lemma rawQuotedFormulaShape_code : forall (M : RawPAModel) phi,
  rawCodedFormulaShapeCode M (rawQuotedFormulaShape M phi) =
  rawQuotedFormulaCode M phi.
Proof. intros M phi. destruct phi; reflexivity. Qed.

(** An earlier row of a traversal is itself a public rank witness.  The
    successor prefix is important: it keeps exactly the row in question and
    all rows on which that row may depend. *)
Corollary raw_codedFormulaRank_of_traversal_row : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi,
  RawCodedFormulaRankTraversal M
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi ->
  forall index code rowSigma rowPi,
    rawLt M index bound ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code rowSigma rowPi ->
    RawCodedFormulaRank M code rowSigma rowPi.
Proof.
  intros M hPA formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal
    index code rowSigma rowPi hindex hlookup.
  exists formulaCode, formulaStep, sigmaCode, sigmaStep, piCode, piStep,
    (raw_succ M index), index.
  exact (raw_codedFormulaRankTraversal_restrict_to_row M hPA
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep
    bound rootIndex root sigma pi htraversal
    index code rowSigma rowPi hindex hlookup).
Qed.

(** Canonical numeral instances of the five nontrivial rank equations. *)
Lemma raw_formulaRankImp_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall leftSigma leftPi rightSigma rightPi,
  RawFormulaRankImp M
    (rawNumeralValue M (Nat.max leftPi rightSigma))
    (rawNumeralValue M (Nat.max leftSigma rightPi))
    (rawNumeralValue M leftSigma) (rawNumeralValue M leftPi)
    (rawNumeralValue M rightSigma) (rawNumeralValue M rightPi).
Proof.
  intros M hPA leftSigma leftPi rightSigma rightPi. split;
    apply RawMax_numerals; exact hPA.
Qed.

Lemma raw_formulaRankAndOr_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall leftSigma leftPi rightSigma rightPi,
  RawFormulaRankAndOr M
    (rawNumeralValue M (Nat.max leftSigma rightSigma))
    (rawNumeralValue M (Nat.max leftPi rightPi))
    (rawNumeralValue M leftSigma) (rawNumeralValue M leftPi)
    (rawNumeralValue M rightSigma) (rawNumeralValue M rightPi).
Proof.
  intros M hPA leftSigma leftPi rightSigma rightPi. split;
    apply RawMax_numerals; exact hPA.
Qed.

Lemma raw_formulaRankAll_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall childSigma childPi,
  RawFormulaRankAll M
    (rawNumeralValue M (S (Nat.max 1 childPi)))
    (rawNumeralValue M (Nat.max 1 childPi))
    (rawNumeralValue M childSigma) (rawNumeralValue M childPi).
Proof.
  intros M hPA childSigma childPi.
  exists (rawNumeralValue M (Nat.max 1 childPi)).
  split; [apply RawMax_numerals; exact hPA |].
  split; reflexivity.
Qed.

Lemma raw_formulaRankEx_numerals : forall (M : RawPAModel),
  RawPASatisfies M -> forall childSigma childPi,
  RawFormulaRankEx M
    (rawNumeralValue M (Nat.max 1 childSigma))
    (rawNumeralValue M (S (Nat.max 1 childSigma)))
    (rawNumeralValue M childSigma) (rawNumeralValue M childPi).
Proof.
  intros M hPA childSigma childPi.
  exists (rawNumeralValue M (Nat.max 1 childSigma)).
  split; [apply RawMax_numerals; exact hPA |].
  split; reflexivity.
Qed.

(** Every certificate whose root is an externally quoted formula computes
    exactly the meta-level mutually recursive hierarchy ranks.  This is a
    soundness theorem, not a totality claim: it applies to any supplied
    beta-coded traversal, including one living in a nonstandard PA model. *)
Theorem raw_codedFormulaRank_standard_sound :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall phi sigma pi,
    RawCodedFormulaRank M (rawQuotedFormulaCode M phi) sigma pi ->
    sigma = rawNumeralValue M (sigmaRank phi) /\
    pi = rawNumeralValue M (piRank phi).
Proof.
  intros hpairProof M hPA phi.
  induction phi as
      [leftTerm rightTerm
      | (* bottom *)
      | leftFormula IHleft rightFormula IHright
      | leftFormula IHleft rightFormula IHright
      | leftFormula IHleft rightFormula IHright
      | child IHchild
      | child IHchild];
    intros sigma pi
      (formulaCode & formulaStep & sigmaCode & sigmaStep &
       piCode & piStep & bound & rootIndex & htraversal).
  all: pose proof
    (raw_codedFormulaRankTraversal_root_row M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound rootIndex
      _ sigma pi htraversal) as hrow.
  all: apply raw_codedFormulaRankTraversalRow_shape_iff in hrow.
  all: destruct hrow as [shape [hshapeCode hshapeRank]].
  all: match goal with
  | hshapeCode : rawQuotedFormulaCode ?model ?thisFormula =
      rawCodedFormulaShapeCode ?model ?thisShape |- _ =>
      assert (hshape : thisShape = rawQuotedFormulaShape model thisFormula) by
        (apply (rawCodedFormulaShapeCode_injective hpairProof model hPA);
         rewrite rawQuotedFormulaShape_code; symmetry; exact hshapeCode)
  end.
  all: subst shape;
    cbn [rawQuotedFormulaShape RawCodedFormulaShapeRankRow] in hshapeRank.
  - exact hshapeRank.
  - exact hshapeRank.
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    pose proof htraversal as htraversalFacts.
    destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
    assert (hleftBound : rawLt M leftIndex bound).
    { exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound). }
    assert (hrightBound : rawLt M rightIndex bound).
    { exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound). }
    destruct (IHleft leftSigma leftPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pImp leftFormula rightFormula))
        sigma pi htraversal leftIndex
        (rawQuotedFormulaCode M leftFormula) leftSigma leftPi
        hleftBound hleftLookup)) as [hleftSigma hleftPi].
    destruct (IHright rightSigma rightPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pImp leftFormula rightFormula))
        sigma pi htraversal rightIndex
        (rawQuotedFormulaCode M rightFormula) rightSigma rightPi
        hrightBound hrightLookup)) as [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrank.
    exact (raw_formulaRankImp_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrank
      (raw_formulaRankImp_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    pose proof htraversal as htraversalFacts.
    destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
    assert (hleftBound : rawLt M leftIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound).
    assert (hrightBound : rawLt M rightIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound).
    destruct (IHleft leftSigma leftPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pAnd leftFormula rightFormula))
        sigma pi htraversal leftIndex
        (rawQuotedFormulaCode M leftFormula) leftSigma leftPi
        hleftBound hleftLookup)) as [hleftSigma hleftPi].
    destruct (IHright rightSigma rightPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pAnd leftFormula rightFormula))
        sigma pi htraversal rightIndex
        (rawQuotedFormulaCode M rightFormula) rightSigma rightPi
        hrightBound hrightLookup)) as [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrank.
    exact (raw_formulaRankAndOr_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrank
      (raw_formulaRankAndOr_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct hshapeRank as
      (leftIndex & leftSigma & leftPi & rightIndex & rightSigma & rightPi &
       hleftIndex & hleftLookup & hrightIndex & hrightLookup & hrank).
    pose proof htraversal as htraversalFacts.
    destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
    assert (hleftBound : rawLt M leftIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        leftIndex rootIndex bound hleftIndex hrootBound).
    assert (hrightBound : rawLt M rightIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        rightIndex rootIndex bound hrightIndex hrootBound).
    destruct (IHleft leftSigma leftPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pOr leftFormula rightFormula))
        sigma pi htraversal leftIndex
        (rawQuotedFormulaCode M leftFormula) leftSigma leftPi
        hleftBound hleftLookup)) as [hleftSigma hleftPi].
    destruct (IHright rightSigma rightPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pOr leftFormula rightFormula))
        sigma pi htraversal rightIndex
        (rawQuotedFormulaCode M rightFormula) rightSigma rightPi
        hrightBound hrightLookup)) as [hrightSigma hrightPi].
    rewrite hleftSigma, hleftPi, hrightSigma, hrightPi in hrank.
    exact (raw_formulaRankAndOr_functional M hPA
      sigma pi
      (rawNumeralValue M
        (Nat.max (sigmaRank leftFormula) (sigmaRank rightFormula)))
      (rawNumeralValue M
        (Nat.max (piRank leftFormula) (piRank rightFormula)))
      (rawNumeralValue M (sigmaRank leftFormula))
      (rawNumeralValue M (piRank leftFormula))
      (rawNumeralValue M (sigmaRank rightFormula))
      (rawNumeralValue M (piRank rightFormula))
      hrank
      (raw_formulaRankAndOr_numerals M hPA
        (sigmaRank leftFormula) (piRank leftFormula)
        (sigmaRank rightFormula) (piRank rightFormula))).
  - destruct hshapeRank as
      (childIndex & childSigma & childPi & hchildIndex & hchildLookup & hrank).
    pose proof htraversal as htraversalFacts.
    destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
    assert (hchildBound : rawLt M childIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        childIndex rootIndex bound hchildIndex hrootBound).
    destruct (IHchild childSigma childPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pAll child))
        sigma pi htraversal childIndex
        (rawQuotedFormulaCode M child) childSigma childPi
        hchildBound hchildLookup)) as [hchildSigma hchildPi].
    rewrite hchildSigma, hchildPi in hrank.
    exact (raw_formulaRankAll_functional M hPA
      sigma pi
      (rawNumeralValue M (S (Nat.max 1 (piRank child))))
      (rawNumeralValue M (Nat.max 1 (piRank child)))
      (rawNumeralValue M (sigmaRank child))
      (rawNumeralValue M (piRank child))
      hrank
      (raw_formulaRankAll_numerals M hPA
        (sigmaRank child) (piRank child))).
  - destruct hshapeRank as
      (childIndex & childSigma & childPi & hchildIndex & hchildLookup & hrank).
    pose proof htraversal as htraversalFacts.
    destruct htraversalFacts as [_ [_ [_ [hrootBound _]]]].
    assert (hchildBound : rawLt M childIndex bound) by
      exact (raw_assignment_lt_trans M hPA
        childIndex rootIndex bound hchildIndex hrootBound).
    destruct (IHchild childSigma childPi
      (raw_codedFormulaRank_of_traversal_row M hPA
        formulaCode formulaStep sigmaCode sigmaStep piCode piStep
        bound rootIndex (rawQuotedFormulaCode M (pEx child))
        sigma pi htraversal childIndex
        (rawQuotedFormulaCode M child) childSigma childPi
        hchildBound hchildLookup)) as [hchildSigma hchildPi].
    rewrite hchildSigma, hchildPi in hrank.
    exact (raw_formulaRankEx_functional M hPA
      sigma pi
      (rawNumeralValue M (Nat.max 1 (sigmaRank child)))
      (rawNumeralValue M (S (Nat.max 1 (sigmaRank child))))
      (rawNumeralValue M (sigmaRank child))
      (rawNumeralValue M (piRank child))
      hrank
      (raw_formulaRankEx_numerals M hPA
        (sigmaRank child) (piRank child))).
Qed.

(** Consequently, different traversal witnesses cannot disagree on the rank
    of a standard quotation.  This is the strongest unconditional
    cross-certificate functionality available here; the corresponding claim
    for an arbitrary nonstandard root is kept as an explicit seam below. *)
Corollary raw_codedFormulaRank_standard_functional :
  PolynomialPairInjectivityProof ->
  forall (M : RawPAModel), RawPASatisfies M ->
  forall phi sigma pi sigma' pi',
    RawCodedFormulaRank M (rawQuotedFormulaCode M phi) sigma pi ->
    RawCodedFormulaRank M (rawQuotedFormulaCode M phi) sigma' pi' ->
    sigma = sigma' /\ pi = pi'.
Proof.
  intros hpairProof M hPA phi sigma pi sigma' pi' hrank hrank'.
  destruct (raw_codedFormulaRank_standard_sound hpairProof M hPA
    phi sigma pi hrank) as [hsigma hpi].
  destruct (raw_codedFormulaRank_standard_sound hpairProof M hPA
    phi sigma' pi' hrank') as [hsigma' hpi'].
  split; congruence.
Qed.

(** Exact named seams.  The relation and all theorems above are unconditional;
    what remains for arbitrary nonstandard syntax is to construct a traversal
    and to prove that outputs from different traversal witnesses agree. *)
Definition RawCodedFormulaRankTotal (M : RawPAModel) : Prop :=
  forall root : M, exists sigma pi : M,
    RawCodedFormulaRank M root sigma pi.

Definition RawCodedFormulaRankFunctional (M : RawPAModel) : Prop :=
  forall root sigma pi sigma' pi' : M,
    RawCodedFormulaRank M root sigma pi ->
    RawCodedFormulaRank M root sigma' pi' ->
    sigma = sigma' /\ pi = pi'.

Arguments RawCodedFormulaRankTotal M : clear implicits.
Arguments RawCodedFormulaRankFunctional M : clear implicits.

Theorem raw_codedFormulaRank_exists_unique_of_total_functional : forall
    (M : RawPAModel),
  RawCodedFormulaRankTotal M ->
  RawCodedFormulaRankFunctional M ->
  forall root : M,
  exists sigma pi : M,
    RawCodedFormulaRank M root sigma pi /\
    forall sigma' pi',
      RawCodedFormulaRank M root sigma' pi' ->
      sigma = sigma' /\ pi = pi'.
Proof.
  intros M htotal hfunctional root.
  destruct (htotal root) as [sigma [pi hrank]].
  exists sigma, pi. split; [exact hrank |].
  intros sigma' pi' hrank'.
  exact (hfunctional root sigma pi sigma' pi' hrank hrank').
Qed.

End PABoundedRawCodedFormulaRankTraversal.
