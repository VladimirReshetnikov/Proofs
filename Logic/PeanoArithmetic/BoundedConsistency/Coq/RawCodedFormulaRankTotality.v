(**
  Realization of hierarchy ranks from model-internal formula syntax traces.

  The public rank graph in [RawCodedFormulaRankTraversal] deliberately does
  not claim totality on every element of a nonstandard PA model: malformed
  carrier elements are not formula codes.  This file supplies the missing
  honest domain.  A formula-syntax traversal is one beta-coded postorder
  list whose atomic equality payloads are arbitrary term codes and whose
  recursive formula children occur at strictly earlier rows.

  Starting from such a traversal, PA induction constructs two synchronized
  beta tables of Sigma and Pi ranks.  The construction is internal even when
  the traversal bound is nonstandard: Coq never recurses over a carrier
  element.  One-entry CRT extension is used at the successor step.  The rank
  bound at row [i] is [S i], which is exactly strong enough for quantifiers
  and supplies the modulus bound needed by CRT.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFOrdinalCodeTotalInduction.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness PolynomialPairInjectivity RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedFormulaRankStep
  RawCodedFormulaRankTraversal RawCodedFormulaRankRealization.

Import ListNotations.

Module PABoundedRawCodedFormulaRankTotality.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaRankTraversal.
Import PABoundedRawCodedFormulaRankRealization.

(** ------------------------------------------------------------------
    A genuine PA formula for one postorder syntax row. *)

Definition syntaxTraversalEx2 (body : formula) : formula :=
  pEx (pEx body).

Definition syntaxTraversalEx4 (body : formula) : formula :=
  pEx (pEx (pEx (pEx body))).

Definition codedFormulaEqSyntaxRowTermAt (code : term) : formula :=
  syntaxTraversalEx2
    (formulaEqCodeTermAt (liftTerm 2 code) (tVar 1) (tVar 0)).

Definition codedFormulaBotSyntaxRowTermAt (code : term) : formula :=
  formulaBotCodeTermAt code.

(** The four witnesses are, from outermost to innermost, the left row and
    code followed by the right row and code.  At the body they occupy
    variables 3,2,1,0. *)
Definition codedFormulaBinarySyntaxRowTermAt
    (constructor : term -> term -> term -> formula)
    (formulaCode formulaStep index code : term) : formula :=
  syntaxTraversalEx4 (rankTraversalAnd5
    (Formula.ltTermAt (tVar 3) (liftTerm 4 index))
    (codedAssignmentLookupTermAt
      (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
      (tVar 3) (tVar 2))
    (Formula.ltTermAt (tVar 1) (liftTerm 4 index))
    (codedAssignmentLookupTermAt
      (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
      (tVar 1) (tVar 0))
    (constructor (liftTerm 4 code) (tVar 2) (tVar 0))).

Definition codedFormulaUnarySyntaxRowTermAt
    (constructor : term -> term -> formula)
    (formulaCode formulaStep index code : term) : formula :=
  syntaxTraversalEx2 (rankTraversalAnd3
    (Formula.ltTermAt (tVar 1) (liftTerm 2 index))
    (codedAssignmentLookupTermAt
      (liftTerm 2 formulaCode) (liftTerm 2 formulaStep)
      (tVar 1) (tVar 0))
    (constructor (liftTerm 2 code) (tVar 0))).

Definition codedFormulaSyntaxTraversalRowTermAt
    (formulaCode formulaStep index code : term) : formula :=
  pOr (codedFormulaEqSyntaxRowTermAt code)
  (pOr (codedFormulaBotSyntaxRowTermAt code)
  (pOr (codedFormulaBinarySyntaxRowTermAt formulaImpCodeTermAt
      formulaCode formulaStep index code)
  (pOr (codedFormulaBinarySyntaxRowTermAt formulaAndCodeTermAt
      formulaCode formulaStep index code)
  (pOr (codedFormulaBinarySyntaxRowTermAt formulaOrCodeTermAt
      formulaCode formulaStep index code)
  (pOr (codedFormulaUnarySyntaxRowTermAt formulaAllCodeTermAt
      formulaCode formulaStep index code)
    (codedFormulaUnarySyntaxRowTermAt formulaExCodeTermAt
      formulaCode formulaStep index code)))))).

Definition RawCodedFormulaEqSyntaxRow (M : RawPAModel)
    (code : M) : Prop :=
  exists left right : M, code = rawFormulaEqCode M left right.

Definition RawCodedFormulaBinarySyntaxRow (M : RawPAModel)
    (constructor : M -> M -> M)
    (formulaCode formulaStep index code : M) : Prop :=
  exists leftIndex left rightIndex right : M,
    rawLt M leftIndex index /\
    RawCodedAssignmentLookup M formulaCode formulaStep leftIndex left /\
    rawLt M rightIndex index /\
    RawCodedAssignmentLookup M formulaCode formulaStep rightIndex right /\
    code = constructor left right.

Definition RawCodedFormulaUnarySyntaxRow (M : RawPAModel)
    (constructor : M -> M)
    (formulaCode formulaStep index code : M) : Prop :=
  exists childIndex child : M,
    rawLt M childIndex index /\
    RawCodedAssignmentLookup M formulaCode formulaStep childIndex child /\
    code = constructor child.

Definition RawCodedFormulaSyntaxTraversalRow (M : RawPAModel)
    (formulaCode formulaStep index code : M) : Prop :=
  RawCodedFormulaEqSyntaxRow M code \/
  code = rawFormulaBotCode M \/
  RawCodedFormulaBinarySyntaxRow M (rawFormulaImpCode M)
    formulaCode formulaStep index code \/
  RawCodedFormulaBinarySyntaxRow M (rawFormulaAndCode M)
    formulaCode formulaStep index code \/
  RawCodedFormulaBinarySyntaxRow M (rawFormulaOrCode M)
    formulaCode formulaStep index code \/
  RawCodedFormulaUnarySyntaxRow M (rawFormulaAllCode M)
    formulaCode formulaStep index code \/
  RawCodedFormulaUnarySyntaxRow M (rawFormulaExCode M)
    formulaCode formulaStep index code.

Arguments RawCodedFormulaSyntaxTraversalRow
  M formulaCode formulaStep index code : clear implicits.

Lemma raw_sat_codedFormulaEqSyntaxRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code,
  raw_formula_sat M e (codedFormulaEqSyntaxRowTermAt code) <->
  RawCodedFormulaEqSyntaxRow M (raw_term_eval M e code).
Proof.
  intros M e code.
  unfold codedFormulaEqSyntaxRowTermAt, syntaxTraversalEx2,
    RawCodedFormulaEqSyntaxRow.
  cbn [raw_formula_sat]. split.
  - intros [left [right h]]. exists left, right.
    apply (proj1 (raw_sat_formulaEqCodeTermAt_iff M
      (scons M right (scons M left e)) _ _ _)) in h.
    rewrite raw_rankTraversal_eval_liftTerm_two in h.
    cbn [raw_term_eval scons] in h. exact h.
  - intros [left [right h]]. exists left, right.
    apply (proj2 (raw_sat_formulaEqCodeTermAt_iff M
      (scons M right (scons M left e)) _ _ _)).
    rewrite raw_rankTraversal_eval_liftTerm_two.
    cbn [raw_term_eval scons]. exact h.
Qed.

Lemma raw_sat_codedFormulaBotSyntaxRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) code,
  raw_formula_sat M e (codedFormulaBotSyntaxRowTermAt code) <->
  raw_term_eval M e code = rawFormulaBotCode M.
Proof.
  intros. unfold codedFormulaBotSyntaxRowTermAt.
  apply raw_sat_formulaBotCodeTermAt_iff.
Qed.

(** The semantic proof for all three binary constructors is factored over
    their formula/raw interpretations. *)
Lemma raw_sat_codedFormulaBinarySyntaxRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    (constructor : term -> term -> term -> formula)
    (rawConstructor : M -> M -> M),
  (forall e' code left right,
    raw_formula_sat M e' (constructor code left right) <->
    raw_term_eval M e' code = rawConstructor
      (raw_term_eval M e' left) (raw_term_eval M e' right)) ->
  forall formulaCode formulaStep index code,
  raw_formula_sat M e
    (codedFormulaBinarySyntaxRowTermAt constructor
      formulaCode formulaStep index code) <->
  RawCodedFormulaBinarySyntaxRow M rawConstructor
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e index) (raw_term_eval M e code).
Proof.
  intros M e constructor rawConstructor hconstructor
    formulaCode formulaStep index code.
  unfold codedFormulaBinarySyntaxRowTermAt, syntaxTraversalEx4,
    rankTraversalAnd5, RawCodedFormulaBinarySyntaxRow.
  cbn [raw_formula_sat]. split.
  - intros (li & left & ri & right & hli & hleft & hri & hright & hcode).
    exists li, left, ri, right.
    split; [|split; [|split; [|split]]].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hli.
      rewrite raw_rankTraversal_eval_liftTerm_four in hli.
      cbn [raw_term_eval scons] in hli. exact hli.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff in hleft.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hleft.
      cbn [raw_term_eval scons] in hleft. exact hleft.
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hri.
      rewrite raw_rankTraversal_eval_liftTerm_four in hri.
      cbn [raw_term_eval scons] in hri. exact hri.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff in hright.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four in hright.
      cbn [raw_term_eval scons] in hright. exact hright.
    + apply (proj1 (hconstructor
        (scons M right (scons M ri (scons M left (scons M li e))))
        _ _ _)) in hcode.
      rewrite raw_rankTraversal_eval_liftTerm_four in hcode.
      cbn [raw_term_eval scons] in hcode. exact hcode.
  - intros (li & left & ri & right & hli & hleft & hri & hright & hcode).
    exists li, left, ri, right.
    split; [|split; [|split; [|split]]].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hli.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hleft.
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hri.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hright.
    + apply (proj2 (hconstructor
        (scons M right (scons M ri (scons M left (scons M li e))))
        _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_four.
      cbn [raw_term_eval scons]. exact hcode.
Qed.

Lemma raw_sat_codedFormulaUnarySyntaxRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    (constructor : term -> term -> formula)
    (rawConstructor : M -> M),
  (forall e' code child,
    raw_formula_sat M e' (constructor code child) <->
    raw_term_eval M e' code = rawConstructor (raw_term_eval M e' child)) ->
  forall formulaCode formulaStep index code,
  raw_formula_sat M e
    (codedFormulaUnarySyntaxRowTermAt constructor
      formulaCode formulaStep index code) <->
  RawCodedFormulaUnarySyntaxRow M rawConstructor
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e index) (raw_term_eval M e code).
Proof.
  intros M e constructor rawConstructor hconstructor
    formulaCode formulaStep index code.
  unfold codedFormulaUnarySyntaxRowTermAt, syntaxTraversalEx2,
    rankTraversalAnd3, RawCodedFormulaUnarySyntaxRow.
  cbn [raw_formula_sat]. split.
  - intros (ci & child & hci & hchild & hcode).
    exists ci, child. split; [|split].
    + apply (proj1 (raw_sat_ltTermAt_iff M _ _ _)) in hci.
      rewrite raw_rankTraversal_eval_liftTerm_two in hci.
      cbn [raw_term_eval scons] in hci. exact hci.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff in hchild.
      repeat rewrite raw_rankTraversal_eval_liftTerm_two in hchild.
      cbn [raw_term_eval scons] in hchild. exact hchild.
    + apply (proj1 (hconstructor
        (scons M child (scons M ci e)) _ _)) in hcode.
      rewrite raw_rankTraversal_eval_liftTerm_two in hcode.
      cbn [raw_term_eval scons] in hcode. exact hcode.
  - intros (ci & child & hci & hchild & hcode).
    exists ci, child. split; [|split].
    + apply (proj2 (raw_sat_ltTermAt_iff M _ _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hci.
    + rewrite raw_sat_codedAssignmentLookupTermAt_iff.
      repeat rewrite raw_rankTraversal_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hchild.
    + apply (proj2 (hconstructor
        (scons M child (scons M ci e)) _ _)).
      rewrite raw_rankTraversal_eval_liftTerm_two.
      cbn [raw_term_eval scons]. exact hcode.
Qed.

Theorem raw_sat_codedFormulaSyntaxTraversalRowTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep index code,
  raw_formula_sat M e
    (codedFormulaSyntaxTraversalRowTermAt
      formulaCode formulaStep index code) <->
  RawCodedFormulaSyntaxTraversalRow M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e index) (raw_term_eval M e code).
Proof.
  intros M e formulaCode formulaStep index code.
  unfold codedFormulaSyntaxTraversalRowTermAt,
    RawCodedFormulaSyntaxTraversalRow.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedFormulaEqSyntaxRowTermAt_iff.
  rewrite raw_sat_codedFormulaBotSyntaxRowTermAt_iff.
  rewrite (raw_sat_codedFormulaBinarySyntaxRowTermAt_iff M e
    formulaImpCodeTermAt (rawFormulaImpCode M)
    (raw_sat_formulaImpCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBinarySyntaxRowTermAt_iff M e
    formulaAndCodeTermAt (rawFormulaAndCode M)
    (raw_sat_formulaAndCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaBinarySyntaxRowTermAt_iff M e
    formulaOrCodeTermAt (rawFormulaOrCode M)
    (raw_sat_formulaOrCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaUnarySyntaxRowTermAt_iff M e
    formulaAllCodeTermAt (rawFormulaAllCode M)
    (raw_sat_formulaAllCodeTermAt_iff M)).
  rewrite (raw_sat_codedFormulaUnarySyntaxRowTermAt_iff M e
    formulaExCodeTermAt (rawFormulaExCode M)
    (raw_sat_formulaExCodeTermAt_iff M)).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    The global syntax certificate and its exact raw semantics. *)

Definition codedFormulaSyntaxTraversalRowsTermAt
    (formulaCode formulaStep bound : term) : formula :=
  pAll (pAll (pImp
    (Formula.ltTermAt (tVar 1) (liftTerm 2 bound))
    (pImp
      (codedAssignmentLookupTermAt
        (liftTerm 2 formulaCode) (liftTerm 2 formulaStep)
        (tVar 1) (tVar 0))
      (codedFormulaSyntaxTraversalRowTermAt
        (liftTerm 2 formulaCode) (liftTerm 2 formulaStep)
        (tVar 1) (tVar 0))))).

Definition RawCodedFormulaSyntaxTraversalRows (M : RawPAModel)
    (formulaCode formulaStep bound : M) : Prop :=
  forall index code : M,
    rawLt M index bound ->
    RawCodedAssignmentLookup M formulaCode formulaStep index code ->
    RawCodedFormulaSyntaxTraversalRow M
      formulaCode formulaStep index code.

Arguments RawCodedFormulaSyntaxTraversalRows
  M formulaCode formulaStep bound : clear implicits.

Lemma raw_sat_codedFormulaSyntaxTraversalRowsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) formulaCode formulaStep bound,
  raw_formula_sat M e
    (codedFormulaSyntaxTraversalRowsTermAt formulaCode formulaStep bound) <->
  RawCodedFormulaSyntaxTraversalRows M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e bound).
Proof.
  intros M e formulaCode formulaStep bound.
  unfold codedFormulaSyntaxTraversalRowsTermAt,
    RawCodedFormulaSyntaxTraversalRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSyntaxTraversalRowTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Definition codedFormulaSyntaxTraversalTermAt
    (formulaCode formulaStep bound rootIndex root : term) : formula :=
  rankTraversalAnd4
    (codedAssignmentDefinedThroughTermAt formulaCode formulaStep bound)
    (Formula.ltTermAt rootIndex bound)
    (codedAssignmentLookupTermAt formulaCode formulaStep rootIndex root)
    (codedFormulaSyntaxTraversalRowsTermAt
      formulaCode formulaStep bound).

Definition RawCodedFormulaSyntaxTraversal (M : RawPAModel)
    (formulaCode formulaStep bound rootIndex root : M) : Prop :=
  RawCodedAssignmentDefinedThrough M formulaCode formulaStep bound /\
  rawLt M rootIndex bound /\
  RawCodedAssignmentLookup M formulaCode formulaStep rootIndex root /\
  RawCodedFormulaSyntaxTraversalRows M formulaCode formulaStep bound.

Arguments RawCodedFormulaSyntaxTraversal
  M formulaCode formulaStep bound rootIndex root : clear implicits.

Lemma raw_sat_codedFormulaSyntaxTraversalTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep bound rootIndex root,
  raw_formula_sat M e
    (codedFormulaSyntaxTraversalTermAt
      formulaCode formulaStep bound rootIndex root) <->
  RawCodedFormulaSyntaxTraversal M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e bound) (raw_term_eval M e rootIndex)
    (raw_term_eval M e root).
Proof.
  intros. unfold codedFormulaSyntaxTraversalTermAt,
    RawCodedFormulaSyntaxTraversal, rankTraversalAnd4.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  rewrite raw_sat_ltTermAt_iff.
  rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  rewrite raw_sat_codedFormulaSyntaxTraversalRowsTermAt_iff.
  reflexivity.
Qed.

Definition codedWellFormedFormulaTermAt (root : term) : formula :=
  pEx (pEx (pEx (pEx
    (codedFormulaSyntaxTraversalTermAt
      (tVar 3) (tVar 2) (tVar 1) (tVar 0) (liftTerm 4 root))))).

Definition RawCodedWellFormedFormula (M : RawPAModel) (root : M) : Prop :=
  exists formulaCode formulaStep bound rootIndex : M,
    RawCodedFormulaSyntaxTraversal M
      formulaCode formulaStep bound rootIndex root.

Arguments RawCodedWellFormedFormula M root : clear implicits.

Lemma raw_sat_codedWellFormedFormulaTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) root,
  raw_formula_sat M e (codedWellFormedFormulaTermAt root) <->
  RawCodedWellFormedFormula M (raw_term_eval M e root).
Proof.
  intros M e root.
  unfold codedWellFormedFormulaTermAt, RawCodedWellFormedFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedFormulaSyntaxTraversalTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    A definable prefix invariant for the rank-table construction. *)

Definition codedFormulaRankBoundRowsTermAt
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      bound : term) : formula :=
  pAll (pAll (pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 3) (liftTerm 4 bound))
      (pImp
        (codedFormulaRankTripleLookupTermAt
          (liftTerm 4 formulaCode) (liftTerm 4 formulaStep)
          (liftTerm 4 sigmaCode) (liftTerm 4 sigmaStep)
          (liftTerm 4 piCode) (liftTerm 4 piStep)
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (pAnd
          (Formula.leTermAt (tVar 1) (tSucc (tVar 3)))
          (Formula.leTermAt (tVar 0) (tSucc (tVar 3))))))))).

Definition RawCodedFormulaRankBoundRows (M : RawPAModel)
    (formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound : M)
    : Prop :=
  forall index code sigma pi : M,
    rawLt M index bound ->
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep
      index code sigma pi ->
    rawLe M sigma (raw_succ M index) /\
    rawLe M pi (raw_succ M index).

Arguments RawCodedFormulaRankBoundRows
  M formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound
  : clear implicits.

Lemma raw_sat_codedFormulaRankBoundRowsTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound,
  raw_formula_sat M e
    (codedFormulaRankBoundRowsTermAt
      formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound) <->
  RawCodedFormulaRankBoundRows M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e sigmaCode) (raw_term_eval M e sigmaStep)
    (raw_term_eval M e piCode) (raw_term_eval M e piStep)
    (raw_term_eval M e bound).
Proof.
  intros M e formulaCode formulaStep sigmaCode sigmaStep piCode piStep bound.
  unfold codedFormulaRankBoundRowsTermAt,
    RawCodedFormulaRankBoundRows.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTripleLookupTermAt_iff.
  setoid_rewrite raw_sat_leTermAt_iff_rank.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_four.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Only the two evolving table codes are existential.  Their common step is
    fixed before induction, so one CRT capacity works at every row. *)
Definition codedFormulaRankPrefixTermAt
    (formulaCode formulaStep rankStep current : term) : formula :=
  syntaxTraversalEx2 (rankTraversalAnd4
    (codedAssignmentDefinedThroughTermAt
      (tVar 1) (liftTerm 2 rankStep) (liftTerm 2 current))
    (codedAssignmentDefinedThroughTermAt
      (tVar 0) (liftTerm 2 rankStep) (liftTerm 2 current))
    (codedFormulaRankTraversalRowsTermAt
      (liftTerm 2 formulaCode) (liftTerm 2 formulaStep)
      (tVar 1) (liftTerm 2 rankStep)
      (tVar 0) (liftTerm 2 rankStep) (liftTerm 2 current))
    (codedFormulaRankBoundRowsTermAt
      (liftTerm 2 formulaCode) (liftTerm 2 formulaStep)
      (tVar 1) (liftTerm 2 rankStep)
      (tVar 0) (liftTerm 2 rankStep) (liftTerm 2 current))).

Definition RawCodedFormulaRankPrefix (M : RawPAModel)
    (formulaCode formulaStep rankStep current : M) : Prop :=
  exists sigmaCode piCode : M,
    RawCodedAssignmentDefinedThrough M sigmaCode rankStep current /\
    RawCodedAssignmentDefinedThrough M piCode rankStep current /\
    RawCodedFormulaRankTraversalRows M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep current /\
    RawCodedFormulaRankBoundRows M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep current.

Arguments RawCodedFormulaRankPrefix
  M formulaCode formulaStep rankStep current : clear implicits.

Lemma raw_sat_codedFormulaRankPrefixTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep rankStep current,
  raw_formula_sat M e
    (codedFormulaRankPrefixTermAt
      formulaCode formulaStep rankStep current) <->
  RawCodedFormulaRankPrefix M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e rankStep) (raw_term_eval M e current).
Proof.
  intros M e formulaCode formulaStep rankStep current.
  unfold codedFormulaRankPrefixTermAt, syntaxTraversalEx2,
    rankTraversalAnd4, RawCodedFormulaRankPrefix.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTraversalRowsTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankBoundRowsTermAt_iff.
  repeat setoid_rewrite raw_rankTraversal_eval_liftTerm_two.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** ------------------------------------------------------------------
    CRT capacity.  This is not an assumption: PA proves that a coding step
    exists above any requested capacity. *)

Definition RawFormulaRankCodingStep (M : RawPAModel)
    (bound step : M) : Prop :=
  RawCommonMultipleThrough M bound step /\
  rawLe M (raw_succ M bound) step.

Arguments RawFormulaRankCodingStep M bound step : clear implicits.

Lemma raw_sat_formulaRankCodingStepTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M) bound step,
  raw_formula_sat M e
    (Formula.betaCodingStepTermAt bound bound step) <->
  RawFormulaRankCodingStep M
    (raw_term_eval M e bound) (raw_term_eval M e step).
Proof.
  intros M e bound step.
  unfold Formula.betaCodingStepTermAt, RawFormulaRankCodingStep.
  cbn [raw_formula_sat].
  rewrite raw_sat_commonMultipleThroughTermAt_iff.
  rewrite raw_sat_leTermAt_iff_rank.
  reflexivity.
Qed.

Theorem raw_formulaRankCodingStep_exists : forall (M : RawPAModel),
  RawPASatisfies M -> forall bound : M,
  exists step : M, RawFormulaRankCodingStep M bound step.
Proof.
  intros M hPA bound.
  set (tail := fun _ : nat => raw_zero M).
  set (e := scons M bound tail).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (BProv_Ax_s_betaCodingStepExistsTermAt [] (tVar 0) (tVar 0)) e)
    as hsat.
  unfold Formula.betaCodingStepExistsTermAt in hsat.
  cbn [raw_formula_sat] in hsat.
  destruct hsat as [step hstep]. exists step.
  apply (proj1 (raw_sat_formulaRankCodingStepTermAt_iff M
    (scons M step e)
    (Term.rename S (tVar 0)) (tVar 0))).
  exact hstep.
Qed.

Lemma raw_rank_zero_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M (raw_zero M) x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_zero_left [] (tVar 0)) e) as hle.
  change (rawLe M (raw_zero M) x) in hle. exact hle.
Qed.

Lemma raw_rank_le_refl : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M, rawLe M x x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_sat_of_BProv_axs M _ hPA
    (Formula.BProv_Ax_s_leTermAt_refl [] (tVar 0)) e) as hle.
  change (rawLe M x x) in hle. exact hle.
Qed.

Lemma raw_rank_succ_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLe M x y -> rawLe M (raw_succ M x) (raw_succ M y).
Proof.
  intros M hPA x y [gap hgap]. exists gap.
  rewrite raw_succ_add_pair by exact hPA.
  now rewrite hgap.
Qed.

Lemma raw_rank_one_le_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  rawLe M (rawNumeralValue M 1) (raw_succ M x).
Proof.
  intros M hPA x.
  change (rawLe M (raw_succ M (raw_zero M)) (raw_succ M x)).
  apply raw_rank_succ_le; [exact hPA |].
  apply raw_rank_zero_le. exact hPA.
Qed.

Lemma raw_rank_max_exists_bounded : forall (M : RawPAModel),
  RawPASatisfies M -> forall left right upper : M,
  rawLe M left upper -> rawLe M right upper ->
  exists out : M, RawMax M out left right /\ rawLe M out upper.
Proof.
  intros M hPA left right upper hleft hright.
  destruct (raw_le_or_gt M hPA left right) as [hle | hgt].
  - exists right. split; [left; split; reflexivity || assumption |].
    exact hright.
  - exists left. split.
    + right. split; [exact (raw_lt_to_le M right left hgt) | reflexivity].
    + exact hleft.
Qed.

Definition RawFormulaRankTableCapacity (M : RawPAModel)
    (bound step : M) : Prop :=
  RawCommonMultipleThrough M bound step /\
  forall index value : M,
    rawLt M index bound ->
    rawLe M value (raw_succ M index) ->
    rawLt M value (rawBetaModulus M step index).

Arguments RawFormulaRankTableCapacity M bound step : clear implicits.

Theorem raw_formulaRankTableCapacity_of_codingStep : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound step,
  RawFormulaRankCodingStep M bound step ->
  RawFormulaRankTableCapacity M bound step.
Proof.
  intros M hPA bound step [hcommon hlarge]. split; [exact hcommon |].
  intros index value hindex hvalue.
  assert (hsuccIndexBound : rawLe M (raw_succ M index) bound).
  { exact (raw_succ_le_of_lt_pair M hPA index bound hindex). }
  assert (hvalueBound : rawLe M value bound).
  { exact (raw_le_trans M hPA value (raw_succ M index) bound
      hvalue hsuccIndexBound). }
  assert (hvalueSuccBound : rawLt M value (raw_succ M bound)).
  { exact (raw_lt_succ_of_le M hPA value bound hvalueBound). }
  assert (hvalueStep : rawLt M value step).
  { exact (raw_lt_le_trans_pair M hPA value (raw_succ M bound) step
      hvalueSuccBound hlarge). }
  assert (hstepProduct : rawLe M step
      (raw_mul M (raw_succ M index) step)).
  {
    exists (raw_mul M index step).
    rewrite raw_succ_mul by exact hPA.
    apply raw_add_comm. exact hPA.
  }
  assert (hstepModulus : rawLt M step
      (raw_succ M (raw_mul M (raw_succ M index) step))).
  { exact (raw_lt_succ_of_le M hPA _ _ hstepProduct). }
  unfold rawBetaModulus.
  exact (raw_assignment_lt_trans M hPA value step _
    hvalueStep hstepModulus).
Qed.

Corollary raw_formulaRankTableCapacity_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall bound : M,
  exists step : M, RawFormulaRankTableCapacity M bound step.
Proof.
  intros M hPA bound.
  destruct (raw_formulaRankCodingStep_exists M hPA bound)
    as [step hstep].
  exists step.
  exact (raw_formulaRankTableCapacity_of_codingStep M hPA
    bound step hstep).
Qed.

(** ------------------------------------------------------------------
    Local realization and the [S i] rank bound. *)

Lemma raw_rank_child_values : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode rankStep piCode current,
  RawCodedAssignmentDefinedThrough M sigmaCode rankStep current ->
  RawCodedAssignmentDefinedThrough M piCode rankStep current ->
  RawCodedFormulaRankBoundRows M
    formulaCode formulaStep sigmaCode rankStep piCode rankStep current ->
  forall childIndex child,
  rawLt M childIndex current ->
  RawCodedAssignmentLookup M
    formulaCode formulaStep childIndex child ->
  exists childSigma childPi,
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep
      childIndex child childSigma childPi /\
    rawLe M childSigma (raw_succ M childIndex) /\
    rawLe M childPi (raw_succ M childIndex).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode rankStep piCode current
    hsigmaDefined hpiDefined hbounds childIndex child hchild hformula.
  destruct (hsigmaDefined childIndex hchild) as [childSigma hsigma].
  destruct (hpiDefined childIndex hchild) as [childPi hpi].
  assert (hlookup : RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep
      childIndex child childSigma childPi).
  { repeat split; assumption. }
  destruct (hbounds childIndex child childSigma childPi hchild hlookup)
    as [hsigmaBound hpiBound].
  exists childSigma, childPi. repeat split; assumption.
Qed.

Theorem raw_formulaSyntaxRow_rank_exists_bounded : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep sigmaCode rankStep piCode current code,
  RawCodedAssignmentDefinedThrough M sigmaCode rankStep current ->
  RawCodedAssignmentDefinedThrough M piCode rankStep current ->
  RawCodedFormulaRankBoundRows M
    formulaCode formulaStep sigmaCode rankStep piCode rankStep current ->
  RawCodedFormulaSyntaxTraversalRow M
    formulaCode formulaStep current code ->
  exists sigma pi,
    RawCodedFormulaRankTraversalRow M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep
      current code sigma pi /\
    rawLe M sigma (raw_succ M current) /\
    rawLe M pi (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep sigmaCode rankStep piCode
    current code hsigmaDefined hpiDefined hbounds hsyntax.
  assert (hcurrentSucc : rawLe M current (raw_succ M current)).
  { exact (raw_lt_to_le M current (raw_succ M current)
      (raw_assignment_lt_self_succ M hPA current)). }
  destruct hsyntax as
    [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - destruct heq as [left [right hcode]].
    exists (raw_zero M), (raw_zero M). split.
    + left. exists left, right. split; [exact hcode |].
      split; reflexivity.
    + split; apply raw_rank_zero_le; exact hPA.
  - exists (raw_zero M), (raw_zero M). split.
    + right. left. split; [exact hbot |]. split; reflexivity.
    + split; apply raw_rank_zero_le; exact hPA.
  - destruct himp as
      (li & left & ri & right & hli & hleft & hri & hright & hcode).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds li left hli hleft)
      as (ls & lp & hleftTriple & hls & hlp).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds ri right hri hright)
      as (rs & rp & hrightTriple & hrs & hrp).
    assert (hliCurrent : rawLe M (raw_succ M li) current).
    { exact (raw_succ_le_of_lt_pair M hPA li current hli). }
    assert (hriCurrent : rawLe M (raw_succ M ri) current).
    { exact (raw_succ_le_of_lt_pair M hPA ri current hri). }
    assert (hlsCurrent : rawLe M ls current).
    { exact (raw_le_trans M hPA _ _ _ hls hliCurrent). }
    assert (hlpCurrent : rawLe M lp current).
    { exact (raw_le_trans M hPA _ _ _ hlp hliCurrent). }
    assert (hrsCurrent : rawLe M rs current).
    { exact (raw_le_trans M hPA _ _ _ hrs hriCurrent). }
    assert (hrpCurrent : rawLe M rp current).
    { exact (raw_le_trans M hPA _ _ _ hrp hriCurrent). }
    destruct (raw_rank_max_exists_bounded M hPA lp rs current
      hlpCurrent hrsCurrent) as [sigma [hsigmaRank hsigmaBound]].
    destruct (raw_rank_max_exists_bounded M hPA ls rp current
      hlsCurrent hrpCurrent) as [pi [hpiRank hpiBound]].
    exists sigma, pi. split.
    + right. right. left.
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleftTriple |].
      split; [exact hri |].
      split; [exact hrightTriple |].
      split; [exact hcode |].
      split; assumption.
    + split.
      * exact (raw_le_trans M hPA _ _ _ hsigmaBound hcurrentSucc).
      * exact (raw_le_trans M hPA _ _ _ hpiBound hcurrentSucc).
  - destruct hand as
      (li & left & ri & right & hli & hleft & hri & hright & hcode).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds li left hli hleft)
      as (ls & lp & hleftTriple & hls & hlp).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds ri right hri hright)
      as (rs & rp & hrightTriple & hrs & hrp).
    assert (hliCurrent := raw_succ_le_of_lt_pair M hPA li current hli).
    assert (hriCurrent := raw_succ_le_of_lt_pair M hPA ri current hri).
    assert (hlsCurrent := raw_le_trans M hPA _ _ _ hls hliCurrent).
    assert (hlpCurrent := raw_le_trans M hPA _ _ _ hlp hliCurrent).
    assert (hrsCurrent := raw_le_trans M hPA _ _ _ hrs hriCurrent).
    assert (hrpCurrent := raw_le_trans M hPA _ _ _ hrp hriCurrent).
    destruct (raw_rank_max_exists_bounded M hPA ls rs current
      hlsCurrent hrsCurrent) as [sigma [hsigmaRank hsigmaBound]].
    destruct (raw_rank_max_exists_bounded M hPA lp rp current
      hlpCurrent hrpCurrent) as [pi [hpiRank hpiBound]].
    exists sigma, pi. split.
    + right. right. right. left.
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleftTriple |].
      split; [exact hri |].
      split; [exact hrightTriple |].
      split; [exact hcode |].
      split; assumption.
    + split.
      * exact (raw_le_trans M hPA _ _ _ hsigmaBound hcurrentSucc).
      * exact (raw_le_trans M hPA _ _ _ hpiBound hcurrentSucc).
  - destruct hor as
      (li & left & ri & right & hli & hleft & hri & hright & hcode).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds li left hli hleft)
      as (ls & lp & hleftTriple & hls & hlp).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds ri right hri hright)
      as (rs & rp & hrightTriple & hrs & hrp).
    assert (hliCurrent := raw_succ_le_of_lt_pair M hPA li current hli).
    assert (hriCurrent := raw_succ_le_of_lt_pair M hPA ri current hri).
    assert (hlsCurrent := raw_le_trans M hPA _ _ _ hls hliCurrent).
    assert (hlpCurrent := raw_le_trans M hPA _ _ _ hlp hliCurrent).
    assert (hrsCurrent := raw_le_trans M hPA _ _ _ hrs hriCurrent).
    assert (hrpCurrent := raw_le_trans M hPA _ _ _ hrp hriCurrent).
    destruct (raw_rank_max_exists_bounded M hPA ls rs current
      hlsCurrent hrsCurrent) as [sigma [hsigmaRank hsigmaBound]].
    destruct (raw_rank_max_exists_bounded M hPA lp rp current
      hlpCurrent hrpCurrent) as [pi [hpiRank hpiBound]].
    exists sigma, pi. split.
    + right. right. right. right. left.
      exists li, left, ls, lp, ri, right, rs, rp.
      split; [exact hli |].
      split; [exact hleftTriple |].
      split; [exact hri |].
      split; [exact hrightTriple |].
      split; [exact hcode |].
      split; assumption.
    + split.
      * exact (raw_le_trans M hPA _ _ _ hsigmaBound hcurrentSucc).
      * exact (raw_le_trans M hPA _ _ _ hpiBound hcurrentSucc).
  - destruct hall as (ci & child & hci & hchild & hcode).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds ci child hci hchild)
      as (cs & cp & hchildTriple & hcs & hcp).
    assert (hciCurrent := raw_succ_le_of_lt_pair M hPA ci current hci).
    assert (hcpCurrent := raw_le_trans M hPA _ _ _ hcp hciCurrent).
    assert (honeCurrent : rawLe M (rawNumeralValue M 1) current).
    {
      exact (raw_le_trans M hPA _ (raw_succ M ci) current
        (raw_rank_one_le_succ M hPA ci) hciCurrent).
    }
    destruct (raw_rank_max_exists_bounded M hPA
      (rawNumeralValue M 1) cp current honeCurrent hcpCurrent)
      as [base [hbase hbaseBound]].
    exists (raw_succ M base), base. split.
    + right. right. right. right. right. left.
      exists ci, child, cs, cp.
      split; [exact hci |].
      split; [exact hchildTriple |].
      split; [exact hcode |].
      exists base. repeat split; try assumption.
    + split.
      * exact (raw_rank_succ_le M hPA base current hbaseBound).
      * exact (raw_le_trans M hPA _ _ _ hbaseBound hcurrentSucc).
  - destruct hex as (ci & child & hci & hchild & hcode).
    destruct (raw_rank_child_values M hPA
      formulaCode formulaStep sigmaCode rankStep piCode current
      hsigmaDefined hpiDefined hbounds ci child hci hchild)
      as (cs & cp & hchildTriple & hcs & hcp).
    assert (hciCurrent := raw_succ_le_of_lt_pair M hPA ci current hci).
    assert (hcsCurrent := raw_le_trans M hPA _ _ _ hcs hciCurrent).
    assert (honeCurrent : rawLe M (rawNumeralValue M 1) current).
    {
      exact (raw_le_trans M hPA _ (raw_succ M ci) current
        (raw_rank_one_le_succ M hPA ci) hciCurrent).
    }
    destruct (raw_rank_max_exists_bounded M hPA
      (rawNumeralValue M 1) cs current honeCurrent hcsCurrent)
      as [base [hbase hbaseBound]].
    exists base, (raw_succ M base). split.
    + right. right. right. right. right. right.
      exists ci, child, cs, cp.
      split; [exact hci |].
      split; [exact hchildTriple |].
      split; [exact hcode |].
      exists base. repeat split; try assumption.
    + split.
      * exact (raw_le_trans M hPA _ _ _ hbaseBound hcurrentSucc).
      * exact (raw_rank_succ_le M hPA base current hbaseBound).
Qed.

(** ------------------------------------------------------------------
    One-entry beta extension preserves the already certified prefix. *)

Lemma raw_rank_betaExtension_defined_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall oldCode step current value newCode,
  RawCodedAssignmentDefinedThrough M oldCode step current ->
  RawBetaCodeExtension M oldCode step current value newCode ->
  RawCodedAssignmentDefinedThrough M
    newCode step (raw_succ M current).
Proof.
  intros M hPA oldCode step current value newCode hdefined hext
    index hindex.
  destruct (raw_lt_succ_cases M hPA index current hindex)
    as [hbefore | ->].
  - destruct (hdefined index hbefore) as [out hout]. exists out.
    unfold RawCodedAssignmentLookup in *.
    exact ((proj1 hext) index hbefore out hout).
  - exists value. exact (proj2 hext).
Qed.

Lemma raw_rankTripleLookup_extend : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep oldSigmaCode rankStep oldPiCode
    current newSigmaCode newPiCode sigmaOut piOut,
  RawBetaCodeExtension M
    oldSigmaCode rankStep current sigmaOut newSigmaCode ->
  RawBetaCodeExtension M
    oldPiCode rankStep current piOut newPiCode ->
  forall index code sigma pi,
  rawLt M index current ->
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep oldSigmaCode rankStep oldPiCode rankStep
    index code sigma pi ->
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep newSigmaCode rankStep newPiCode rankStep
    index code sigma pi.
Proof.
  intros M hPA formulaCode formulaStep oldSigmaCode rankStep oldPiCode
    current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
    index code sigma pi hindex [hcode [hsigma hpi]].
  split; [exact hcode |]. split.
  - unfold RawCodedAssignmentLookup in *.
    exact ((proj1 hsigmaExt) index hindex sigma hsigma).
  - unfold RawCodedAssignmentLookup in *.
    exact ((proj1 hpiExt) index hindex pi hpi).
Qed.

Lemma raw_rankTraversalRow_extend : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep oldSigmaCode rankStep oldPiCode
    current newSigmaCode newPiCode sigmaOut piOut,
  RawBetaCodeExtension M
    oldSigmaCode rankStep current sigmaOut newSigmaCode ->
  RawBetaCodeExtension M
    oldPiCode rankStep current piOut newPiCode ->
  forall index code sigma pi,
  rawLe M index current ->
  RawCodedFormulaRankTraversalRow M
    formulaCode formulaStep oldSigmaCode rankStep oldPiCode rankStep
    index code sigma pi ->
  RawCodedFormulaRankTraversalRow M
    formulaCode formulaStep newSigmaCode rankStep newPiCode rankStep
    index code sigma pi.
Proof.
  intros M hPA formulaCode formulaStep oldSigmaCode rankStep oldPiCode
    current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
    index code sigma pi hindexCurrent hrow.
  destruct hrow as [heq | [hbot | [himp | [hand | [hor | [hall | hex]]]]]].
  - left. exact heq.
  - right. left. exact hbot.
  - right. right. left.
    destruct himp as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & hstep).
    exists li, left, ls, lp, ri, right, rs, rp.
    split; [exact hli |]. split.
    + exact (raw_rankTripleLookup_extend M hPA
        formulaCode formulaStep oldSigmaCode rankStep oldPiCode
        current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
        li left ls lp
        (raw_lt_le_trans_pair M hPA li index current hli hindexCurrent)
        hleft).
    + split; [exact hri |]. split.
      * exact (raw_rankTripleLookup_extend M hPA
          formulaCode formulaStep oldSigmaCode rankStep oldPiCode
          current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
          ri right rs rp
          (raw_lt_le_trans_pair M hPA ri index current hri hindexCurrent)
          hright).
      * exact hstep.
  - right. right. right. left.
    destruct hand as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & hstep).
    exists li, left, ls, lp, ri, right, rs, rp.
    split; [exact hli |]. split.
    + exact (raw_rankTripleLookup_extend M hPA
        formulaCode formulaStep oldSigmaCode rankStep oldPiCode
        current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
        li left ls lp
        (raw_lt_le_trans_pair M hPA li index current hli hindexCurrent)
        hleft).
    + split; [exact hri |]. split.
      * exact (raw_rankTripleLookup_extend M hPA
          formulaCode formulaStep oldSigmaCode rankStep oldPiCode
          current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
          ri right rs rp
          (raw_lt_le_trans_pair M hPA ri index current hri hindexCurrent)
          hright).
      * exact hstep.
  - right. right. right. right. left.
    destruct hor as
      (li & left & ls & lp & ri & right & rs & rp &
       hli & hleft & hri & hright & hstep).
    exists li, left, ls, lp, ri, right, rs, rp.
    split; [exact hli |]. split.
    + exact (raw_rankTripleLookup_extend M hPA
        formulaCode formulaStep oldSigmaCode rankStep oldPiCode
        current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
        li left ls lp
        (raw_lt_le_trans_pair M hPA li index current hli hindexCurrent)
        hleft).
    + split; [exact hri |]. split.
      * exact (raw_rankTripleLookup_extend M hPA
          formulaCode formulaStep oldSigmaCode rankStep oldPiCode
          current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
          ri right rs rp
          (raw_lt_le_trans_pair M hPA ri index current hri hindexCurrent)
          hright).
      * exact hstep.
  - right. right. right. right. right. left.
    destruct hall as (ci & child & cs & cp & hci & hchild & hstep).
    exists ci, child, cs, cp. split; [exact hci |]. split.
    + exact (raw_rankTripleLookup_extend M hPA
        formulaCode formulaStep oldSigmaCode rankStep oldPiCode
        current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
        ci child cs cp
        (raw_lt_le_trans_pair M hPA ci index current hci hindexCurrent)
        hchild).
    + exact hstep.
  - right. right. right. right. right. right.
    destruct hex as (ci & child & cs & cp & hci & hchild & hstep).
    exists ci, child, cs, cp. split; [exact hci |]. split.
    + exact (raw_rankTripleLookup_extend M hPA
        formulaCode formulaStep oldSigmaCode rankStep oldPiCode
        current newSigmaCode newPiCode sigmaOut piOut hsigmaExt hpiExt
        ci child cs cp
        (raw_lt_le_trans_pair M hPA ci index current hci hindexCurrent)
        hchild).
    + exact hstep.
Qed.

(** A lookup in the extended prefix can be pulled back uniquely to the old
    prefix.  This is needed because [RawBetaCodeExtension] records forward
    preservation rather than an extensional equality of beta functions. *)
Lemma raw_rankTripleLookup_pullback : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep oldSigmaCode rankStep oldPiCode current
    newSigmaCode newPiCode sigmaOut piOut,
  RawCodedAssignmentDefinedThrough M oldSigmaCode rankStep current ->
  RawCodedAssignmentDefinedThrough M oldPiCode rankStep current ->
  RawBetaCodeExtension M
    oldSigmaCode rankStep current sigmaOut newSigmaCode ->
  RawBetaCodeExtension M
    oldPiCode rankStep current piOut newPiCode ->
  forall index code sigma pi,
  rawLt M index current ->
  RawCodedFormulaRankTripleLookup M
    formulaCode formulaStep newSigmaCode rankStep newPiCode rankStep
    index code sigma pi ->
  exists oldSigma oldPi,
    RawCodedFormulaRankTripleLookup M
      formulaCode formulaStep oldSigmaCode rankStep oldPiCode rankStep
      index code oldSigma oldPi /\
    sigma = oldSigma /\ pi = oldPi.
Proof.
  intros M hPA formulaCode formulaStep oldSigmaCode rankStep oldPiCode
    current newSigmaCode newPiCode sigmaOut piOut
    hsigmaDefined hpiDefined hsigmaExt hpiExt
    index code sigma pi hindex [hformula [hsigmaNew hpiNew]].
  destruct (hsigmaDefined index hindex) as [oldSigma hsigmaOld].
  destruct (hpiDefined index hindex) as [oldPi hpiOld].
  assert (hsigmaPreserved : RawCodedAssignmentLookup M
      newSigmaCode rankStep index oldSigma).
  {
    unfold RawCodedAssignmentLookup in *.
    exact ((proj1 hsigmaExt) index hindex oldSigma hsigmaOld).
  }
  assert (hpiPreserved : RawCodedAssignmentLookup M
      newPiCode rankStep index oldPi).
  {
    unfold RawCodedAssignmentLookup in *.
    exact ((proj1 hpiExt) index hindex oldPi hpiOld).
  }
  assert (hsigmaEq : sigma = oldSigma).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newSigmaCode rankStep index sigma oldSigma hsigmaNew hsigmaPreserved).
  }
  assert (hpiEq : pi = oldPi).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      newPiCode rankStep index pi oldPi hpiNew hpiPreserved).
  }
  exists oldSigma, oldPi. repeat split; assumption.
Qed.

Theorem raw_codedFormulaRankPrefix_succ : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep bound rootIndex root rankStep current,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  RawFormulaRankTableCapacity M bound rankStep ->
  rawLt M current bound ->
  RawCodedFormulaRankPrefix M
    formulaCode formulaStep rankStep current ->
  RawCodedFormulaRankPrefix M
    formulaCode formulaStep rankStep (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root rankStep current
    [hformulaDefined [_ [_ hsyntaxRows]]] [hcommon hcapacity]
    hcurrentBound
    (oldSigmaCode & oldPiCode & hsigmaDefined & hpiDefined &
     hrows & hbounds).
  destruct (hformulaDefined current hcurrentBound) as [code hformula].
  pose proof (hsyntaxRows current code hcurrentBound hformula) as hsyntax.
  destruct (raw_formulaSyntaxRow_rank_exists_bounded M hPA
    formulaCode formulaStep oldSigmaCode rankStep oldPiCode current code
    hsigmaDefined hpiDefined hbounds hsyntax)
    as (sigma & pi & hrow & hsigmaBound & hpiBound).
  assert (hcommonCurrent : RawCommonMultipleThrough M current rankStep).
  {
    intros index hindex.
    exact (hcommon index
      (raw_assignment_lt_trans M hPA index current bound
        hindex hcurrentBound)).
  }
  destruct (raw_betaCodeExtension_exists M hPA
    oldSigmaCode rankStep current sigma hcommonCurrent
    (hcapacity current sigma hcurrentBound hsigmaBound))
    as [newSigmaCode hsigmaExt].
  destruct (raw_betaCodeExtension_exists M hPA
    oldPiCode rankStep current pi hcommonCurrent
    (hcapacity current pi hcurrentBound hpiBound))
    as [newPiCode hpiExt].
  exists newSigmaCode, newPiCode.
  split.
  - exact (raw_rank_betaExtension_defined_succ M hPA
      oldSigmaCode rankStep current sigma newSigmaCode
      hsigmaDefined hsigmaExt).
  - split.
    + exact (raw_rank_betaExtension_defined_succ M hPA
        oldPiCode rankStep current pi newPiCode
        hpiDefined hpiExt).
    + split.
      * intros index rowCode rowSigma rowPi hindex hlookup.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | hcurrent].
        -- destruct (raw_rankTripleLookup_pullback M hPA
             formulaCode formulaStep oldSigmaCode rankStep oldPiCode current
             newSigmaCode newPiCode sigma pi
             hsigmaDefined hpiDefined hsigmaExt hpiExt
             index rowCode rowSigma rowPi hbefore hlookup)
             as (oldSigma & oldPi & hold & -> & ->).
           exact (raw_rankTraversalRow_extend M hPA
             formulaCode formulaStep oldSigmaCode rankStep oldPiCode current
             newSigmaCode newPiCode sigma pi hsigmaExt hpiExt
             index rowCode oldSigma oldPi
             (raw_lt_to_le M index current hbefore)
             (hrows index rowCode oldSigma oldPi hbefore hold)).
        -- subst index.
           assert (hcurrentLookup : RawCodedFormulaRankTripleLookup M
               formulaCode formulaStep newSigmaCode rankStep
               newPiCode rankStep current code sigma pi).
           {
             split; [exact hformula |]. split;
               [exact (proj2 hsigmaExt) | exact (proj2 hpiExt)].
           }
           destruct (raw_codedFormulaRankTripleLookup_functional M hPA
             formulaCode formulaStep newSigmaCode rankStep
             newPiCode rankStep current
             rowCode rowSigma rowPi code sigma pi
             hlookup hcurrentLookup) as [-> [-> ->]].
           exact (raw_rankTraversalRow_extend M hPA
             formulaCode formulaStep oldSigmaCode rankStep oldPiCode current
             newSigmaCode newPiCode sigma pi hsigmaExt hpiExt
             current code sigma pi (raw_rank_le_refl M hPA current) hrow).
      * intros index rowCode rowSigma rowPi hindex hlookup.
        destruct (raw_lt_succ_cases M hPA index current hindex)
          as [hbefore | hcurrent].
        -- destruct (raw_rankTripleLookup_pullback M hPA
             formulaCode formulaStep oldSigmaCode rankStep oldPiCode current
             newSigmaCode newPiCode sigma pi
             hsigmaDefined hpiDefined hsigmaExt hpiExt
             index rowCode rowSigma rowPi hbefore hlookup)
             as (oldSigma & oldPi & hold & -> & ->).
           exact (hbounds index rowCode oldSigma oldPi hbefore hold).
        -- subst index.
           assert (hcurrentLookup : RawCodedFormulaRankTripleLookup M
               formulaCode formulaStep newSigmaCode rankStep
               newPiCode rankStep current code sigma pi).
           {
             split; [exact hformula |]. split;
               [exact (proj2 hsigmaExt) | exact (proj2 hpiExt)].
           }
           destruct (raw_codedFormulaRankTripleLookup_functional M hPA
             formulaCode formulaStep newSigmaCode rankStep
             newPiCode rankStep current
             rowCode rowSigma rowPi code sigma pi
             hlookup hcurrentLookup) as [-> [-> ->]].
           split; assumption.
Qed.

(** ------------------------------------------------------------------
    Definable induction over a possibly nonstandard syntax bound. *)

Lemma raw_rank_lt_of_succ_le : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLe M (raw_succ M x) y -> rawLt M x y.
Proof.
  intros M hPA x y [gap hgap]. exists gap.
  rewrite raw_add_succ by exact hPA.
  rewrite <- raw_succ_add_pair by exact hPA.
  exact hgap.
Qed.

Lemma raw_codedFormulaRankPrefix_zero : forall (M : RawPAModel),
  RawPASatisfies M -> forall formulaCode formulaStep rankStep,
  RawCodedFormulaRankPrefix M
    formulaCode formulaStep rankStep (raw_zero M).
Proof.
  intros M hPA formulaCode formulaStep rankStep.
  exists (raw_zero M), (raw_zero M).
  split.
  - intros index hindex.
    exfalso. exact (raw_not_lt_zero M hPA index hindex).
  - split.
    + intros index hindex.
      exfalso. exact (raw_not_lt_zero M hPA index hindex).
    + split.
      * intros index code sigma pi hindex.
        exfalso. exact (raw_not_lt_zero M hPA index hindex).
      * intros index code sigma pi hindex.
        exfalso. exact (raw_not_lt_zero M hPA index hindex).
Qed.

Definition codedFormulaRankPrefixWithinTermAt
    (formulaCode formulaStep rankStep bound current : term) : formula :=
  pImp (Formula.leTermAt current bound)
    (codedFormulaRankPrefixTermAt
      formulaCode formulaStep rankStep current).

Definition RawCodedFormulaRankPrefixWithin (M : RawPAModel)
    (formulaCode formulaStep rankStep bound current : M) : Prop :=
  rawLe M current bound ->
  RawCodedFormulaRankPrefix M
    formulaCode formulaStep rankStep current.

Arguments RawCodedFormulaRankPrefixWithin
  M formulaCode formulaStep rankStep bound current : clear implicits.

Lemma raw_sat_codedFormulaRankPrefixWithinTermAt_iff : forall
    (M : RawPAModel) (e : nat -> M)
    formulaCode formulaStep rankStep bound current,
  raw_formula_sat M e
    (codedFormulaRankPrefixWithinTermAt
      formulaCode formulaStep rankStep bound current) <->
  RawCodedFormulaRankPrefixWithin M
    (raw_term_eval M e formulaCode) (raw_term_eval M e formulaStep)
    (raw_term_eval M e rankStep) (raw_term_eval M e bound)
    (raw_term_eval M e current).
Proof.
  intros. unfold codedFormulaRankPrefixWithinTermAt,
    RawCodedFormulaRankPrefixWithin.
  cbn [raw_formula_sat].
  rewrite raw_sat_leTermAt_iff_rank.
  rewrite raw_sat_codedFormulaRankPrefixTermAt_iff.
  reflexivity.
Qed.

Theorem raw_codedFormulaRankPrefixWithin_succ : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep bound rootIndex root rankStep current,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  RawFormulaRankTableCapacity M bound rankStep ->
  RawCodedFormulaRankPrefixWithin M
    formulaCode formulaStep rankStep bound current ->
  RawCodedFormulaRankPrefixWithin M
    formulaCode formulaStep rankStep bound (raw_succ M current).
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root rankStep current
    hsyntax hcapacity hcurrent hsuccBound.
  assert (hcurrentSucc : rawLe M current (raw_succ M current)).
  { exact (raw_lt_to_le M current (raw_succ M current)
      (raw_assignment_lt_self_succ M hPA current)). }
  assert (hcurrentBound : rawLe M current bound).
  { exact (raw_le_trans M hPA _ _ _ hcurrentSucc hsuccBound). }
  exact (raw_codedFormulaRankPrefix_succ M hPA
    formulaCode formulaStep bound rootIndex root rankStep current
    hsyntax hcapacity
    (raw_rank_lt_of_succ_le M hPA current bound hsuccBound)
    (hcurrent hcurrentBound)).
Qed.

Theorem raw_codedFormulaRankPrefix_all : forall (M : RawPAModel),
  RawPASatisfies M ->
  forall formulaCode formulaStep bound rootIndex root rankStep,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  RawFormulaRankTableCapacity M bound rankStep ->
  forall current,
  RawCodedFormulaRankPrefixWithin M
    formulaCode formulaStep rankStep bound current.
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root rankStep
    hsyntax hcapacity.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => formulaCode
    | 1 => formulaStep
    | 2 => rankStep
    | _ => bound
    end).
  set (phi := codedFormulaRankPrefixWithinTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2 (raw_sat_codedFormulaRankPrefixWithinTermAt_iff M
        (scons M (raw_zero M) parameterEnv)
        (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      intros _.
      exact (raw_codedFormulaRankPrefix_zero M hPA
        formulaCode formulaStep rankStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedFormulaRankPrefixWithinTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedFormulaRankPrefixWithinTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedFormulaRankPrefixWithin_succ M hPA
        formulaCode formulaStep bound rootIndex root rankStep current
        hsyntax hcapacity hcurrent).
  }
  intro current.
  unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedFormulaRankPrefixWithinTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
    (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** The construction endpoint exposes all witnesses, including the chosen
    CRT step.  Thus downstream uses need no hidden choice principle. *)
Theorem raw_formulaSyntaxTraversal_rankTraversal_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep bound rootIndex root,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  exists rankStep sigmaCode piCode sigma pi,
    RawFormulaRankTableCapacity M bound rankStep /\
    RawCodedFormulaRankTraversal M
      formulaCode formulaStep sigmaCode rankStep piCode rankStep
      bound rootIndex root sigma pi.
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root hsyntax.
  destruct (raw_formulaRankTableCapacity_exists M hPA bound)
    as [rankStep hcapacity].
  pose proof (raw_codedFormulaRankPrefix_all M hPA
    formulaCode formulaStep bound rootIndex root rankStep
    hsyntax hcapacity bound) as hwithin.
  destruct hsyntax as
    [hformulaDefined [hrootBound [hrootFormula hsyntaxRows]]].
  destruct (hwithin (raw_rank_le_refl M hPA bound)) as
    (sigmaCode & piCode & hsigmaDefined & hpiDefined & hrows & hbounds).
  destruct (hsigmaDefined rootIndex hrootBound) as [sigma hsigma].
  destruct (hpiDefined rootIndex hrootBound) as [pi hpi].
  exists rankStep, sigmaCode, piCode, sigma, pi.
  split; [exact hcapacity |].
  split; [exact hformulaDefined |].
  split; [exact hsigmaDefined |].
  split; [exact hpiDefined |].
  split; [exact hrootBound |].
  split.
  - repeat split; assumption.
  - exact hrows.
Qed.

Corollary raw_formulaSyntaxTraversal_rank_exists : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall formulaCode formulaStep bound rootIndex root,
  RawCodedFormulaSyntaxTraversal M
    formulaCode formulaStep bound rootIndex root ->
  exists sigma pi, RawCodedFormulaRank M root sigma pi.
Proof.
  intros M hPA formulaCode formulaStep bound rootIndex root hsyntax.
  destruct (raw_formulaSyntaxTraversal_rankTraversal_exists M hPA
    formulaCode formulaStep bound rootIndex root hsyntax)
    as (rankStep & sigmaCode & piCode & sigma & pi & _ & htraversal).
  exists sigma, pi.
  exists formulaCode, formulaStep, sigmaCode, rankStep,
    piCode, rankStep, bound, rootIndex.
  exact htraversal.
Qed.

Theorem raw_codedWellFormedFormula_rank_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedWellFormedFormula M root ->
  exists sigma pi, RawCodedFormulaRank M root sigma pi.
Proof.
  intros M hPA root
    (formulaCode & formulaStep & bound & rootIndex & hsyntax).
  exact (raw_formulaSyntaxTraversal_rank_exists M hPA
    formulaCode formulaStep bound rootIndex root hsyntax).
Qed.

Corollary raw_codedWellFormedFormula_rank_exists_unique : forall
    (M : RawPAModel), RawPASatisfies M -> forall root,
  RawCodedWellFormedFormula M root ->
  exists sigma pi,
    RawCodedFormulaRank M root sigma pi /\
    forall otherSigma otherPi,
      RawCodedFormulaRank M root otherSigma otherPi ->
      sigma = otherSigma /\ pi = otherPi.
Proof.
  intros M hPA root hwellformed.
  destruct (raw_codedWellFormedFormula_rank_exists M hPA root hwellformed)
    as [sigma [pi hrank]].
  exists sigma, pi. split; [exact hrank |].
  intros otherSigma otherPi hother.
  exact (raw_codedFormulaRank_functional M hPA
    root sigma pi otherSigma otherPi hrank hother).
Qed.

(** The totality theorem is itself a PA theorem over the honest syntax
    domain.  The two existential binders put root at variable 2. *)
Definition codedWellFormedFormulaRankTotalFormula : formula :=
  pAll (pImp
    (codedWellFormedFormulaTermAt (tVar 0))
    (pEx (pEx
      (codedFormulaRankTermAt (tVar 2) (tVar 1) (tVar 0))))).

Lemma raw_sat_codedWellFormedFormulaRankTotalFormula_iff : forall
    (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e codedWellFormedFormulaRankTotalFormula <->
  forall root : M,
    RawCodedWellFormedFormula M root ->
    exists sigma pi, RawCodedFormulaRank M root sigma pi.
Proof.
  intros M e.
  unfold codedWellFormedFormulaRankTotalFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedWellFormedFormulaTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaRankTermAt_iff.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Theorem codedWellFormedFormulaRankTotalFormula_sentence :
  Formula.Sentence codedWellFormedFormulaRankTotalFormula.
Proof.
  intros k hfree.
  unfold codedWellFormedFormulaRankTotalFormula in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedWellFormedFormulaRankTotalFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedWellFormedFormulaRankTotalFormula.
Proof.
  intros M hPA e.
  apply (proj2
    (raw_sat_codedWellFormedFormulaRankTotalFormula_iff M e)).
  exact (raw_codedWellFormedFormula_rank_exists M hPA).
Qed.

Theorem PA_proves_codedWellFormedFormulaRankTotalFormula :
  Formula.BProv Formula.Ax_s []
    codedWellFormedFormulaRankTotalFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedWellFormedFormulaRankTotalFormula_sentence.
  - exact codedWellFormedFormulaRankTotalFormula_raw_valid.
Qed.

End PABoundedRawCodedFormulaRankTotality.
