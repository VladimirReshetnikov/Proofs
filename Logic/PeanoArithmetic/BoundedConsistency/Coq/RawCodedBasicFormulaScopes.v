(**
  Scope preservation for the small arithmetic graph constructors used by
  model-internal proof certificates.

  The PAHF beta graph contains large transparent arithmetic formulae.  We
  obtain its scope from the already-proved renaming equations, so no proof
  here normalizes those formulae or the numerals embedded in syntax codes.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedAssignment
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators.

Module PABoundedRawCodedBasicFormulaScopes.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedStandardFormulaScopeCombinators.

Lemma standardFormulaScoped_ltTermAt : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (Formula.ltTermAt lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs.
  apply standardFormulaScoped_of_rename_invariant.
  intros renaming hfix.
  rewrite Formula.rename_ltTermAt.
  rewrite (standardTermScoped_rename_fixed scope lhs renaming hlhs hfix).
  rewrite (standardTermScoped_rename_fixed scope rhs renaming hrhs hfix).
  reflexivity.
Qed.

Lemma standardFormulaScoped_leTermAt : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (Formula.leTermAt lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs.
  apply standardFormulaScoped_of_rename_invariant.
  intros renaming hfix.
  rewrite Formula.rename_leTermAt.
  rewrite (standardTermScoped_rename_fixed scope lhs renaming hlhs hfix).
  rewrite (standardTermScoped_rename_fixed scope rhs renaming hrhs hfix).
  reflexivity.
Qed.

Lemma standardFormulaScoped_betaTermTermAt : forall scope
    output code step index,
  StandardTermScoped scope output ->
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope index ->
  StandardFormulaScoped scope
    (Formula.betaTermTermAt output code step index).
Proof.
  intros scope output code step index
    houtput hcode hstep hindex.
  apply standardFormulaScoped_of_rename_invariant.
  intros renaming hfix.
  rewrite Formula.rename_betaTermTermAt.
  rewrite (standardTermScoped_rename_fixed
    scope output renaming houtput hfix).
  rewrite (standardTermScoped_rename_fixed
    scope code renaming hcode hfix).
  rewrite (standardTermScoped_rename_fixed
    scope step renaming hstep hfix).
  rewrite (standardTermScoped_rename_fixed
    scope index renaming hindex hfix).
  reflexivity.
Qed.

Lemma standardFormulaScoped_betaEntryExistsTermAt : forall scope
    code step index,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope index ->
  StandardFormulaScoped scope
    (betaEntryExistsTermAt code step index).
Proof.
  intros scope code step index hcode hstep hindex.
  unfold betaEntryExistsTermAt.
  apply standardFormulaScoped_ex.
  apply standardFormulaScoped_betaTermTermAt.
  - apply standardTermScoped_var. lia.
  - exact (standardTermScoped_rename_succ scope code hcode).
  - exact (standardTermScoped_rename_succ scope step hstep).
  - exact (standardTermScoped_rename_succ scope index hindex).
Qed.

Lemma standardFormulaScoped_betaEntryExistsPrefixTermAt : forall scope
    code step bound,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (betaEntryExistsPrefixTermAt code step bound).
Proof.
  intros scope code step bound hcode hstep hbound.
  unfold betaEntryExistsPrefixTermAt.
  apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var. lia.
    + exact (standardTermScoped_rename_succ scope bound hbound).
  - apply standardFormulaScoped_betaEntryExistsTermAt.
    + exact (standardTermScoped_rename_succ scope code hcode).
    + exact (standardTermScoped_rename_succ scope step hstep).
    + apply standardTermScoped_var. lia.
Qed.

Lemma standardFormulaScoped_codedAssignmentLookupTermAt : forall scope
    code step index value,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope index ->
  StandardTermScoped scope value ->
  StandardFormulaScoped scope
    (codedAssignmentLookupTermAt code step index value).
Proof.
  intros scope code step index value hcode hstep hindex hvalue.
  unfold codedAssignmentLookupTermAt.
  exact (standardFormulaScoped_betaTermTermAt scope
    value code step index hvalue hcode hstep hindex).
Qed.

Lemma standardFormulaScoped_codedAssignmentDefinedThroughTermAt :
    forall scope code step bound,
  StandardTermScoped scope code ->
  StandardTermScoped scope step ->
  StandardTermScoped scope bound ->
  StandardFormulaScoped scope
    (codedAssignmentDefinedThroughTermAt code step bound).
Proof.
  intros scope code step bound hcode hstep hbound.
  unfold codedAssignmentDefinedThroughTermAt.
  exact (standardFormulaScoped_betaEntryExistsPrefixTermAt scope
    code step bound hcode hstep hbound).
Qed.

Lemma standardTermScoped_pairTerm : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardTermScoped scope (pairTerm lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs.
  unfold pairTerm.
  apply standardTermScoped_add.
  - apply standardTermScoped_mul;
      apply standardTermScoped_add; assumption.
  - exact hlhs.
Qed.

Lemma standardTermScoped_nodeTerm : forall scope head tail,
  StandardTermScoped scope head ->
  StandardTermScoped scope tail ->
  StandardTermScoped scope (nodeTerm head tail).
Proof.
  intros scope head tail hhead htail.
  unfold nodeTerm.
  apply standardTermScoped_succ.
  exact (standardTermScoped_pairTerm scope head tail hhead htail).
Qed.

Lemma standardTermScoped_codeList1Term : forall scope first,
  StandardTermScoped scope first ->
  StandardTermScoped scope (codeList1Term first).
Proof.
  intros scope first hfirst. unfold codeList1Term.
  apply standardTermScoped_nodeTerm; [exact hfirst |].
  apply standardTermScoped_zero.
Qed.

Lemma standardTermScoped_codeList2Term : forall scope first second,
  StandardTermScoped scope first ->
  StandardTermScoped scope second ->
  StandardTermScoped scope (codeList2Term first second).
Proof.
  intros scope first second hfirst hsecond. unfold codeList2Term.
  apply standardTermScoped_nodeTerm; [exact hfirst |].
  exact (standardTermScoped_codeList1Term scope second hsecond).
Qed.

Lemma standardTermScoped_codeList3Term : forall scope first second third,
  StandardTermScoped scope first ->
  StandardTermScoped scope second ->
  StandardTermScoped scope third ->
  StandardTermScoped scope (codeList3Term first second third).
Proof.
  intros scope first second third hfirst hsecond hthird.
  unfold codeList3Term.
  apply standardTermScoped_nodeTerm; [exact hfirst |].
  exact (standardTermScoped_codeList2Term
    scope second third hsecond hthird).
Qed.

Lemma standardFormulaScoped_codeList1TermAt : forall scope code first,
  StandardTermScoped scope code ->
  StandardTermScoped scope first ->
  StandardFormulaScoped scope (codeList1TermAt code first).
Proof.
  intros scope code first hcode hfirst. unfold codeList1TermAt.
  apply standardFormulaScoped_eq; [exact hcode |].
  exact (standardTermScoped_codeList1Term scope first hfirst).
Qed.

Lemma standardFormulaScoped_codeList2TermAt : forall scope code first second,
  StandardTermScoped scope code ->
  StandardTermScoped scope first ->
  StandardTermScoped scope second ->
  StandardFormulaScoped scope (codeList2TermAt code first second).
Proof.
  intros scope code first second hcode hfirst hsecond.
  unfold codeList2TermAt.
  apply standardFormulaScoped_eq; [exact hcode |].
  exact (standardTermScoped_codeList2Term
    scope first second hfirst hsecond).
Qed.

Lemma standardFormulaScoped_codeList3TermAt : forall scope
    code first second third,
  StandardTermScoped scope code ->
  StandardTermScoped scope first ->
  StandardTermScoped scope second ->
  StandardTermScoped scope third ->
  StandardFormulaScoped scope
    (codeList3TermAt code first second third).
Proof.
  intros scope code first second third hcode hfirst hsecond hthird.
  unfold codeList3TermAt.
  apply standardFormulaScoped_eq; [exact hcode |].
  exact (standardTermScoped_codeList3Term
    scope first second third hfirst hsecond hthird).
Qed.

Lemma standardFormulaScoped_termVarCodeTermAt : forall scope code index,
  StandardTermScoped scope code ->
  StandardTermScoped scope index ->
  StandardFormulaScoped scope (termVarCodeTermAt code index).
Proof.
  intros scope code index hcode hindex. unfold termVarCodeTermAt.
  apply standardFormulaScoped_codeList2TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_termZeroCodeTermAt : forall scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope (termZeroCodeTermAt code).
Proof.
  intros scope code hcode. unfold termZeroCodeTermAt.
  apply standardFormulaScoped_codeList1TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_termSuccCodeTermAt : forall scope code child,
  StandardTermScoped scope code ->
  StandardTermScoped scope child ->
  StandardFormulaScoped scope (termSuccCodeTermAt code child).
Proof.
  intros scope code child hcode hchild. unfold termSuccCodeTermAt.
  apply standardFormulaScoped_codeList2TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_termAddCodeTermAt : forall scope code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (termAddCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs. unfold termAddCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_termMulCodeTermAt : forall scope code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (termMulCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs. unfold termMulCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

(** Every PA syntax-code graph is merely a [codeList] graph with a closed
    constructor tag.  Keeping the tag numeral opaque is essential here. *)
Lemma standardFormulaScoped_formulaBotCodeTermAt : forall scope code,
  StandardTermScoped scope code ->
  StandardFormulaScoped scope (formulaBotCodeTermAt code).
Proof.
  intros scope code hcode. unfold formulaBotCodeTermAt.
  apply standardFormulaScoped_codeList1TermAt; [exact hcode |].
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaEqCodeTermAt : forall scope
    code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (formulaEqCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs.
  unfold formulaEqCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaImpCodeTermAt : forall scope
    code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (formulaImpCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs.
  unfold formulaImpCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaAndCodeTermAt : forall scope
    code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (formulaAndCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs.
  unfold formulaAndCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaOrCodeTermAt : forall scope
    code lhs rhs,
  StandardTermScoped scope code ->
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (formulaOrCodeTermAt code lhs rhs).
Proof.
  intros scope code lhs rhs hcode hlhs hrhs.
  unfold formulaOrCodeTermAt.
  apply standardFormulaScoped_codeList3TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaAllCodeTermAt : forall scope code child,
  StandardTermScoped scope code ->
  StandardTermScoped scope child ->
  StandardFormulaScoped scope (formulaAllCodeTermAt code child).
Proof.
  intros scope code child hcode hchild. unfold formulaAllCodeTermAt.
  apply standardFormulaScoped_codeList2TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

Lemma standardFormulaScoped_formulaExCodeTermAt : forall scope code child,
  StandardTermScoped scope code ->
  StandardTermScoped scope child ->
  StandardFormulaScoped scope (formulaExCodeTermAt code child).
Proof.
  intros scope code child hcode hchild. unfold formulaExCodeTermAt.
  apply standardFormulaScoped_codeList2TermAt; try assumption.
  apply standardTermScoped_numeral.
Qed.

End PABoundedRawCodedBasicFormulaScopes.
