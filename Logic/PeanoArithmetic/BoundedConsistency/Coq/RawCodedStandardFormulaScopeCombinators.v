(**
  Constructor-level lemmas for metatheoretic de Bruijn scopes.

  These lemmas deliberately keep standard numerals and the large arithmetic
  graph formulae opaque.  Downstream scope proofs can consequently unfold one
  named graph constructor at a time instead of asking Rocq to normalize an
  enormous quoted numeral or formula code.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport.

Module PABoundedRawCodedStandardFormulaScopeCombinators.

Import PA.
Import PAListRepresentability.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.

Lemma standardTermScoped_weaken : forall sourceScope targetScope input,
  StandardTermScoped sourceScope input ->
  sourceScope <= targetScope ->
  StandardTermScoped targetScope input.
Proof.
  intros sourceScope targetScope input hscope hle index hfree.
  specialize (hscope index hfree). lia.
Qed.

Lemma standardFormulaScoped_weaken : forall sourceScope targetScope input,
  StandardFormulaScoped sourceScope input ->
  sourceScope <= targetScope ->
  StandardFormulaScoped targetScope input.
Proof.
  intros sourceScope targetScope input hscope hle index hfree.
  specialize (hscope index hfree). lia.
Qed.

Lemma standardTermScoped_var : forall scope index,
  index < scope -> StandardTermScoped scope (tVar index).
Proof.
  intros scope index hlt variable hfree.
  cbn [Term.Free] in hfree. now subst variable.
Qed.

Lemma standardTermScoped_zero : forall scope,
  StandardTermScoped scope tZero.
Proof.
  intros scope index hfree. cbn [Term.Free] in hfree. contradiction.
Qed.

Lemma standardTermScoped_succ : forall scope child,
  StandardTermScoped scope child ->
  StandardTermScoped scope (tSucc child).
Proof.
  intros scope child hchild index hfree.
  exact (hchild index hfree).
Qed.

Lemma standardTermScoped_add : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardTermScoped scope (tAdd lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardTermScoped_mul : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardTermScoped scope (tMul lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardTermScoped_numeral : forall scope value,
  StandardTermScoped scope (Term.numeral value).
Proof.
  intros scope value. induction value as [|value IH].
  - exact (standardTermScoped_zero scope).
  - exact (standardTermScoped_succ scope _ IH).
Qed.

(** [liftTerm binderCount] raises every free index by [binderCount]. *)
Lemma standardTermScoped_lift : forall scope binderCount input,
  StandardTermScoped scope input ->
  StandardTermScoped (binderCount + scope) (liftTerm binderCount input).
Proof.
  intros scope binderCount input hscope index hfree.
  unfold liftTerm in hfree.
  destruct (standardTermFree_rename_preimage input
    (fun sourceIndex => sourceIndex + binderCount) index hfree)
    as [sourceIndex [hsource heq]].
  specialize (hscope sourceIndex hsource). lia.
Qed.

Lemma standardTermScoped_rename_succ : forall scope input,
  StandardTermScoped scope input ->
  StandardTermScoped (S scope) (Term.rename S input).
Proof.
  intros scope input hscope index hfree.
  destruct (standardTermFree_rename_preimage input S index hfree)
    as [sourceIndex [hsource heq]].
  specialize (hscope sourceIndex hsource). lia.
Qed.

Lemma standardTermScoped_rename_fixed : forall scope input renaming,
  StandardTermScoped scope input ->
  (forall index, index < scope -> renaming index = index) ->
  Term.rename renaming input = input.
Proof.
  intros scope input renaming hscope hrenaming.
  transitivity (Term.rename (fun index => index) input).
  - apply Term.rename_ext_free.
    intros index hfree. exact (hrenaming index (hscope index hfree)).
  - exact (Term.rename_id input).
Qed.

Lemma standardFormulaScoped_rename_fixed : forall scope input renaming,
  StandardFormulaScoped scope input ->
  (forall index, index < scope -> renaming index = index) ->
  Formula.rename renaming input = input.
Proof.
  intros scope input renaming hscope hrenaming.
  transitivity (Formula.rename (fun index => index) input).
  - apply Formula.rename_ext_free.
    intros index hfree. exact (hrenaming index (hscope index hfree)).
  - exact (Formula.rename_id input).
Qed.

Lemma standardTermFree_rename_forward : forall input renaming index,
  Term.Free index input ->
  Term.Free (renaming index) (Term.rename renaming input).
Proof.
  intros input. induction input as [variable | | child IH |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    intros renaming index hfree; cbn [Term.rename Term.Free] in *.
  - now subst index.
  - contradiction.
  - exact (IH renaming index hfree).
  - destruct hfree as [hfree | hfree].
    + left. exact (IHlhs renaming index hfree).
    + right. exact (IHrhs renaming index hfree).
  - destruct hfree as [hfree | hfree].
    + left. exact (IHlhs renaming index hfree).
    + right. exact (IHrhs renaming index hfree).
Qed.

Lemma standardFormulaFree_rename_forward : forall input renaming index,
  Formula.Free index input ->
  Formula.Free (renaming index) (Formula.rename renaming input).
Proof.
  intros input. induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild];
    intros renaming index hfree;
    cbn [Formula.rename Formula.Free] in *.
  - destruct hfree as [hfree | hfree].
    + left. exact (standardTermFree_rename_forward
        lhs renaming index hfree).
    + right. exact (standardTermFree_rename_forward
        rhs renaming index hfree).
  - contradiction.
  - destruct hfree as [hfree | hfree].
    + left. exact (IHlhs renaming index hfree).
    + right. exact (IHrhs renaming index hfree).
  - destruct hfree as [hfree | hfree].
    + left. exact (IHlhs renaming index hfree).
    + right. exact (IHrhs renaming index hfree).
  - destruct hfree as [hfree | hfree].
    + left. exact (IHlhs renaming index hfree).
    + right. exact (IHrhs renaming index hfree).
  - specialize (IHchild (up renaming) (S index) hfree).
    cbn [up]. exact IHchild.
  - specialize (IHchild (up renaming) (S index) hfree).
    cbn [up]. exact IHchild.
Qed.

(** A formula is scoped when every renaming which fixes that scope fixes the
    formula.  The fresh target used below lies beyond [Formula.bound input],
    so a hypothetical out-of-scope occurrence cannot be hidden by syntax. *)
Lemma standardFormulaScoped_of_rename_invariant : forall scope input,
  (forall renaming,
    (forall index, index < scope -> renaming index = index) ->
    Formula.rename renaming input = input) ->
  StandardFormulaScoped scope input.
Proof.
  intros scope input hinvariant index hfree.
  destruct (Nat.lt_ge_cases index scope) as [hlt | hge]; [exact hlt |].
  set (freshRenaming := fun sourceIndex =>
    if sourceIndex <? scope then sourceIndex
    else Formula.bound input + sourceIndex + 1).
  assert (hfix : forall sourceIndex,
      sourceIndex < scope -> freshRenaming sourceIndex = sourceIndex).
  {
    intros sourceIndex hsource.
    unfold freshRenaming.
    rewrite (proj2 (Nat.ltb_lt sourceIndex scope) hsource).
    reflexivity.
  }
  pose proof (standardFormulaFree_rename_forward
    input freshRenaming index hfree) as hfresh.
  rewrite (hinvariant freshRenaming hfix) in hfresh.
  pose proof (Formula.free_lt_bound input _ hfresh) as hbound.
  unfold freshRenaming in hbound.
  rewrite (proj2 (Nat.ltb_ge index scope) hge) in hbound. lia.
Qed.

Lemma standardFormulaScoped_eq : forall scope lhs rhs,
  StandardTermScoped scope lhs ->
  StandardTermScoped scope rhs ->
  StandardFormulaScoped scope (pEq lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardFormulaScoped_bot : forall scope,
  StandardFormulaScoped scope pBot.
Proof.
  intros scope index hfree. cbn [Formula.Free] in hfree. contradiction.
Qed.

Lemma standardFormulaScoped_imp : forall scope lhs rhs,
  StandardFormulaScoped scope lhs ->
  StandardFormulaScoped scope rhs ->
  StandardFormulaScoped scope (pImp lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardFormulaScoped_and : forall scope lhs rhs,
  StandardFormulaScoped scope lhs ->
  StandardFormulaScoped scope rhs ->
  StandardFormulaScoped scope (pAnd lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardFormulaScoped_or : forall scope lhs rhs,
  StandardFormulaScoped scope lhs ->
  StandardFormulaScoped scope rhs ->
  StandardFormulaScoped scope (pOr lhs rhs).
Proof.
  intros scope lhs rhs hlhs hrhs index [hfree | hfree].
  - exact (hlhs index hfree).
  - exact (hrhs index hfree).
Qed.

Lemma standardFormulaScoped_all : forall scope child,
  StandardFormulaScoped (S scope) child ->
  StandardFormulaScoped scope (pAll child).
Proof.
  intros scope child hchild index hfree.
  specialize (hchild (S index) hfree). lia.
Qed.

Lemma standardFormulaScoped_ex : forall scope child,
  StandardFormulaScoped (S scope) child ->
  StandardFormulaScoped scope (pEx child).
Proof.
  intros scope child hchild index hfree.
  specialize (hchild (S index) hfree). lia.
Qed.

(** The only shift needed by the dynamic source inserts a free slot at zero.
    Stating it separately keeps arithmetic obligations tiny. *)
Lemma standardFormulaScoped_shift_zero : forall scope amount input,
  StandardFormulaScoped scope input ->
  StandardFormulaScoped (amount + scope)
    (standardFormulaShift 0 amount input).
Proof.
  intros scope amount input hscope index hfree.
  rewrite standardFormulaShift_as_rename in hfree.
  destruct (standardFormulaFree_rename_preimage input
    (standardShiftRenaming 0 amount) index hfree)
    as [sourceIndex [hsource heq]].
  unfold standardShiftRenaming in heq.
  cbn in heq.
  specialize (hscope sourceIndex hsource). lia.
Qed.

End PABoundedRawCodedStandardFormulaScopeCombinators.
