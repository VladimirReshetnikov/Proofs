(** A small executable decision procedure for metatheoretic free-variable
    scopes, with proofs tied to the relational [Formula.Free] interface. *)

From Stdlib Require Import Arith Bool Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedScopedFormulaDiagonalSubstitution.

Module PABoundedRawCodedStandardFormulaScopeDecision.

Import PA.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.

Fixpoint standardTermScopedb (scope : nat) (input : term) : bool :=
  match input with
  | tVar index => index <? scope
  | tZero => true
  | tSucc child => standardTermScopedb scope child
  | tAdd lhs rhs | tMul lhs rhs =>
      standardTermScopedb scope lhs && standardTermScopedb scope rhs
  end.

Fixpoint standardFormulaScopedb (scope : nat) (input : formula) : bool :=
  match input with
  | pEq lhs rhs =>
      standardTermScopedb scope lhs && standardTermScopedb scope rhs
  | pBot => true
  | pImp lhs rhs | pAnd lhs rhs | pOr lhs rhs =>
      standardFormulaScopedb scope lhs &&
      standardFormulaScopedb scope rhs
  | pAll child | pEx child => standardFormulaScopedb (S scope) child
  end.

Lemma standardTermScopedb_spec : forall scope input,
  standardTermScopedb scope input = true <->
  StandardTermScoped scope input.
Proof.
  intros scope input.
  induction input as [index | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs];
    cbn [standardTermScopedb StandardTermScoped Term.Free].
  - rewrite Nat.ltb_lt. split.
    + intros h _ ->. exact h.
    + intros h. exact (h index eq_refl).
  - split.
    + intros htrue variable hfree. contradiction.
    + intros hscope. reflexivity.
  - exact IH.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
Qed.

Lemma standardFormulaScopedb_spec : forall scope input,
  standardFormulaScopedb scope input = true <->
  StandardFormulaScoped scope input.
Proof.
  intros scope input. revert scope.
  induction input as [lhs rhs | | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs |
      child IHchild | child IHchild]; intro scope;
    cbn [standardFormulaScopedb StandardFormulaScoped Formula.Free].
  - rewrite Bool.andb_true_iff,
      standardTermScopedb_spec, standardTermScopedb_spec.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
  - split.
    + intros htrue variable hfree. contradiction.
    + intros hscope. reflexivity.
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
  - rewrite Bool.andb_true_iff, IHlhs, IHrhs.
    split.
    + intros [hlhs hrhs] index [hfree | hfree].
      * exact (hlhs index hfree).
      * exact (hrhs index hfree).
    + intro h. split.
      * intros index hfree. exact (h index (or_introl hfree)).
      * intros index hfree. exact (h index (or_intror hfree)).
  - rewrite IHchild. split.
    + intros hchild index hfree.
      specialize (hchild (S index) hfree). lia.
    + intros houter [|index] hfree.
      * lia.
      * specialize (houter index hfree). lia.
  - rewrite IHchild. split.
    + intros hchild index hfree.
      specialize (hchild (S index) hfree). lia.
    + intros houter [|index] hfree.
      * lia.
      * specialize (houter index hfree). lia.
Qed.

End PABoundedRawCodedStandardFormulaScopeDecision.
