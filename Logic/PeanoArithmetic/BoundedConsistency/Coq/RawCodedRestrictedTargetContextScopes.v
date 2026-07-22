(**
  Generic scope transport for restricted-target contexts.

  A dynamic source inserts one new free level variable while shifting each
  fixed syntax leaf at the current binder depth.  The predicates below state
  exactly the scope obligations on those opaque leaves.  Their realization
  theorem is independent of the concrete restricted-proof context.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedTermOperationsStandardAdequacy
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport
  RawCodedStandardFormulaScopeCombinators.

Module PABoundedRawCodedRestrictedTargetContextScopes.

Import PA.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.
Import PABoundedRawCodedStandardFormulaScopeCombinators.

(** A shift at an arbitrary cutoff can increase every free index by at most
    one.  These lemmas prevent reduction of fixed quotation leaves. *)
Lemma standardTermScoped_shift_one_any_cutoff : forall scope cutoff input,
  StandardTermScoped scope input ->
  StandardTermScoped (S scope) (standardTermShift cutoff 1 input).
Proof.
  intros scope cutoff input hscope index hfree.
  rewrite standardTermShift_as_rename in hfree.
  destruct (standardTermFree_rename_preimage input
    (standardShiftRenaming cutoff 1) index hfree)
    as [sourceIndex [hsource heq]].
  specialize (hscope sourceIndex hsource).
  unfold standardShiftRenaming in heq.
  destruct (sourceIndex <? cutoff); lia.
Qed.

Lemma standardFormulaScoped_shift_one_any_cutoff :
    forall scope cutoff input,
  StandardFormulaScoped scope input ->
  StandardFormulaScoped (S scope)
    (standardFormulaShift cutoff 1 input).
Proof.
  intros scope cutoff input hscope index hfree.
  rewrite standardFormulaShift_as_rename in hfree.
  destruct (standardFormulaFree_rename_preimage input
    (standardShiftRenaming cutoff 1) index hfree)
    as [sourceIndex [hsource heq]].
  specialize (hscope sourceIndex hsource).
  unfold standardShiftRenaming in heq.
  destruct (sourceIndex <? cutoff); lia.
Qed.

Fixpoint RestrictedTargetTermContextScoped
    (scope : nat) (context : RestrictedTargetTermContext) : Prop :=
  match context with
  | RTTCFixed fixed => StandardTermScoped scope fixed
  | RTTCHole => True
  | RTTCSucc child => RestrictedTargetTermContextScoped scope child
  | RTTCAdd lhs rhs
  | RTTCMul lhs rhs =>
      RestrictedTargetTermContextScoped scope lhs /\
      RestrictedTargetTermContextScoped scope rhs
  end.

Fixpoint RestrictedTargetFormulaContextScoped
    (scope : nat) (context : RestrictedTargetFormulaContext) : Prop :=
  match context with
  | RTFCFixed fixed => StandardFormulaScoped scope fixed
  | RTFCBot => True
  | RTFCEq lhs rhs =>
      RestrictedTargetTermContextScoped scope lhs /\
      RestrictedTargetTermContextScoped scope rhs
  | RTFCImp lhs rhs
  | RTFCAnd lhs rhs
  | RTFCOr lhs rhs =>
      RestrictedTargetFormulaContextScoped scope lhs /\
      RestrictedTargetFormulaContextScoped scope rhs
  | RTFCAll child
  | RTFCEx child => RestrictedTargetFormulaContextScoped (S scope) child
  | RTFCSeal _ => True
  end.

Lemma restrictedPADynamicSourceTermContext_scoped : forall
    context scope depth,
  depth <= scope ->
  RestrictedTargetTermContextScoped scope context ->
  StandardTermScoped (S scope)
    (restrictedPADynamicSourceTermContext depth context).
Proof.
  induction context as [fixed | | child IH | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs]; intros scope depth hdepth hcontext;
    cbn [RestrictedTargetTermContextScoped
      restrictedPADynamicSourceTermContext] in *.
  - now apply standardTermScoped_shift_one_any_cutoff.
  - apply standardTermScoped_var. lia.
  - apply standardTermScoped_succ. now apply IH.
  - destruct hcontext as [hlhs hrhs].
    apply standardTermScoped_add.
    + now apply IHlhs.
    + now apply IHrhs.
  - destruct hcontext as [hlhs hrhs].
    apply standardTermScoped_mul.
    + now apply IHlhs.
    + now apply IHrhs.
Qed.

Lemma restrictedPADynamicSourceFormulaContext_scoped : forall
    context scope depth,
  depth <= scope ->
  RestrictedTargetFormulaContextScoped scope context ->
  StandardFormulaScoped (S scope)
    (restrictedPADynamicSourceFormulaContext depth context).
Proof.
  induction context as [fixed | | lhs rhs | lhs IHlhs rhs IHrhs |
      lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs | child IH |
      child IH | sealed]; intros scope depth hdepth hcontext;
    cbn [RestrictedTargetFormulaContextScoped
      restrictedPADynamicSourceFormulaContext] in *.
  - now apply standardFormulaScoped_shift_one_any_cutoff.
  - apply standardFormulaScoped_bot.
  - destruct hcontext as [hlhs hrhs].
    apply standardFormulaScoped_eq.
    + now apply restrictedPADynamicSourceTermContext_scoped.
    + now apply restrictedPADynamicSourceTermContext_scoped.
  - destruct hcontext as [hlhs hrhs].
    apply standardFormulaScoped_imp.
    + now apply IHlhs.
    + now apply IHrhs.
  - destruct hcontext as [hlhs hrhs].
    apply standardFormulaScoped_and.
    + now apply IHlhs.
    + now apply IHrhs.
  - destruct hcontext as [hlhs hrhs].
    apply standardFormulaScoped_or.
    + now apply IHlhs.
    + now apply IHrhs.
  - apply standardFormulaScoped_all.
    apply IH; [lia | exact hcontext].
  - apply standardFormulaScoped_ex.
    apply IH; [lia | exact hcontext].
  - apply standardFormulaScoped_bot.
Qed.

End PABoundedRawCodedRestrictedTargetContextScopes.
