(** Scope certificates for the reusable quantifier-bound contexts. *)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Module PABoundedRawCodedRestrictedTargetDomainContextScopes.

Import PA.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Lemma restrictedTargetLeContext_scoped : forall scope lhs,
  StandardTermScoped scope lhs ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetLeContext lhs).
Proof.
  intros scope lhs hlhs.
  unfold restrictedTargetLeContext.
  cbn [RestrictedTargetFormulaContextScoped
    RestrictedTargetTermContextScoped].
  split; [|exact I].
  apply standardTermScoped_add.
  - exact (standardTermScoped_rename_succ scope lhs hlhs).
  - apply standardTermScoped_var. lia.
Qed.

Lemma restrictedTargetSigmaDomainContext_scoped : forall scope code,
  StandardTermScoped scope code ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetSigmaDomainContext code).
Proof.
  intros scope code hcode.
  unfold restrictedTargetSigmaDomainContext.
  cbn [restrictedTargetExN RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - apply restrictedTargetLeContext_scoped. raw_scope_term.
Qed.

Lemma restrictedTargetPiDomainContext_scoped : forall scope code,
  StandardTermScoped scope code ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetPiDomainContext code).
Proof.
  intros scope code hcode.
  unfold restrictedTargetPiDomainContext.
  cbn [restrictedTargetExN RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - apply restrictedTargetLeContext_scoped. raw_scope_term.
Qed.

Lemma restrictedTargetFormulaQuantifierBoundedContext_scoped :
    forall scope code,
  StandardTermScoped scope code ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetFormulaQuantifierBoundedContext code).
Proof.
  intros scope code hcode.
  unfold restrictedTargetFormulaQuantifierBoundedContext.
  cbn [RestrictedTargetFormulaContextScoped].
  split.
  - now apply restrictedTargetSigmaDomainContext_scoped.
  - now apply restrictedTargetPiDomainContext_scoped.
Qed.

Lemma restrictedTargetContextAllBoundedWithTablesContext_scoped : forall
    scope bound headCode headStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope headCode ->
  StandardTermScoped scope headStep ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetContextAllBoundedWithTablesContext
      bound headCode headStep).
Proof.
  intros scope bound headCode headStep hbound hheadCode hheadStep.
  unfold restrictedTargetContextAllBoundedWithTablesContext.
  cbn [RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - split.
    + raw_scope_formula.
    + apply restrictedTargetFormulaQuantifierBoundedContext_scoped.
      raw_scope_term.
Qed.

Lemma restrictedTargetContextAllBoundedContext_scoped : forall scope root,
  StandardTermScoped scope root ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetContextAllBoundedContext root).
Proof.
  intros scope root hroot.
  unfold restrictedTargetContextAllBoundedContext.
  cbn [restrictedTargetExN RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - apply restrictedTargetContextAllBoundedWithTablesContext_scoped;
      raw_scope_term.
Qed.

Lemma restrictedTargetProofFormulaFieldsBoundedContext_scoped : forall
    scope fields,
  Forall (StandardTermScoped scope) fields ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofFormulaFieldsBoundedContext fields).
Proof.
  intros scope fields hfields.
  induction hfields as [|field tail hfield htail IH].
  - cbn [restrictedTargetProofFormulaFieldsBoundedContext
      RestrictedTargetFormulaContextScoped].
    apply standardFormulaScoped_eq;
      apply standardTermScoped_zero.
  - cbn [restrictedTargetProofFormulaFieldsBoundedContext
      RestrictedTargetFormulaContextScoped].
    split.
    + now apply restrictedTargetFormulaQuantifierBoundedContext_scoped.
    + exact IH.
Qed.

End PABoundedRawCodedRestrictedTargetDomainContextScopes.
