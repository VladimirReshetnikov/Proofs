(** Scope certificates for the proof-constructor occurrence cases. *)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedTargetDomainContextScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Module PABoundedRawCodedRestrictedTargetOccurrenceContextScopes.

Import PA.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedTargetDomainContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Definition RestrictedTargetOccurrenceCaseScoped
    (scope : nat) (entry : term * list term) : Prop :=
  StandardTermScoped scope (fst entry) /\
  Forall (StandardTermScoped scope) (snd entry).

Lemma restrictedTargetProofOccurrenceCasesBoundedContext_scoped : forall
    scope code context cases,
  StandardTermScoped scope code ->
  StandardTermScoped scope context ->
  Forall (RestrictedTargetOccurrenceCaseScoped scope) cases ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofOccurrenceCasesBoundedContext
      code context cases).
Proof.
  intros scope code context cases hcode hcontext hcases.
  induction hcases as [|[constructorCode fields] tail
      [hconstructor hfields] htail IH].
  - cbn [restrictedTargetProofOccurrenceCasesBoundedContext
      RestrictedTargetFormulaContextScoped].
    apply standardFormulaScoped_eq;
      apply standardTermScoped_zero.
  - cbn [restrictedTargetProofOccurrenceCasesBoundedContext
      RestrictedTargetFormulaContextScoped].
    split.
    + split.
      * now apply standardFormulaScoped_eq.
      * split.
        -- now apply restrictedTargetContextAllBoundedContext_scoped.
        -- now apply restrictedTargetProofFormulaFieldsBoundedContext_scoped.
    + exact IH.
Qed.

(** The finite constructor table contains only arithmetic codes built from
    its eight parameters.  This is checked once here instead of once per
    occurrence of the table in the dynamic source. *)
Lemma proofOccurrenceCasesTerms_scoped : forall
    scope context a b c witness child1 child2 child3,
  StandardTermScoped scope context ->
  StandardTermScoped scope a ->
  StandardTermScoped scope b ->
  StandardTermScoped scope c ->
  StandardTermScoped scope witness ->
  StandardTermScoped scope child1 ->
  StandardTermScoped scope child2 ->
  StandardTermScoped scope child3 ->
  Forall (RestrictedTargetOccurrenceCaseScoped scope)
    (proofOccurrenceCasesTerms
      context a b c witness child1 child2 child3).
Proof.
  intros scope context a b c witness child1 child2 child3
    hcontext ha hb hc hwitness hchild1 hchild2 hchild3.
  unfold proofOccurrenceCasesTerms,
    RestrictedTargetOccurrenceCaseScoped.
  repeat constructor;
    try assumption;
    try raw_scope_term.
Qed.

Lemma restrictedTargetProofConstructorOccurrencesBoundedContext_scoped :
    forall scope code,
  StandardTermScoped scope code ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofConstructorOccurrencesBoundedContext code).
Proof.
  intros scope code hcode.
  unfold restrictedTargetProofConstructorOccurrencesBoundedContext.
  cbn [restrictedTargetAllN RestrictedTargetFormulaContextScoped].
  apply restrictedTargetProofOccurrenceCasesBoundedContext_scoped.
  - raw_scope_term.
  - raw_scope_term.
  - apply proofOccurrenceCasesTerms_scoped; raw_scope_term.
Qed.

End PABoundedRawCodedRestrictedTargetOccurrenceContextScopes.
