(** Scope certificates for the restricted proof context, assembled from the
    reusable domain and constructor-occurrence certificates. *)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedProofTraversal
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedTargetDomainContextScopes
  RawCodedRestrictedTargetOccurrenceContextScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Module PABoundedRawCodedRestrictedTargetProofContextScopes.

Import PA.
Import PABoundedRawCodedRestrictedProofTraversal.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedTargetDomainContextScopes.
Import PABoundedRawCodedRestrictedTargetOccurrenceContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Lemma restrictedTargetProofEndpointOccurrencesBoundedContext_scoped :
    forall scope code,
  StandardTermScoped scope code ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofEndpointOccurrencesBoundedContext code).
Proof.
  intros scope code hcode.
  unfold restrictedTargetProofEndpointOccurrencesBoundedContext.
  cbn [restrictedTargetAllN RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - split.
    + apply restrictedTargetContextAllBoundedContext_scoped.
      raw_scope_term.
    + apply restrictedTargetFormulaQuantifierBoundedContext_scoped.
      raw_scope_term.
Qed.

Lemma restrictedTargetProofNodeContext_scoped : forall
    scope code supportCode supportStep,
  StandardTermScoped scope code ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofNodeContext code supportCode supportStep).
Proof.
  intros scope code supportCode supportStep hcode hsupportCode hsupportStep.
  unfold restrictedTargetProofNodeContext.
  cbn [RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - split.
    + raw_scope_formula.
    + split.
      * now apply
          restrictedTargetProofConstructorOccurrencesBoundedContext_scoped.
      * now apply
          restrictedTargetProofEndpointOccurrencesBoundedContext_scoped.
Qed.

Lemma restrictedTargetProofTraversalContext_scoped : forall
    scope bound supportCode supportStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofTraversalContext bound supportCode supportStep).
Proof.
  intros scope bound supportCode supportStep hbound hsupportCode hsupportStep.
  unfold restrictedTargetProofTraversalContext.
  cbn [RestrictedTargetFormulaContextScoped].
  split.
  - raw_scope_formula.
  - split.
    + raw_scope_formula.
    + split.
      * raw_scope_formula.
      * apply restrictedTargetProofNodeContext_scoped;
          raw_scope_term.
Qed.

Lemma restrictedTargetProofCertificateWithSupportContext_scoped : forall
    scope root supportCode supportStep,
  StandardTermScoped scope root ->
  StandardTermScoped scope supportCode ->
  StandardTermScoped scope supportStep ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofCertificateWithSupportContext
      root supportCode supportStep).
Proof.
  intros scope root supportCode supportStep hroot hsupportCode hsupportStep.
  unfold restrictedTargetProofCertificateWithSupportContext.
  cbn [RestrictedTargetFormulaContextScoped].
  split.
  - apply restrictedTargetProofTraversalContext_scoped;
      raw_scope_term.
  - raw_scope_formula.
Qed.

Theorem restrictedTargetProofContext_scoped : forall scope root,
  StandardTermScoped scope root ->
  RestrictedTargetFormulaContextScoped scope
    (restrictedTargetProofContext root).
Proof.
  intros scope root hroot.
  unfold restrictedTargetProofContext.
  cbn [restrictedTargetExN RestrictedTargetFormulaContextScoped].
  apply restrictedTargetProofCertificateWithSupportContext_scoped;
    raw_scope_term.
Qed.

End PABoundedRawCodedRestrictedTargetProofContextScopes.
