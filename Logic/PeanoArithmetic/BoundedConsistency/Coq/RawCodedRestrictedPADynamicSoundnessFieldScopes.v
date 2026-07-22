(**
  Opaque scope certificates for the fixed dynamic-soundness checker fields.

  This file begins with the PA-axiom/context field.  Its proof follows the
  represented beta tables compositionally and never normalizes the enormous
  closed numerals occurring in finite axiom tags.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAProof
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedBasicFormulaScopes
  RawCodedContextListScopes
  RawCodedPAAxiomWitnessScopes.

Module PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.

Import PA.
Import PAListRepresentability.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedBasicFormulaScopes.
Import PABoundedRawCodedContextListScopes.
Import PABoundedRawCodedPAAxiomWitnessScopes.

Lemma standardFormulaScoped_codedPAAxiomWitnessContextRowsTermAt :
    forall scope bound witnessHeadCode witnessHeadStep
      axiomHeadCode axiomHeadStep,
  StandardTermScoped scope bound ->
  StandardTermScoped scope witnessHeadCode ->
  StandardTermScoped scope witnessHeadStep ->
  StandardTermScoped scope axiomHeadCode ->
  StandardTermScoped scope axiomHeadStep ->
  StandardFormulaScoped scope
    (codedPAAxiomWitnessContextRowsTermAt bound
      witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep).
Proof.
  intros scope bound witnessHeadCode witnessHeadStep
    axiomHeadCode axiomHeadStep hbound hwitnessCode hwitnessStep
    haxiomCode haxiomStep.
  unfold codedPAAxiomWitnessContextRowsTermAt, restrictedPAAll3.
  repeat apply standardFormulaScoped_all.
  apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_ltTermAt.
    + apply standardTermScoped_var; lia.
    + exact (standardTermScoped_lift scope 3 bound hbound).
  - apply standardFormulaScoped_imp.
    + apply standardFormulaScoped_codedAssignmentLookupTermAt.
      * exact (standardTermScoped_lift
          scope 3 witnessHeadCode hwitnessCode).
      * exact (standardTermScoped_lift
          scope 3 witnessHeadStep hwitnessStep).
      * apply standardTermScoped_var; lia.
      * apply standardTermScoped_var; lia.
    + apply standardFormulaScoped_imp.
      * apply standardFormulaScoped_codedAssignmentLookupTermAt.
        -- exact (standardTermScoped_lift
             scope 3 axiomHeadCode haxiomCode).
        -- exact (standardTermScoped_lift
             scope 3 axiomHeadStep haxiomStep).
        -- apply standardTermScoped_var; lia.
        -- apply standardTermScoped_var; lia.
      * apply standardFormulaScoped_codedPAAxiomWitnessTermAt;
          apply standardTermScoped_var; lia.
Qed.

Lemma standardFormulaScoped_codedPAAxiomWitnessContextWithTablesTermAt :
    forall scope witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep,
  StandardTermScoped scope witnessList ->
  StandardTermScoped scope context ->
  StandardTermScoped scope bound ->
  StandardTermScoped scope witnessTailCode ->
  StandardTermScoped scope witnessTailStep ->
  StandardTermScoped scope witnessHeadCode ->
  StandardTermScoped scope witnessHeadStep ->
  StandardTermScoped scope axiomTailCode ->
  StandardTermScoped scope axiomTailStep ->
  StandardTermScoped scope axiomHeadCode ->
  StandardTermScoped scope axiomHeadStep ->
  StandardFormulaScoped scope
    (codedPAAxiomWitnessContextWithTablesTermAt witnessList context bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep).
Proof.
  intros scope witnessList context bound witnessTailCode witnessTailStep
    witnessHeadCode witnessHeadStep axiomTailCode axiomTailStep
    axiomHeadCode axiomHeadStep hwitnessList hcontext hbound
    hwitnessTailCode hwitnessTailStep hwitnessHeadCode hwitnessHeadStep
    haxiomTailCode haxiomTailStep haxiomHeadCode haxiomHeadStep.
  unfold codedPAAxiomWitnessContextWithTablesTermAt, restrictedPAAnd3.
  apply standardFormulaScoped_and.
  - apply standardFormulaScoped_contextListTraversalTermAt; assumption.
  - apply standardFormulaScoped_and.
    + apply standardFormulaScoped_contextListTraversalTermAt; assumption.
    + apply standardFormulaScoped_codedPAAxiomWitnessContextRowsTermAt;
        assumption.
Qed.

Lemma standardFormulaScoped_codedPAAxiomWitnessContextTermAt : forall scope
    witnessList context,
  StandardTermScoped scope witnessList ->
  StandardTermScoped scope context ->
  StandardFormulaScoped scope
    (codedPAAxiomWitnessContextTermAt witnessList context).
Proof.
  intros scope witnessList context hwitnessList hcontext.
  unfold codedPAAxiomWitnessContextTermAt, restrictedPAEx9.
  repeat apply standardFormulaScoped_ex.
  apply standardFormulaScoped_codedPAAxiomWitnessContextWithTablesTermAt.
  - exact (standardTermScoped_lift scope 9 witnessList hwitnessList).
  - exact (standardTermScoped_lift scope 9 context hcontext).
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
  - apply standardTermScoped_var; lia.
Qed.

Theorem codedPAAxiomWitnessContextTermAt_scoped_three :
  StandardFormulaScoped 3
    (codedPAAxiomWitnessContextTermAt (tVar 2) (tVar 0)).
Proof.
  apply standardFormulaScoped_codedPAAxiomWitnessContextTermAt;
    apply standardTermScoped_var; lia.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.
