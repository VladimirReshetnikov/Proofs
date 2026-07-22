(**
  Compositional scope certificate for the dynamic-soundness source.

  The occurrence premise is obtained from the generic dynamic-context scope
  theorem and the separately cached restricted-proof context certificate.
  The remaining five premises are ordinary three-slot formulae shifted once
  at cutoff zero.  No reflected computation expands a quoted syntax numeral.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeCombinators
  RawCodedRestrictedTargetContextScopes
  RawCodedRestrictedTargetProofContextScopes
  RawCodedRestrictedPADynamicSoundnessFieldScopes
  RawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Module PABoundedRawCodedRestrictedPADynamicSoundnessSourceScope.

Import PA.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeCombinators.
Import PABoundedRawCodedRestrictedTargetContextScopes.
Import PABoundedRawCodedRestrictedTargetProofContextScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessFieldScopes.
Import PABoundedRawCodedRestrictedPADynamicSoundnessRemainingFieldScopes.

Lemma restrictedPADynamicOccurrenceSourceFormula_scoped_four :
  StandardFormulaScoped 4 restrictedPADynamicOccurrenceSourceFormula.
Proof.
  unfold restrictedPADynamicOccurrenceSourceFormula.
  apply (restrictedPADynamicSourceFormulaContext_scoped
    (restrictedTargetProofContext (tVar 1)) 3 0).
  - lia.
  - apply restrictedTargetProofContext_scoped.
    apply standardTermScoped_var. lia.
Qed.

Theorem restrictedPADynamicSoundnessSourceFormula_scoped_four :
  StandardFormulaScoped 4 restrictedPADynamicSoundnessSourceFormula.
Proof.
  unfold restrictedPADynamicSoundnessSourceFormula.
  repeat apply standardFormulaScoped_imp.
  - apply standardFormulaScoped_shift_zero.
    exact codedPAAxiomWitnessContextTermAt_scoped_three.
  - exact restrictedPADynamicOccurrenceSourceFormula_scoped_four.
  - apply standardFormulaScoped_shift_zero.
    exact proofAtomicallyAdequateTermAt_scoped_three.
  - apply standardFormulaScoped_shift_zero.
    exact proofHasFormulaCoverageTermAt_scoped_three.
  - apply standardFormulaScoped_shift_zero.
    exact proofRuleCoverageTermAt_scoped_three.
  - apply standardFormulaScoped_shift_zero.
    exact proofRuleValidTermAt_scoped_three.
  - apply standardFormulaScoped_bot.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessSourceScope.
