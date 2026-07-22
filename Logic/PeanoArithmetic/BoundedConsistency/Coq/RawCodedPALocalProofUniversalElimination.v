(** Universal elimination in an arbitrary model-coded proof context. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedProofAllEConstructor RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofUniversalElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedPALocalProofExistential.

Theorem raw_codedPALocalProofOf_allE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement conclusion child,
  RawCodedPALocalProofOf M context
    (rawFormulaAllCode M body) child ->
  RawCodedFormulaSingleSubstitution M replacement body conclusion ->
  RawCodedPALocalProofOf M context conclusion
    (rawProofAllERoot M context body replacement child).
Proof.
  intros M hPA context body replacement conclusion child
    [hchildCoverage hchildEndpoint] hsubstitution.
  split.
  - exact (raw_proofAllE_ruleCoverage M hPA
      context body replacement child hchildCoverage hchildEndpoint).
  - exact (raw_proofAllE_endpoint M
      context body replacement conclusion child hsubstitution).
Qed.

End PABoundedRawCodedPALocalProofUniversalElimination.
