(**
  Propositional composition in an arbitrary model-coded proof context.

  [RawCodedPAOpenProofComposition] already supplies implication and bottom
  elimination when the context has the distinguished shape

      assumption :: witnessed-PA-context.

  After the three existential eliminations used by the restricted-
  consistency compiler, however, the context contains several temporary
  assumptions.  The smaller [RawCodedPALocalProofOf] package is the right
  interface there.  The two constructors below deliberately retain the
  context verbatim and merely put the corresponding honest raw proof node
  over already covered children.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofUnaryConstructors
  RawCodedProofBinaryConstructors RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofComposition.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.

(** Bottom elimination does not inspect the temporary context. *)
Theorem raw_codedPALocalProofOf_botE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context child,
  RawCodedPALocalProofOf M context (rawFormulaBotCode M) child ->
  forall target,
  RawCodedPALocalProofOf M context target
    (rawProofBotERoot M context target child).
Proof.
  intros M hPA context child [hcoverage hendpoint] target.
  split.
  - exact (raw_proofBotE_ruleCoverage M hPA
      context target child hcoverage hendpoint).
  - exact (raw_proofBotE_endpoint M context target child).
Qed.

(** Modus ponens for two local proofs sharing exactly the same context. *)
Theorem raw_codedPALocalProofOf_impE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M antecedent consequent) impChild ->
  RawCodedPALocalProofOf M context antecedent antecedentChild ->
  RawCodedPALocalProofOf M context consequent
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    [himpCoverage himpEndpoint]
    [hantecedentCoverage hantecedentEndpoint].
  split.
  - exact (raw_proofImpE_ruleCoverage M hPA
      context antecedent consequent impChild antecedentChild
      himpCoverage himpEndpoint
      hantecedentCoverage hantecedentEndpoint).
  - exact (raw_proofImpE_endpoint M
      context antecedent consequent impChild antecedentChild).
Qed.

End PABoundedRawCodedPALocalProofComposition.
