(**
  Induction syntax for the provability-valued compact selector package.

  Unlike direct induction on [Con_n(PA)], this predicate stores an ordinary
  PA proof certificate for [Con_n(PA)].  Induction over it therefore targets

      forall n, Prov_PA(code(Con_n(PA)))

  and does not assert uniform reflection.  The scope theorem imported below
  proves that the level is the package formula's only free variable.
*)

From Stdlib Require Import Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedNumeralTermCode
  RawCodedFormulaOperationsStandardAdequacy
  RawCodedPAAxiomWitness
  RawCodedFormulaDiagonalOperationComposition
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeTransport
  CompactPAUniformProvability
  RawCodedCompactSelectorScopes.

Module PABoundedRawCodedCompactSelectorInductionSyntax.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaOperationsStandardAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedFormulaDiagonalOperationComposition.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeTransport.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedCompactSelectorScopes.

Definition compactSelectorInductionSourceFormula : formula :=
  compactSelectorPackageFormula.

Definition compactSelectorInductionShiftedFormula : formula :=
  standardPAAxiomInductionShifted compactSelectorInductionSourceFormula.

Definition compactSelectorInductionSuccessorFormula : formula :=
  standardPAAxiomInductionSuccessorInstance
    compactSelectorInductionSourceFormula.

Definition compactSelectorInductionZeroFormula : formula :=
  standardPAAxiomInductionZeroInstance compactSelectorInductionSourceFormula.

Definition compactSelectorInductionStepFormula : formula :=
  pAll (pImp
    compactSelectorInductionSourceFormula
    compactSelectorInductionSuccessorFormula).

Definition compactSelectorInductionBodyFormula : formula :=
  standardPAAxiomInductionBody compactSelectorInductionSourceFormula.

Definition compactSelectorInductionAxiomFormula : formula :=
  Formula.sealPA compactSelectorInductionBodyFormula.

Lemma compactSelectorInductionSourceFormula_scoped :
  StandardFormulaScoped 1 compactSelectorInductionSourceFormula.
Proof.
  exact compactSelectorPackageFormula_scoped_one.
Qed.

Lemma compactSelectorInductionSuccessorFormula_scoped :
  StandardFormulaScoped 1 compactSelectorInductionSuccessorFormula.
Proof.
  unfold compactSelectorInductionSuccessorFormula,
    standardPAAxiomInductionSuccessorInstance.
  rewrite standardFormulaShift_one_one_then_substitute_succ.
  apply (standardFormulaSubstitution_scoped 1 1
    compactSelectorInductionSourceFormula Formula.substSuccVar).
  - exact compactSelectorInductionSourceFormula_scoped.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.substSuccVar Term.Free] in hfree.
    lia.
Qed.

Lemma compactSelectorInductionZeroFormula_closed :
  StandardFormulaScoped 0 compactSelectorInductionZeroFormula.
Proof.
  unfold compactSelectorInductionZeroFormula,
    standardPAAxiomInductionZeroInstance.
  rewrite standardFormulaSingleSubstitution_zero.
  apply (standardFormulaSubstitution_scoped 1 0
    compactSelectorInductionSourceFormula (Formula.instTerm tZero)).
  - exact compactSelectorInductionSourceFormula_scoped.
  - intros [|sourceIndex] hindex; [|lia].
    intros index hfree.
    cbn [Formula.instTerm Term.Free] in hfree. contradiction.
Qed.

Lemma compactSelectorInductionBodyFormula_closed :
  StandardFormulaScoped 0 compactSelectorInductionBodyFormula.
Proof.
  unfold compactSelectorInductionBodyFormula,
    standardPAAxiomInductionBody.
  intros index hfree.
  cbn [Formula.Free] in hfree.
  destruct hfree as [[hzero | hstep] | hsource].
  - exact (compactSelectorInductionZeroFormula_closed index hzero).
  - destruct hstep as [hsource | hsuccessor].
    + pose proof
        (compactSelectorInductionSourceFormula_scoped
          (S index) hsource). lia.
    + pose proof
        (compactSelectorInductionSuccessorFormula_scoped
          (S index) hsuccessor). lia.
  - pose proof
      (compactSelectorInductionSourceFormula_scoped
        (S index) hsource). lia.
Qed.

(** The generic closure-induction compiler needs a diagonal certificate for
    its body.  Each component follows from the one-variable source scope;
    no semantic induction case is assumed here. *)
Theorem raw_codedCompactSelectorInductionBody_diagonal : forall
    (M : RawPAModel), RawPASatisfies M -> forall numeralBound numeralCode,
  RawNumeralTermCodeAt M numeralBound numeralCode ->
  RawCodedFormulaDiagonalSubstitutionAtAllDepths M numeralCode
    (rawQuotedFormulaCode M compactSelectorInductionBodyFormula).
Proof.
  intros M hPA numeralBound numeralCode hnumeral.
  unfold compactSelectorInductionBodyFormula,
    standardPAAxiomInductionBody.
  apply (raw_codedFormulaDiagonalSubstitutionAtAllDepths_inductionBody
    M hPA numeralCode
    (rawQuotedFormulaCode M compactSelectorInductionSourceFormula)
    (rawQuotedFormulaCode M compactSelectorInductionSuccessorFormula)
    (rawQuotedFormulaCode M compactSelectorInductionZeroFormula)).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      compactSelectorInductionSourceFormula hnumeral
      compactSelectorInductionSourceFormula_scoped).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_positive
      M hPA numeralBound numeralCode
      compactSelectorInductionSuccessorFormula hnumeral
      compactSelectorInductionSuccessorFormula_scoped).
  - exact (raw_codedFormulaDiagonalSubstitution_standard_closed
      M hPA numeralBound numeralCode
      compactSelectorInductionZeroFormula hnumeral
      compactSelectorInductionZeroFormula_closed).
Qed.

End PABoundedRawCodedCompactSelectorInductionSyntax.
