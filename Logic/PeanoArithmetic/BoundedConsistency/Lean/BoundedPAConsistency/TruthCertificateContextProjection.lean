import BoundedPAConsistency.TruthCertificateProofCompiler

/-!
# Projecting and changing truth-certificate contexts

The successor proof templates do not normally need every component of the
preceding six-field certificate.  For example, the cross-level induction uses
the preceding cross-level law, while substitution uses the preceding
substitution law.  Nevertheless `PAInductionKernel` deliberately has the
whole preceding master sentence as its context.

This module supplies the proof-code plumbing between those two interfaces.
Every projection below is an actual theorem of the internal Hilbert system,
not a meta-level implication.  `PAInductionKernel.recontextualize` then
precomposes both induction premises with such a theorem.  Consequently a
formula-specific template may be proved under the smallest field it needs
and later installed under the master-certificate context without inspecting
or decoding any model-coded formula.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

namespace TruthCertificateFields

variable {T : InternalTheory V ℒₒᵣ}

/-- The master conjunction proves its local-step component. -/
noncomputable def proveLocalStep (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.localStep :=
  Entailment.and₁

/-- The master conjunction proves its cross-level component. -/
noncomputable def proveCrossLevel (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.crossLevel :=
  Entailment.C_trans Entailment.and₂ Entailment.and₁

/-- The master conjunction proves its shift-invariance component. -/
noncomputable def proveShiftInvariant
    (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.shiftInvariant :=
  Entailment.C_trans Entailment.and₂ <|
    Entailment.C_trans Entailment.and₂ Entailment.and₁

/-- The master conjunction proves its substitution-invariance component. -/
noncomputable def proveSubstitutionInvariant
    (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.substitutionInvariant :=
  Entailment.C_trans Entailment.and₂ <|
    Entailment.C_trans Entailment.and₂ <|
      Entailment.C_trans Entailment.and₂ Entailment.and₁

/-- The master conjunction proves its PA-axiom-soundness component. -/
noncomputable def proveAxiomSound (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.axiomSound :=
  Entailment.C_trans Entailment.and₂ <|
    Entailment.C_trans Entailment.and₂ <|
      Entailment.C_trans Entailment.and₂ <|
        Entailment.C_trans Entailment.and₂ Entailment.and₁

/-- The master conjunction proves its final-consistency component. -/
noncomputable def proveFinalConsistency
    (F : TruthCertificateFields (V := V)) :
    T ⊢! F.sentence 🡒 F.finalConsistency :=
  Entailment.C_trans Entailment.and₂ <|
    Entailment.C_trans Entailment.and₂ <|
      Entailment.C_trans Entailment.and₂ <|
        Entailment.C_trans Entailment.and₂ Entailment.and₂

end TruthCertificateFields

variable [V↓[ℒₒᵣ] ⊧* Peano]

namespace PAInductionKernel

/-- Install an already proved universal field behind the induction-kernel
interface.

Some certificate fields are most naturally established by PA's internal
*structural* induction on formula codes.  Once that argument has produced
`context -> forall x, predicate x`, running a second numerical induction
would add no mathematical content.  This constructor derives the two
premises expected by `PAInductionKernel` from the universal theorem itself:
the zero instance is universal elimination, and the successor premise is a
fixed first-order consequence which simply ignores its redundant induction
hypothesis.

The returned kernel still compiles to the exact public universal closure, so
it can be used by the staged certificate compiler without changing that
interface or weakening its target. -/
noncomputable def ofUniversalProof
    {context : Bootstrapping.Formula V ℒₒᵣ}
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (shiftFixed : shift ℒₒᵣ predicate.val = predicate.val)
    (proof : Peano.internalize V ⊢! context 🡒 ∀⁰ predicate) :
    PAInductionKernel context where
  predicate := predicate
  shiftFixed := shiftFixed
  proveZero :=
    TProof.specializeWithCtxAux proof
      ⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝
  proveSuccessor :=
    Entailment.C_trans proof <| by
      classical
      apply TProof.generalizeAux
      have hall : Peano.internalize V ⊢!
          (∀⁰ predicate).shift 🡒 ∀⁰ predicate.shift := by
        simpa using
          (show Peano.internalize V ⊢!
              (∀⁰ predicate).shift 🡒 (∀⁰ predicate).shift from
            Entailment.C_id)
      have hsuccessor := TProof.specializeWithCtxAux hall
        (⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝ :
          Bootstrapping.Semiterm V ℒₒᵣ 1).free
      simpa [Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs,
        Bootstrapping.Semiformula.substs_substs] using
        (Entailment.C_swap
          (Entailment.C_of_conseq
            (ψ := predicate.free) hsuccessor))

/-- Change the closed context of an induction kernel along a represented PA
implication.

The predicate and its shift certificate are unchanged.  Only the two proof
premises are precomposed, so this operation adds no induction and performs no
syntax decoding. -/
noncomputable def recontextualize
    {outer inner : Bootstrapping.Formula V ℒₒᵣ}
    (h : Peano.internalize V ⊢! outer 🡒 inner)
    (kernel : PAInductionKernel inner) :
    PAInductionKernel outer where
  predicate := kernel.predicate
  shiftFixed := kernel.shiftFixed
  proveZero := Entailment.C_trans h kernel.proveZero
  proveSuccessor := Entailment.C_trans h kernel.proveSuccessor

/-- A kernel proved from the preceding local field can be installed under
the full preceding master certificate. -/
noncomputable def underLocalStep
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.localStep) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveLocalStep
      (T := Peano.internalize V) F) kernel

/-- A kernel proved from the preceding cross-level field can be installed
under the full preceding master certificate. -/
noncomputable def underCrossLevel
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.crossLevel) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveCrossLevel
      (T := Peano.internalize V) F) kernel

/-- A kernel proved from the preceding shift field can be installed under
the full preceding master certificate. -/
noncomputable def underShiftInvariant
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.shiftInvariant) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveShiftInvariant
      (T := Peano.internalize V) F) kernel

/-- A kernel proved from the preceding substitution field can be installed
under the full preceding master certificate. -/
noncomputable def underSubstitutionInvariant
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.substitutionInvariant) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveSubstitutionInvariant
      (T := Peano.internalize V) F) kernel

/-- A kernel proved from the preceding axiom-soundness field can be installed
under the full preceding master certificate. -/
noncomputable def underAxiomSound
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.axiomSound) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveAxiomSound
      (T := Peano.internalize V) F) kernel

/-- A kernel proved from the preceding final field can be installed under
the full preceding master certificate. -/
noncomputable def underFinalConsistency
    (F : TruthCertificateFields (V := V))
    (kernel : PAInductionKernel F.finalConsistency) :
    PAInductionKernel F.sentence :=
  recontextualize
    (TruthCertificateFields.proveFinalConsistency
      (T := Peano.internalize V) F) kernel

end PAInductionKernel

end LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection
