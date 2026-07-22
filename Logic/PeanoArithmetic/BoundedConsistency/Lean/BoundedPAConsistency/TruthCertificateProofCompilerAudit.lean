import BoundedPAConsistency.TruthCertificateProofCompiler

/-! Kernel-facing audit for the typed truth-certificate proof compiler. -/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateProofCompilerAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

#check TruthCertificateFields
#check TruthCertificateFields.sentence
#check TruthCertificateFields.intro
#check TruthCertificateFields.localStepProof
#check TruthCertificateFields.crossLevelProof
#check TruthCertificateFields.shiftInvariantProof
#check TruthCertificateFields.substitutionInvariantProof
#check TruthCertificateFields.axiomSoundProof
#check TruthCertificateFields.finalConsistencyProof
#check TruthCertificateStep
#check TruthCertificateStep.compile
#check TruthCertificateStep.compile_isProof
#check PAInductionKernel
#check PAInductionKernel.compile
#check PAInductionKernel.compileImplication
#check PAInductionKernel.compileViaImplication
#check PAInductiveTruthCertificateStep
#check PAInductiveTruthCertificateStep.target
#check PAInductiveTruthCertificateStep.compile
#check PAInductiveTruthCertificateStep.compile_isProof
#check PAInductiveTruthCertificateStep.compile_isPAProof

#print axioms TruthCertificateFields.intro
#print axioms TruthCertificateStep.compile
#print axioms TruthCertificateStep.compile_isProof
#print axioms PAInductionKernel.compile
#print axioms PAInductionKernel.compileImplication
#print axioms PAInductionKernel.compileViaImplication
#print axioms PAInductiveTruthCertificateStep.compile
#print axioms PAInductiveTruthCertificateStep.compile_isPAProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The packer and the final-field projection compose at the typed proof
level, so no semantic decoding of a package is needed. -/
noncomputable example (F : TruthCertificateFields (V := V))
    (hlocal : Peano.internalize V ⊢! F.localStep)
    (hcross : Peano.internalize V ⊢! F.crossLevel)
    (hshift : Peano.internalize V ⊢! F.shiftInvariant)
    (hsubst : Peano.internalize V ⊢! F.substitutionInvariant)
    (haxiom : Peano.internalize V ⊢! F.axiomSound)
    (hfinal : Peano.internalize V ⊢! F.finalConsistency) :
    Peano.internalize V ⊢! F.finalConsistency :=
  F.finalConsistencyProof
    (F.intro hlocal hcross hshift hsubst haxiom hfinal)

/-- The specialized successor's `.val` is a proof code for exactly its
model-coded target certificate. -/
example {previous : TruthCertificateFields (V := V)}
    (step : PAInductiveTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Proof Peano (step.compile hprevious).val step.target.sentence.val :=
  step.compile_isPAProof hprevious

end LeanProofs.BoundedPAConsistency.TruthCertificateProofCompilerAudit
