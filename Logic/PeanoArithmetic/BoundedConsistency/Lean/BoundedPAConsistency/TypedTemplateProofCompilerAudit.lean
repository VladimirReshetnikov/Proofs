import BoundedPAConsistency.TypedTemplateProofCompiler

/-!
# Kernel audit for specialization of standard proof templates

The checks in this file expose the small interface consumed by the future
partial-truth proof templates.  In particular, the final example verifies
that compiling a standard derivation produces a carrier accepted by the
represented target proof predicate even when the translated formulas are
arbitrary model-coded syntax.
-/

namespace LeanProofs.BoundedPAConsistency.TypedTemplateProofCompilerAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TypedTemplateProofCompiler

#check TypedTemplateTranslation
#check TypedTemplateTranslation.translateList
#check TypedTemplateTranslation.translateSequent
#check TypedTemplateTranslation.mem_translateSequent_iff
#check TypedTemplateTranslation.translateSequent_insert
#check TypedTemplateTranslation.translateSequent_image_shift
#check TypedTheoryTemplateTranslation
#check TypedTheoryTemplateTranslation.compileDerivation
#check TypedTheoryTemplateTranslation.compileProof
#check TypedTheoryTemplateTranslation.compileProof_isProof

#print axioms TypedTemplateTranslation.mem_translateSequent_iff
#print axioms TypedTemplateTranslation.translateSequent_image_shift
#print axioms TypedTheoryTemplateTranslation.compileDerivation
#print axioms TypedTheoryTemplateTranslation.compileProof
#print axioms TypedTheoryTemplateTranslation.compileProof_isProof

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L₁ L₂ : Language}
variable [L₁.DecidableEq] [L₂.Encodable] [L₂.LORDefinable]
variable {T₁ : Theory L₁} {T₂ : InternalTheory V L₂}

/-- The public compiler theorem states the exact represented-proof judgment,
not merely well-formedness of the generated syntax tree. -/
example (tr : TypedTheoryTemplateTranslation T₁ T₂)
    {sigma : Sentence L₁} (d : T₁ ⊢! sigma) :
    Proof T₂.theory (tr.compileProof d).val
      (tr.formula (Rewriting.emb sigma)).val :=
  tr.compileProof_isProof d

end LeanProofs.BoundedPAConsistency.TypedTemplateProofCompilerAudit
