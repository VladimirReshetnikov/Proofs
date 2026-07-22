import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
import BoundedPAConsistency.FixedLevelPAAxioms

/-!
# A genuine PA proof of base dynamic axiom soundness

The model-coded axiom-soundness field becomes ordinary arithmetic syntax at
the base of the dynamic truth orbit.  This module writes down that standard
sentence, proves that its typed quotation is literally the advertised base
field, proves the sentence in outer PA from fixed-level axiom soundness at
external level zero, and finally applies derivability condition D1 to obtain
the required proof object in an arbitrary ambient model of PA.

Keeping the quotation equality separate is important: the final transport
does not appeal to semantic extensionality of model-coded formulas.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundness

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms
open LeanProofs.BoundedPAConsistency.FixedLevelTruth

/-! ## Ordinary syntax for the base field -/

/-- Apply an ordinary closed unary formula to one ordinary closed term. -/
noncomputable def standardApply₁ {n : ℕ}
    (S : ArithmeticSemisentence 1)
    (t : ClosedSemiterm ℒₒᵣ n) : ArithmeticSemisentence n :=
  S ⇜ ![t]

/-- Quotation commutes with the unary application used below. -/
@[simp] theorem typedQuote_standardApply₁
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
    {n : ℕ} (S : ArithmeticSemisentence 1)
    (t : ClosedSemiterm ℒₒᵣ n) :
    (⌜standardApply₁ S t⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) =
      (⌜S⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst
        ![(⌜t⌝ : Bootstrapping.Semiterm V ℒₒᵣ n)] := by
  rw [standardApply₁, typedQuote_closedSubst]
  congr
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Ordinary syntax saying that the formula-code variable is recognized as
a PA axiom.  Within the two-variable body, `#1` is the formula code. -/
noncomputable def standardRecognizedPAAxiomFormula :
    ArithmeticSemisentence 2 :=
  standardApply₁ (Peano : Theory ℒₒᵣ).Δ₁ch.val (#1)

/-- Ordinary syntax saying that the formula code has quantifier-group bound
zero. -/
noncomputable def standardZeroAxiomBoundedDomainFormula :
    ArithmeticSemisentence 2 :=
  standardApply₂ (quantifierBoundedCodeDef ℒₒᵣ).val
    (‘0’ : ArithmeticSemiterm Empty 2) (#1)

/-- Ordinary syntax saying that `#0` is a coded free-variable sequence. -/
noncomputable def standardAxiomFreeSequenceFormula :
    ArithmeticSemisentence 2 :=
  standardApply₁ seqDef.val (#0)

/-- The ordinary level-zero axiom-soundness implication. -/
noncomputable def standardBaseAxiomSoundnessBody :
    ArithmeticSemisentence 2 :=
  Arrow.arrow
    (standardRecognizedPAAxiomFormula ⋏
      (standardZeroAxiomBoundedDomainFormula ⋏
        standardAxiomFreeSequenceFormula))
    (standardApply₃ levelZeroTruthSyntax
      (‘0’ : ArithmeticSemiterm Empty 2) (#0) (#1))

/-- The ordinary arithmetic sentence underlying the base model-coded field. -/
noncomputable def standardBaseAxiomSoundnessSentence : ArithmeticSentence :=
  ∀⁰ ∀⁰ standardBaseAxiomSoundnessBody

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- Typed quotation of the standard sentence is exactly the base field.
Every component is constructor-level syntax; in particular the consequent
uses the previously proved quotation identity for `levelZeroTruthSyntax`. -/
@[simp] theorem typedQuote_standardBaseAxiomSoundnessSentence :
    (⌜standardBaseAxiomSoundnessSentence⌝ :
        Bootstrapping.Formula V ℒₒᵣ) =
      baseAxiomSoundnessFormula := by
  simp [standardBaseAxiomSoundnessSentence,
    standardBaseAxiomSoundnessBody,
    standardRecognizedPAAxiomFormula,
    standardZeroAxiomBoundedDomainFormula,
    standardAxiomFreeSequenceFormula,
    baseAxiomSoundnessFormula_eq_upper,
    upperAxiomSoundnessFormula, axiomSoundnessPredicateFormula,
    axiomSoundnessBodyFormula, recognizedPAAxiomFormula,
    axiomBoundedDomainFormula, freeSequenceFormula,
    DynamicTruthFormula.apply₃,
    DynamicTruthFormula.levelZeroTruthFormula_eq_typedQuote,
    DynamicTruthAxiomSoundnessFormula.typedSourceZeroTerm]

/-! ## Outer and internal PA derivations -/

/-- Outer PA proves the ordinary base field.  Completeness reduces the claim
to an arbitrary PA model, where the three represented hypotheses are exactly
membership in PA's Delta-one axiom class, quantifier-group boundedness at
level zero, and sequencehood.  The fixed-level theorem supplies the desired
`SigmaTrue 1` conclusion. -/
noncomputable def standardBaseAxiomSoundnessProof :
    Peano ⊢! standardBaseAxiomSoundnessSentence :=
  (LO.FirstOrder.Arithmetic.complete.{0} Peano _ <| by
    intro M _ hM
    letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hM
    simp [models_iff, standardBaseAxiomSoundnessSentence,
      standardBaseAxiomSoundnessBody,
      standardRecognizedPAAxiomFormula,
      standardZeroAxiomBoundedDomainFormula,
      standardAxiomFreeSequenceFormula,
      standardApply₁, standardApply₂, standardApply₃]
    intro p free hp hbounded hfree
    have hbounded' : QuantifierBoundedCode ℒₒᵣ
        (levelCode (V := M) 0) p := by
      apply OrientedHierarchy.quantifierBoundedCode_iff_sigma_or_pi.mpr
      simpa [levelCode] using hbounded
    simpa [eval_levelZeroTruthSyntax_iff, levelCode] using
      (sigmaTrue_succ_of_mem_pa_delta1Class (V := M) 0
        hp hbounded' hfree)).get

/-- A genuine internal PA derivation of the exact model-coded base field. -/
noncomputable def baseAxiomSoundnessProof :
    Peano.internalize V ⊢! baseAxiomSoundnessFormula := by
  rw [← typedQuote_standardBaseAxiomSoundnessSentence (V := V)]
  exact (internal_provable_of_outer_provable (V := V)
    (show Peano ⊢ standardBaseAxiomSoundnessSentence from
      ⟨standardBaseAxiomSoundnessProof⟩)).get

end LeanProofs.BoundedPAConsistency.DynamicTruthBaseAxiomSoundness
