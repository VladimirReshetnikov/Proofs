import BoundedPAConsistency.DynamicTruthOrbit
import BoundedPAConsistency.DynamicTruthTemplateFormula
import Foundation.FirstOrder.Completeness

/-!
# A compiled local projection law for dynamic truth

The first component of a successor truth certificate is the local fact that
every accepted state has an HFS certificate witnessing its root state.  This
module proves that component once in the fixed source language used by
`DynamicTruthTemplateFormula`, and then specializes the proof at an arbitrary
model-coded lower truth predicate and arbitrary model levels.

The result is deliberately stronger than a semantic observation: the public
endpoint is a typed internal PA proof, and its `.val` is accepted by the
represented PA proof predicate.  The final theorem instantiates it at the
nonstandard orbit, where the antecedent is syntactically the next truth
formula `truthFormula (n + 1)`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

/-! ## The fixed source theorem -/

/-- Forget the local-validity half of a successor certificate while retaining
the HFS witness for the advertised root state. -/
noncomputable def hasStateProjection :
    Semisentence SourceLanguage 3 :=
  ∃⁰ liftArithmeticFormula hasTruthStateDef.val

/-- The universally closed local projection law.

Its three quantified variables are the environment bound, free-variable
assignment, and formula code used by the ternary truth predicate. -/
noncomputable def localProjectionSentence : Sentence SourceLanguage :=
  ∀⁰ ∀⁰ ∀⁰ (successorTruthFormula 🡒 hasStateProjection)

/-- A single, fixed PA proof of the local projection law.

Only first-order logic is used: a witness for
`exists C, HasState C ... and Valid C` is also a witness for
`exists C, HasState C ...`.  Completeness is used here solely to construct
that standard source derivation; the later specialization compiler traverses
the resulting finite proof tree and emits a represented proof code. -/
noncomputable def sourceProof :
    parameterTemplatePeano 3 2 ⊢! localProjectionSentence :=
  (Theory.Proof.small_complete <| consequence_iff.mpr fun _ ↦ by
    simp [models_iff, localProjectionSentence, hasStateProjection,
      DynamicTruthTemplateFormula.successorTruthFormula]
    intro _ _ _ _ _ _ _ hstate _
    exact ⟨_, hstate⟩).get

/-! ## Exact model-coded specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The concrete typed formula obtained after inserting a model-coded lower
truth predicate and the two possibly nonstandard hierarchy levels. -/
noncomputable def localProjectionFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰
    (DynamicTruthFormula.successorTruthFormula
        lower lowerLevel upperLevel 🡒
      ∃⁰ (⌜hasTruthStateDef.val⌝ :
        Bootstrapping.Semiformula V ℒₒᵣ 4))

/-- Translation of the fixed source theorem is syntactically the advertised
model-coded local law. -/
@[simp] theorem translate_localProjectionSentence
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) :
    translateFormula lower ![lowerLevel, upperLevel]
        (Rewriting.emb localProjectionSentence) =
      localProjectionFormula lower lowerLevel upperLevel := by
  simp only [localProjectionSentence, Rewriting.app_all,
    Rew.q_emb, ModelCodedPredicateParameters.translateFormula]
  have himp :
      (Rewriting.emb (successorTruthFormula 🡒 hasStateProjection) :
          Semiproposition SourceLanguage 3) =
        (∼(Rewriting.emb successorTruthFormula) ⋎
          Rewriting.emb hasStateProjection) := by
    simp [FirstOrder.Semiformula.imp_eq]
  rw [himp]
  simp only [ModelCodedPredicateParameters.translateFormula]
  rw [ModelCodedPredicateParameters.translateFormula_neg,
    translate_successorTruthFormula]
  simp [hasStateProjection, localProjectionFormula,
    ModelCodedPredicateParameters.translateFormula,
    Bootstrapping.Semiformula.imp_def]

/-- Compile the fixed source proof at arbitrary model-coded syntax and
arbitrary model levels. -/
noncomputable def compiledLocalProjectionProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Peano.internalize V ⊢!
      localProjectionFormula lower lowerLevel upperLevel := by
  simpa only [translate_localProjectionSentence] using
    (compilePeanoTemplate lower ![lowerLevel, upperLevel] hlower sourceProof)

set_option backward.isDefEq.respectTransparency false in
/-- The compiled derivation has an actual PA proof code. -/
theorem compiledLocalProjectionProof_isPAProof
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (lowerLevel upperLevel : V) (hlower : lower.shift = lower) :
    Proof Peano
      (compiledLocalProjectionProof lower lowerLevel upperLevel hlower).val
      (localProjectionFormula lower lowerLevel upperLevel).val := by
  simpa [Proof] using
    (compiledLocalProjectionProof lower lowerLevel upperLevel
      hlower).derivationOf

/-! ## The exact nonstandard-orbit instance -/

/-- The local projection field written with the actual next member of the
dynamic truth orbit in its antecedent. -/
noncomputable def orbitLocalProjectionFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  ∀⁰ ∀⁰ ∀⁰
    (truthFormula (n + 1) 🡒
      ∃⁰ (⌜hasTruthStateDef.val⌝ :
        Bootstrapping.Semiformula V ℒₒᵣ 4))

/-- An exact typed PA proof of the first local successor-law component at
every, including nonstandard, model level. -/
noncomputable def orbitLocalProjectionProof (n : V) :
    Peano.internalize V ⊢! orbitLocalProjectionFormula n := by
  simpa only [orbitLocalProjectionFormula, localProjectionFormula,
    truthFormula_succ] using
    (compiledLocalProjectionProof (truthFormula n) (n + 1) (n + 1 + 1)
      (truthFormula_shift n))

set_option backward.isDefEq.respectTransparency false in
/-- Represented-proof form of `orbitLocalProjectionProof`. -/
theorem orbitLocalProjectionProof_isPAProof (n : V) :
    Proof Peano (orbitLocalProjectionProof n).val
      (orbitLocalProjectionFormula n).val := by
  simpa [Proof] using (orbitLocalProjectionProof n).derivationOf

end LeanProofs.BoundedPAConsistency.DynamicTruthLocalProjectionTemplate
