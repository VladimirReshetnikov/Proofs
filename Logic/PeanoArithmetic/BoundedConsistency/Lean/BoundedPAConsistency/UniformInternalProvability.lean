import BoundedPAConsistency.FixedLevelPAAxioms
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
import Foundation.FirstOrder.Bootstrapping.FixedPoint

/-!
# The literal uniform internal-provability sentence

The already established theorem
`FixedLevelPAAxioms.pa_proves_restrictedConsistency n` is indexed by a
*metatheoretic* natural number.  Consequently, putting a Lean `forall` in
front of that theorem still does not produce a single sentence of PA.

This file records the distinct sentence requested by the notation

`PA proves: for every n, PA proves Con_n(PA)`.

The inner occurrence of "proves" is Foundation's represented PA proof
predicate.  The graph `ssnum` computes the code obtained by substituting the
numeral for the (possibly nonstandard) model element `n` into the fixed unary
formula defining bounded consistency.  Thus the outer quantifier really
ranges over every element of an arbitrary PA model; it is not an abbreviation
for the previously proved numeralwise scheme.
-/

namespace LeanProofs.BoundedPAConsistency.UniformInternalProvability

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.FixedLevelPAAxioms

/-- The fixed unary formula whose numeral instances are `Con_n(PA)`. -/
noncomputable abbrev paRestrictedConsistencyTemplate :
    ArithmeticSemisentence 1 :=
  (restrictedConsistentDef Peano).val

/-- The literal object-language reading of
`PA proves: forall n, PA proves Con_n(PA)`.

The existentially quantified `p` is the code of the numeral instance of the
fixed consistency template.  Functionality of `ssnum` makes this equivalent
to applying the represented provability predicate directly to
`substNumeral quote(template) n`. -/
noncomputable def paUniformRestrictedConsistencyProvabilitySentence :
    ArithmeticSentence :=
  “∀ n, ∃ p,
      !ssnum p !!(⌜paRestrictedConsistencyTemplate⌝) n ∧
      !(provable Peano) p”

variable {V : Type*} [ORingStructure V]
variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Semantic specification of the literal uniform sentence.  Notice that
`n` has type `V`, so this includes nonstandard levels in nonstandard models. -/
@[simp] theorem eval_paUniformRestrictedConsistencyProvabilitySentence_iff :
    paUniformRestrictedConsistencyProvabilitySentence.Evalb
        (M := V) ![] ↔
      ∀ n : V,
        Provable Peano
          (substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n) := by
  simp [paUniformRestrictedConsistencyProvabilitySentence]

/-- Substitution of a standard numeral into a quoted unary formula computes
the quotation of its syntactic numeral instance.

Using `substNumerals_app_quote` here avoids normalizing the concrete (and
large) bounded-consistency formula merely to compare two quotation paths. -/
private theorem substNumeral_quote_numeral
    (sigma : ArithmeticSemisentence 1) (n : ℕ) :
    substNumeral (⌜sigma⌝ : V) (ORingStructure.numeral n : V) =
      (⌜(sigma/[n] : ArithmeticSentence)⌝ : V) := by
  simpa [substNumeral, substNumerals, numeral_eq_natCast,
    Matrix.vecHead, Matrix.vecTail, Matrix.constant_eq_singleton] using
    (substNumerals_app_quote (V := V) sigma (fun _ : Fin 1 ↦ n))

/-- The canonical syntactic instance computed by `ssnum` has exactly the
intended bounded-consistency semantics at every standard numeral. -/
@[simp] theorem eval_paRestrictedConsistencyTemplate_instance_iff (n : ℕ) :
    ((paRestrictedConsistencyTemplate/[n] : ArithmeticSentence).Evalb
        (M := V) ![]) ↔
      RestrictedConsistent Peano (ORingStructure.numeral n : V) := by
  simpa [FirstOrder.Semiformula.eval_substs,
    paRestrictedConsistencyTemplate, numeral_eq_natCast,
    Matrix.constant_eq_singleton] using
    (RestrictedConsistent.defined (V := V) Peano).iff
      (v := ![(ORingStructure.numeral n : V)])

/-- PA proves the canonical syntactic instance computed by the uniform
substitution graph. This is the same fixed-level semantic argument as for
`paRestrictedConsistencySentence`, without an expensive normalization-based
comparison between the two host-language formula constructions. -/
theorem pa_proves_paRestrictedConsistencyTemplate_instance (n : ℕ) :
    Peano ⊢ (paRestrictedConsistencyTemplate/[n] : ArithmeticSentence) := by
  apply LO.FirstOrder.Arithmetic.complete.{0} Peano _
  intro M _ hPA
  letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
  simpa [models_iff] using
    (eval_paRestrictedConsistencyTemplate_instance_iff (V := M) n).mpr
      (restrictedConsistent_pa_fixedLevel (V := M) n)

/-- At a standard numeral, the code used by the uniform sentence is exactly
the quotation of the canonical syntactic instance of `Con_n(PA)`. -/
theorem substNumeral_paRestrictedConsistencyTemplate_eq_quote (n : ℕ) :
    substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V)
        (ORingStructure.numeral n : V) =
      (⌜(paRestrictedConsistencyTemplate/[n] : ArithmeticSentence)⌝ : V) :=
  substNumeral_quote_numeral paRestrictedConsistencyTemplate n

/-- Every standard point of the literal uniform predicate follows from the
fixed-level theorem by Hilbert--Bernays derivability condition D1.  This is
still a metatheoretic family: it deliberately does not quantify over `V`. -/
theorem provable_paRestrictedConsistency_standard_point (n : ℕ) :
    Provable Peano
      (substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V)
        (ORingStructure.numeral n : V)) := by
  rw [substNumeral_paRestrictedConsistencyTemplate_eq_quote]
  exact internalize_provability
    (V := V) (pa_proves_paRestrictedConsistencyTemplate_instance n)

/-! ## The exact missing uniform selector -/

/-- A model-internal proof selector for the bounded-consistency instances.

This name intentionally says `Selector`: unlike the preceding standard-point
theorem, it asks for a proof witness at *every* model element, including a
nonstandard `n`.  Establishing this property requires a represented recursive
constructor for the fixed-level PA proofs.  The model-theoretic completeness
argument used in `FixedLevelPAAxioms` does not provide such a constructor. -/
def PARestrictedConsistencyProofSelectorIn (V : Type*)
    [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1] : Prop :=
  ∀ n : V, ∃ d : V,
    Proof Peano d
      (substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n)

/-- The selector fact in every PA model.  The explicit `I Sigma 1` instance
is logically redundant (PA supplies it) but makes the model-internal proof
coding operations' required instance visible in the type. -/
def PARestrictedConsistencyProofSelectorInAllModels : Prop :=
  ∀ (V : Type) [ORingStructure V]
      [V↓[ℒₒᵣ] ⊧* Peano] [V↓[ℒₒᵣ] ⊧* ISigma 1],
    PARestrictedConsistencyProofSelectorIn V

/-- The object sentence says exactly that a model-internal selector exists.
This equivalence is only definitional packaging; it does not assume or prove
the missing selector. -/
theorem eval_paUniformRestrictedConsistencyProvabilitySentence_iff_selector :
    paUniformRestrictedConsistencyProvabilitySentence.Evalb
        (M := V) ![] ↔
      PARestrictedConsistencyProofSelectorIn V := by
  simpa [PARestrictedConsistencyProofSelectorIn, Provable] using
    (eval_paUniformRestrictedConsistencyProvabilitySentence_iff (V := V))

/-- Once the represented uniform proof selector has been constructed in every
PA model, first-order completeness yields the requested actual PA theorem. -/
theorem pa_proves_uniformRestrictedConsistencyProvability_of_selectorInAllModels
    (hselector : PARestrictedConsistencyProofSelectorInAllModels) :
    Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} Peano _
  intro M _ hPA
  letI : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA
  simpa [models_iff] using
    (eval_paUniformRestrictedConsistencyProvabilitySentence_iff_selector
      (V := M)).mpr (hselector M)

/-- Exact characterization of the remaining Lean obligation: the requested
PA derivation is equivalent (by soundness and completeness) to the selector
property in every PA model. -/
theorem pa_proves_uniformRestrictedConsistencyProvability_iff_selectorInAllModels :
    (Peano ⊢ paUniformRestrictedConsistencyProvabilitySentence) ↔
      PARestrictedConsistencyProofSelectorInAllModels := by
  constructor
  · intro hprov M _ hPA _
    apply
      (eval_paUniformRestrictedConsistencyProvabilitySentence_iff_selector
        (V := M)).mp
    simpa [models_iff] using
      (models_of_provable hPA hprov)
  · exact
      pa_proves_uniformRestrictedConsistencyProvability_of_selectorInAllModels

end LeanProofs.BoundedPAConsistency.UniformInternalProvability
