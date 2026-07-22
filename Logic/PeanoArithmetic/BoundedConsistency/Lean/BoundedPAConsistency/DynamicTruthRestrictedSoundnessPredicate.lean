import BoundedPAConsistency.AbstractSoundness
import BoundedPAConsistency.DynamicTruthCertificateSemantics
import BoundedPAConsistency.ModelCodedStrongInduction

/-!
# A fixed source predicate for restricted-derivation soundness

The last field of a dynamic truth certificate says that a restricted PA
derivation cannot end in falsity.  Its proof first establishes the stronger
statement that every restricted derivation has a true conclusion sequent.

This module writes that invariant as one unary formula in the common source
language.  All proof-code operations remain ordinary represented arithmetic
graphs; the only opaque atom is the model-coded truth relation itself.  This
is the shape required by `ModelCodedStrongInduction`.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency
open LeanProofs.BoundedPAConsistency.AbstractSoundness
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCertificateSemantics
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStrongStepSource
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthTemplateSemantics
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters

private abbrev L := DynamicTruthTemplateFormula.SourceLanguage

/-! ## Fixed source syntax -/

/-- The arithmetic statement that the input is a restricted PA derivation at
the first named hierarchy level. -/
noncomputable def sourceRestrictedDerivation : Semisentence L 1 :=
  DynamicTruthTemplateFormula.apply₂
    (liftArithmeticFormula
      (restrictedDerivationDef (L := ℒₒᵣ) Peano).sigma.val)
    (parameterTerm 0) (#0)

/-- The conclusion sequent of the input derivation is true for every coded
free-variable environment.

After the three binders for `free`, `sequent`, and `formula`, their values are
respectively `#2`, `#1`, and `#0`.  The original derivation has shifted to
`#3`. -/
noncomputable def sourceSequentTrue : Semisentence L 1 :=
  ∀⁰
    (apply₁ (liftArithmeticFormula seqDef.val) (#0) 🡒
      ∃⁰
        (DynamicTruthTemplateFormula.apply₂
            (liftArithmeticFormula fstIdxDef.val) (#0) (#2) ⋏
          (∃⁰
            (DynamicTruthTemplateFormula.apply₂
                (liftArithmeticFormula hfsMemDef.val) (#0) (#1) ⋏
              DynamicTruthTemplateFormula.apply₃
                DynamicTruthTemplateFormula.successorTruthFormula
                sourceZeroTerm (#2) (#0)))))

/-- Unary invariant used for represented strong induction on derivation
codes. -/
noncomputable def sourceDerivationSoundnessPredicate : Semisentence L 1 :=
  sourceRestrictedDerivation 🡒 sourceSequentTrue

/-- The arithmetic guard `e < d`, with `e = #0` and `d = #1`. -/
noncomputable def sourceDerivationPrefixGuard : Semisentence L 2 :=
  liftArithmeticFormula
    (.rel Language.LT.lt
      ![(#0 : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2)])

/-- Every smaller derivation code satisfies the soundness invariant. -/
noncomputable def sourceDerivationSoundnessPrefix : Semisentence L 1 :=
  ∀⁰
    (sourceDerivationPrefixGuard 🡒
      apply₁ sourceDerivationSoundnessPredicate (#0))

/-- Strong-step premise for soundness of all restricted derivation codes. -/
noncomputable def sourceDerivationSoundnessStrongStep : Sentence L :=
  ∀⁰
    (sourceDerivationSoundnessPrefix 🡒
      sourceDerivationSoundnessPredicate)

/-! ## Typed specialization -/

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- Specialize the invariant to the represented successor of an arbitrary
model-coded lower predicate and an arbitrary (possibly nonstandard)
restricted-derivation bound. -/
noncomputable def derivationSoundnessPredicateFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (level nextLevel : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  translateFormula lower ![level, nextLevel]
    (Rewriting.emb sourceDerivationSoundnessPredicate)

@[simp] theorem translate_sourceDerivationSoundnessPredicate
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (level nextLevel : V) :
    translateFormula lower ![level, nextLevel]
        (Rewriting.emb sourceDerivationSoundnessPredicate) =
      derivationSoundnessPredicateFormula lower level nextLevel := rfl

/-- The translated fixed-source strong step, before it is embedded under the
staged certificate context. -/
noncomputable def derivationSoundnessStrongStepFormula
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (level nextLevel : V) : Bootstrapping.Formula V ℒₒᵣ :=
  translateFormula lower ![level, nextLevel]
    (Rewriting.emb sourceDerivationSoundnessStrongStep)

/-- The specialized invariant is closed under coded free-variable shift, as
required by represented strong induction. -/
@[simp] theorem derivationSoundnessPredicateFormula_shift
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (level nextLevel : V) (hlower : lower.shift = lower) :
    (derivationSoundnessPredicateFormula lower level nextLevel).shift =
      derivationSoundnessPredicateFormula lower level nextLevel := by
  unfold derivationSoundnessPredicateFormula
  rw [← ModelCodedPredicateParameters.translateFormula_shift
    lower ![level, nextLevel] hlower]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-! ## Source semantics -/

variable {M : Type*}
variable [sourceStructure : Structure L M]
variable [Nonempty M] [ORingStructure M]
variable [hPA : M↓[ℒₒᵣ] ⊧* Peano]

local instance : M↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

variable (hArithmeticReduct :
  sourceStructure.lMap (arithmeticHom 3 2) =
    LO.FirstOrder.Arithmetic.standardModel M)

include hArithmeticReduct in
@[simp] theorem eval_sourceRestrictedDerivation (d : M) :
    sourceRestrictedDerivation.Evalb (M := M) ![d] ↔
      RestrictedDerivation Peano (level 0) d := by
  simp [sourceRestrictedDerivation,
    DynamicTruthTemplateSemantics.eval_apply₂,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateFormula.parameterTerm, level]

include hArithmeticReduct in
@[simp] theorem eval_sourceSequentTrue (d : M) :
    sourceSequentTrue.Evalb (M := M) ![d] ↔
      SequentTrue
        (SuccessorTruth lowerRelation (level 0) (level 1))
        (fstIdx d) := by
  simp [sourceSequentTrue, SequentTrue,
    DynamicTruthCertificateSemantics.eval_apply₁,
    DynamicTruthTemplateSemantics.eval_apply₂,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct,
    DynamicTruthTemplateSemantics.eval_successorTruthFormula
      hArithmeticReduct,
    DynamicTruthCertificateSemantics.eval_sourceAxiomZeroTerm
      hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceDerivationSoundnessPredicate (d : M) :
    sourceDerivationSoundnessPredicate.Evalb (M := M) ![d] ↔
      (RestrictedDerivation Peano (level 0) d →
        SequentTrue
          (SuccessorTruth lowerRelation (level 0) (level 1))
          (fstIdx d)) := by
  simp [sourceDerivationSoundnessPredicate,
    eval_sourceRestrictedDerivation hArithmeticReduct,
    eval_sourceSequentTrue hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceDerivationPrefixGuard (v : Fin 2 → M) :
    sourceDerivationPrefixGuard.Evalb (M := M) v ↔ v 0 < v 1 := by
  simp [sourceDerivationPrefixGuard,
    DynamicTruthTemplateSemantics.eval_liftArithmeticFormula
      hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceDerivationSoundnessPrefix (d : M) :
    sourceDerivationSoundnessPrefix.Evalb (M := M) ![d] ↔
      ∀ e < d,
        RestrictedDerivation Peano (level 0) e →
          SequentTrue
            (SuccessorTruth lowerRelation (level 0) (level 1))
            (fstIdx e) := by
  simp [sourceDerivationSoundnessPrefix,
    DynamicTruthCertificateSemantics.eval_apply₁,
    eval_sourceDerivationPrefixGuard hArithmeticReduct,
    eval_sourceDerivationSoundnessPredicate hArithmeticReduct]

include hArithmeticReduct in
@[simp] theorem eval_sourceDerivationSoundnessStrongStep :
    sourceDerivationSoundnessStrongStep.Evalb (M := M) ![] ↔
      ∀ d : M,
        (∀ e < d,
          RestrictedDerivation Peano (level 0) e →
            SequentTrue
              (SuccessorTruth lowerRelation (level 0) (level 1))
              (fstIdx e)) →
        RestrictedDerivation Peano (level 0) d →
          SequentTrue
            (SuccessorTruth lowerRelation (level 0) (level 1))
            (fstIdx d) := by
  simp [sourceDerivationSoundnessStrongStep,
    eval_sourceDerivationSoundnessPrefix hArithmeticReduct,
    eval_sourceDerivationSoundnessPredicate hArithmeticReduct]

end LeanProofs.BoundedPAConsistency.DynamicTruthRestrictedSoundnessPredicate
