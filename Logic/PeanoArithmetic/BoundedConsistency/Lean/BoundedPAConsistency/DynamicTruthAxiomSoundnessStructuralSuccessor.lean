import BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Typed structural successor for dynamic PA-axiom soundness

The positive PA-axiom-soundness field quantifies over a model-coded formula
code.  At nonstandard orbit indices there is no external syntax tree on which
Lean can recurse.  Its successor proof must instead be a represented PA proof
of the complete universal closure.

This module records that exact unary target, proves its coded closedness via
the fixed source translation, and connects any represented structural proof
to the staged `PAInductionKernel` interface.  It does not assume that the
model-coded formula can be decoded.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Exact next-orbit target -/

/-- The unary predicate whose universal closure is the PA-axiom-soundness
field constructed at recurrence index `n`.

The upper truth predicate is displayed as the corresponding successor
constructor.  This makes both its source specialization and its equality
with the next orbit field definitionally transparent. -/
noncomputable def nextAxiomSoundnessPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  axiomSoundnessPredicateFormula
    (DynamicTruthFormula.successorTruthFormula
      (truthFormula n) (n + 1) (n + 1 + 1))
    (n + 1)

/-- Closing the named predicate is definitionally the next positive orbit
field. -/
@[simp] theorem all_nextAxiomSoundnessPredicate_eq_orbit (n : V) :
    (∀⁰ nextAxiomSoundnessPredicate n) =
      orbitSuccessorAxiomSoundnessFormula n := by
  rfl

/-! ## Closedness required by represented PA induction -/

/-- The next axiom-soundness predicate is closed.  Deriving this from the
fixed source predicate keeps the argument entirely at the level of represented
syntax and hence valid for nonstandard model indices. -/
@[simp] theorem nextAxiomSoundnessPredicate_shift (n : V) :
    (nextAxiomSoundnessPredicate n).shift =
      nextAxiomSoundnessPredicate n := by
  unfold nextAxiomSoundnessPredicate
  rw [← translate_sourceAxiomSoundnessPredicate
    (truthFormula n) (n + 1) (n + 1 + 1)]
  rw [← translateFormula_shift
    (truthFormula n)
    ![n + 1, n + 1 + 1]
    (truthFormula_shift n)]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Raw-code form of the closedness theorem, as consumed by
`PAInductionKernel.ofUniversalProof`. -/
@[simp] theorem nextAxiomSoundnessPredicate_shift_val (n : V) :
    shift ℒₒᵣ (nextAxiomSoundnessPredicate n).val =
      (nextAxiomSoundnessPredicate n).val := by
  exact congrArg Bootstrapping.Semiformula.val
    (nextAxiomSoundnessPredicate_shift n)

/-! ## Final production splice -/

/-- Install a represented structural proof of the complete next axiom-
soundness field as an induction kernel under an arbitrary staged context. -/
noncomputable def kernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextAxiomSoundnessPredicate n)) :
    PAInductionKernel context :=
  PAInductionKernel.ofUniversalProof
    (nextAxiomSoundnessPredicate n)
    (nextAxiomSoundnessPredicate_shift_val n)
    proof

/-- Compiling the installed kernel returns the literal next orbit field. -/
noncomputable def compileKernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextAxiomSoundnessPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
  Peano.internalize V ⊢!
      orbitSuccessorAxiomSoundnessFormula n := by
  simpa only [kernelOfStructuralUniversalProof,
    PAInductionKernel.ofUniversalProof,
    all_nextAxiomSoundnessPredicate_eq_orbit] using
    (kernelOfStructuralUniversalProof context n proof).compile hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthAxiomSoundnessStructuralSuccessor
