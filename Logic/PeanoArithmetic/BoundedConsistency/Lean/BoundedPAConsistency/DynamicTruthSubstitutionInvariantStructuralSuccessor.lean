import BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Typed structural successor for dynamic substitution invariance

Simultaneous-substitution invariance at a positive dynamic-truth level is a
universal assertion about a model-coded formula code.  At a nonstandard orbit
index that code cannot be decoded into ordinary Lean syntax.  Consequently,
the structural argument must construct a represented PA proof of the complete
universal closure.

This module names that exact next-orbit predicate, proves the coded closedness
required by represented PA induction, and supplies the final splice from a
represented structural proof into `PAInductionKernel`.  Constructing the
strong structural proof itself remains a separate obligation.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Exact next-orbit target -/

/-- The unary predicate whose universal closure is the simultaneous-
substitution field constructed at recurrence index `n`.

The additions are left explicit because they match the fixed source
parameters and avoid normalization noise in proof-producing call sites. -/
noncomputable def nextSubstitutionInvariantPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  substitutionInvariantPredicateFormula (truthFormula n)
    (n + 1) (n + 1 + 1)

/-- Closing the named predicate is definitionally the next positive orbit
field. -/
@[simp] theorem all_nextSubstitutionInvariantPredicate_eq_orbit (n : V) :
    (∀⁰ nextSubstitutionInvariantPredicate n) =
      orbitSuccessorSubstitutionInvariantFormula n := by
  rfl

/-! ## Closedness required by represented PA induction -/

/-- The named predicate has no external free variables.  This is proved by
translating its fixed source predicate, so the proof applies uniformly to
possibly nonstandard values of `n`. -/
@[simp] theorem nextSubstitutionInvariantPredicate_shift (n : V) :
    (nextSubstitutionInvariantPredicate n).shift =
      nextSubstitutionInvariantPredicate n := by
  unfold nextSubstitutionInvariantPredicate
  rw [← translate_sourceSubstitutionInvariantPredicate
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

/-- Raw-code form of the closedness theorem, matching the input expected by
`PAInductionKernel.ofUniversalProof`. -/
@[simp] theorem nextSubstitutionInvariantPredicate_shift_val (n : V) :
    shift ℒₒᵣ (nextSubstitutionInvariantPredicate n).val =
      (nextSubstitutionInvariantPredicate n).val := by
  exact congrArg Bootstrapping.Semiformula.val
    (nextSubstitutionInvariantPredicate_shift n)

/-! ## Final production splice -/

/-- Install a represented structural proof of the complete next substitution
field as an induction kernel under an arbitrary staged context.  The supplied
universal proof contains the mathematical induction; the kernel fields merely
adapt it to the common certificate interface. -/
noncomputable def kernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextSubstitutionInvariantPredicate n)) :
    PAInductionKernel context :=
  PAInductionKernel.ofUniversalProof
    (nextSubstitutionInvariantPredicate n)
    (nextSubstitutionInvariantPredicate_shift_val n)
    proof

/-- Compiling the installed kernel returns the literal next orbit field. -/
noncomputable def compileKernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextSubstitutionInvariantPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
  Peano.internalize V ⊢!
      orbitSuccessorSubstitutionInvariantFormula n := by
  simpa only [kernelOfStructuralUniversalProof,
    PAInductionKernel.ofUniversalProof,
    all_nextSubstitutionInvariantPredicate_eq_orbit] using
    (kernelOfStructuralUniversalProof context n proof).compile hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthSubstitutionInvariantStructuralSuccessor
