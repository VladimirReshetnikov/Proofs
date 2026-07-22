import BoundedPAConsistency.DynamicTruthShiftInvariantFormula
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Typed structural successor for dynamic shift invariance

Shift invariance at a positive dynamic-truth level is a universal statement
about a model-coded formula code.  At a nonstandard orbit index that code
cannot be decoded into ordinary Lean syntax, so the structural argument must
produce a represented PA proof of the complete universal closure.

This module fixes the exact target of that argument.  It also proves that the
unary target predicate is closed under the coded free-variable shift and
installs any represented structural proof directly behind the staged
`PAInductionKernel` interface.  The actual strong structural induction is
kept separate; no semantic standardness assumption is hidden here.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantFormula
open LeanProofs.BoundedPAConsistency.ModelCodedPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Exact next-orbit target -/

/-- The unary predicate whose closure is shift invariance for the dynamic
truth successor constructed at recurrence index `n`.

The deliberately explicit additions mirror the arguments of
`orbitSuccessorShiftInvariantFormula n`.  Keeping this predicate named
avoids asking elaboration to normalize those model additions at every
proof-producing call site. -/
noncomputable def nextShiftInvariantPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  shiftInvariantPredicateFormula (truthFormula n)
    (n + 1) (n + 1 + 1)

/-- The universal closure of the named predicate is definitionally the next
positive orbit field. -/
@[simp] theorem all_nextShiftInvariantPredicate_eq_orbit (n : V) :
    (∀⁰ nextShiftInvariantPredicate n) =
      orbitSuccessorShiftInvariantFormula n := by
  rfl

/-! ## Closedness required by represented PA induction -/

/-- The next shift-invariance predicate contains only bound variables,
typed numerals, fixed arithmetic syntax, and the closed dynamic truth
predicate.  We prove coded closedness by translating the corresponding fixed
source predicate; this works just as well when `n` is nonstandard. -/
@[simp] theorem nextShiftInvariantPredicate_shift (n : V) :
    (nextShiftInvariantPredicate n).shift =
      nextShiftInvariantPredicate n := by
  unfold nextShiftInvariantPredicate
  rw [← translate_sourceShiftInvariantPredicate
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

/-- Raw-code form of `nextShiftInvariantPredicate_shift`, matching the
closedness field of `PAInductionKernel.ofUniversalProof`. -/
@[simp] theorem nextShiftInvariantPredicate_shift_val (n : V) :
    shift ℒₒᵣ (nextShiftInvariantPredicate n).val =
      (nextShiftInvariantPredicate n).val := by
  exact congrArg Bootstrapping.Semiformula.val
    (nextShiftInvariantPredicate_shift n)

/-! ## Final production splice -/

/-- Install a represented structural proof of the complete next
shift-invariance field as an induction kernel under an arbitrary staged
context.  The kernel's derived zero and successor fields are only interface
plumbing; the supplied universal proof contains the mathematical induction. -/
noncomputable def kernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextShiftInvariantPredicate n)) :
    PAInductionKernel context :=
  PAInductionKernel.ofUniversalProof
    (nextShiftInvariantPredicate n)
    (nextShiftInvariantPredicate_shift_val n)
    proof

/-- Compiling the installed kernel returns the literal next orbit field. -/
noncomputable def compileKernelOfStructuralUniversalProof
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow context (∀⁰ nextShiftInvariantPredicate n))
    (hcontext : Peano.internalize V ⊢! context) :
  Peano.internalize V ⊢!
      orbitSuccessorShiftInvariantFormula n := by
  simpa only [kernelOfStructuralUniversalProof,
    PAInductionKernel.ofUniversalProof,
    all_nextShiftInvariantPredicate_eq_orbit] using
    (kernelOfStructuralUniversalProof context n proof).compile hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthShiftInvariantStructuralSuccessor
