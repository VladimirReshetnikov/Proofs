import BoundedPAConsistency.DynamicTruthQuantifierFreeAnchor
import BoundedPAConsistency.TruthCertificateContextProjection

/-!
# Typed structural successor for dynamic cross-level truth

The two-predicate source successor from
`DynamicTruthCrossLevelSourceSuccessor` is intentionally too general: its
second predicate is an arbitrary relation in an expansion of a PA model, so
lifted arithmetic PA has no induction axiom for formulas containing that
relation.  The production successor instead keeps the current predicate as
the *model-coded arithmetic formula* `truthFormula (n + 1)`.  This file fixes
the exact typed target and the final induction-kernel interface before the
arithmetized structural-induction proof is assembled.

No standardness assumption on `n` occurs below.  In particular, all formula
and proof codes remain elements of the ambient, possibly nonstandard, model.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStructuralSuccessor

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.TruthCertificateContextProjection

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-! ## Exact orbit target -/

/-- The unary predicate whose universal closure is the next positive
cross-level field.  Naming it avoids repeatedly normalizing the three
successor additions in the proof-producing layer. -/
noncomputable def nextCrossLevelPredicate (n : V) :
    Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  crossLevelPredicateFormula (truthFormula (n + 1))
    (n + 1 + 1) (n + 1 + 1 + 1)

/-- The structural successor theorem has exactly the current cross-level
field as antecedent and the universal closure of the next field as
consequent. -/
noncomputable def successorUniversalFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  Arrow.arrow (orbitSuccessorCrossLevelFormula n)
    (∀⁰ nextCrossLevelPredicate n)

/-- Closing the named predicate is definitionally the next orbit field. -/
@[simp] theorem all_nextCrossLevelPredicate_eq_orbit (n : V) :
    (∀⁰ nextCrossLevelPredicate n) =
      orbitSuccessorCrossLevelFormula (n + 1) := by
  rfl

/-- The complete target can therefore also be read as a direct implication
between adjacent represented orbit fields. -/
@[simp] theorem successorUniversalFormula_eq_orbit (n : V) :
    successorUniversalFormula n =
      Arrow.arrow (orbitSuccessorCrossLevelFormula n)
        (orbitSuccessorCrossLevelFormula (n + 1)) := by
  rfl

/-! ## Closedness needed by represented PA induction -/

/-- The next cross-level predicate has no free variables.  Its hierarchy
levels are typed numerals and its lower truth predicate is shift-fixed, so
internal `shift` leaves the complete model-coded formula unchanged. -/
@[simp] theorem nextCrossLevelPredicate_shift (n : V) :
    (nextCrossLevelPredicate n).shift = nextCrossLevelPredicate n := by
  unfold nextCrossLevelPredicate
  rw [← translate_sourceNextCrossLevelInvariant_orbit n]
  rw [← translateFormula_shift
    (truthFormula n) (truthFormula (n + 1))
    ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
    (truthFormula_shift n)
    (truthFormula_shift (n + 1))]
  congr 1
  unfold Rewriting.shift Rewriting.emb
  rw [← TransitiveRewriting.comp_app]
  congr 2
  ext x <;> simp

/-- Raw-code form of `nextCrossLevelPredicate_shift`, as expected by
`PAInductionKernel.ofUniversalProof`. -/
@[simp] theorem nextCrossLevelPredicate_shift_val (n : V) :
    shift ℒₒᵣ (nextCrossLevelPredicate n).val =
      (nextCrossLevelPredicate n).val := by
  exact congrArg Bootstrapping.Semiformula.val
    (nextCrossLevelPredicate_shift n)

/-! ## Final production splice -/

/-- Once arithmetized structural induction supplies the displayed universal
PA proof, this constructor installs it directly as the cross-level induction
kernel.  There is no second semantic argument and no decoding of `n` or of
`truthFormula n`. -/
noncomputable def kernelOfStructuralUniversalProof
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow (orbitSuccessorCrossLevelFormula n)
        (∀⁰ nextCrossLevelPredicate n)) :
    PAInductionKernel (orbitSuccessorCrossLevelFormula n) :=
  PAInductionKernel.ofUniversalProof
    (nextCrossLevelPredicate n)
    (nextCrossLevelPredicate_shift_val n)
    proof

/-- Compiling the installed kernel returns the exact next orbit field. -/
noncomputable def compileKernelOfStructuralUniversalProof
    (n : V)
    (proof : Peano.internalize V ⊢!
      Arrow.arrow (orbitSuccessorCrossLevelFormula n)
        (∀⁰ nextCrossLevelPredicate n))
    (hcontext : Peano.internalize V ⊢!
      orbitSuccessorCrossLevelFormula n) :
    Peano.internalize V ⊢!
      orbitSuccessorCrossLevelFormula (n + 1) := by
  simpa only [kernelOfStructuralUniversalProof,
    PAInductionKernel.ofUniversalProof,
    all_nextCrossLevelPredicate_eq_orbit] using
    (kernelOfStructuralUniversalProof n proof).compile hcontext

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelStructuralSuccessor
