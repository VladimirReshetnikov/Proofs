import BoundedPAConsistency.ModelCodedStrongInduction

/-!
# Audit: strong induction for model-coded predicates

This module keeps the source proof objects, the represented PA compiler, and
the final proof-code acceptance theorem visible to Lean's axiom auditor.  The
endpoint is stated for arbitrary model elements and therefore does not assume
that either the context or the unary predicate is the quotation of standard
Lean syntax.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedStrongInductionAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedStrongInduction

#check sourcePrefixZeroProof
#check sourcePrefixSuccessorProof
#check sourcePrefixExtractionProof
#check predicateCongruenceProof
#check prefixInductionKernel
#check strongStepToInductionContextProof
#check compiledPrefixExtractionProof
#check strongInductionImplicationProof
#check strongInductionProof
#check strongInductionProof_isPAProof

#print axioms sourcePrefixZeroProof
#print axioms sourcePrefixSuccessorProof
#print axioms sourcePrefixExtractionProof
#print axioms predicateCongruenceProof
#print axioms prefixInductionKernel
#print axioms strongStepToInductionContextProof
#print axioms compiledPrefixExtractionProof
#print axioms strongInductionImplicationProof
#print axioms strongInductionProof
#print axioms strongInductionProof_isPAProof

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The public compiler accepts any closed represented context and unary
represented predicate that are stable under the otherwise-vacuous shift. -/
noncomputable example
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate)
    (hstep : Peano.internalize V ⊢!
      strongStepFormula context predicate) :
    Peano.internalize V ⊢! context 🡒 ∀⁰ predicate :=
  strongInductionProof context predicate hcontext hpredicate hstep

/-- The proof term returned above is itself recognized by PA's represented
proof predicate, which is the interface required by the staged compilers. -/
noncomputable example
    (context : Bootstrapping.Formula V ℒₒᵣ)
    (predicate : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (hcontext : context.shift = context)
    (hpredicate : predicate.shift = predicate)
    (hstep : Peano.internalize V ⊢!
      strongStepFormula context predicate) :
    Proof Peano
      (strongInductionProof context predicate hcontext hpredicate hstep).val
      (context 🡒 ∀⁰ predicate).val :=
  strongInductionProof_isPAProof
    context predicate hcontext hpredicate hstep

end LeanProofs.BoundedPAConsistency.ModelCodedStrongInductionAudit
