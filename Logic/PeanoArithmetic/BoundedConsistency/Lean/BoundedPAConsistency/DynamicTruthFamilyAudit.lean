import BoundedPAConsistency.DynamicTruthFamily

/-!
# Kernel-facing audit for the standard dynamic truth hierarchy

This file intentionally audits only the ordinary `Nat`-indexed orbit.  In
particular, none of the checks below asserts that metatheoretic recursion has
already produced a family indexed by arbitrary elements of a model of PA.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthFamilyAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.FixedLevelTruth
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthFamily

#check standardDynamicTruthSyntax
#check standardDynamicTruthFormula
#check standardDynamicTruthFormula_eq_typedQuote
#check standardDynamicTruthFormula_val_eq_quote
#check standardDynamicTruthFormula_shift
#check eval_standardSuccessorTruthFormula_iff
#check eval_standardDynamicTruthSyntax_iff
#check standardBoundedTruthFormula
#check standardBoundedTruthFormula_zero
#check eval_standardBoundedTruthSyntax_iff

#print axioms standardDynamicTruthFormula_eq_typedQuote
#print axioms standardDynamicTruthFormula_shift
#print axioms eval_standardSuccessorTruthFormula_iff
#print axioms eval_standardDynamicTruthSyntax_iff
#print axioms eval_standardBoundedTruthSyntax_iff

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- A concrete sanity check for the indexing convention: bound zero uses
the first successor of quantifier-free truth and hence denotes
`SigmaTrue 1`. -/
example (v : Fin 3 → V) :
    (standardDynamicTruthSyntax 1).Evalb (M := V) v ↔
      SigmaTrue 1 (v 0) (v 1) (v 2) :=
  eval_standardDynamicTruthSyntax_iff 1 v

end LeanProofs.BoundedPAConsistency.DynamicTruthFamilyAudit
