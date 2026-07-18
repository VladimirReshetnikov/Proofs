import BoundedPAConsistency.CodedHierarchy

/-!
# Kernel audit for the coded hierarchy rank

This deliberately small module checks the API needed by the coded restricted
derivation and prints the axioms of the main correctness statements.  Keeping
the audit separate prevents diagnostic output from becoming part of the
library-facing module.
-/

namespace LeanProofs.BoundedPAConsistency.CodedHierarchyAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

-- The recursive rank is represented as a total Sigma-one function.
example : HierarchySymbol.DefinableFunction₁ (V := V)
    HierarchySymbol.sigmaOne (rankPair L) := inferInstance

-- The well-formed-and-bounded predicate has the Delta-one interface required
-- for insertion with either polarity in a fixed-point blueprint.
example : HierarchySymbol.DefinableRel (V := V)
    HierarchySymbol.deltaOne (QuantifierBoundedCode L) := inferInstance

-- Fixing a metatheoretic bound specializes the binary relation to a
-- Delta-one predicate on codes.
example (n : Nat) : HierarchySymbol.DefinablePred (V := V)
    HierarchySymbol.deltaOne (QuantifierBoundedAt L n) := inferInstance

#check rankPair_quote
#check quantifierGroupsCode_quote
#check quantifierBoundedCode_quote_iff
#check QuantifierBoundedCode.mono
#check rankPair_neg
#check rankPair_shift
#check rankPair_subst
#check QuantifierBoundedCode.neg_iff
#check QuantifierBoundedCode.shift_iff
#check QuantifierBoundedCode.substs1
#check QuantifierBoundedCode.free

#print axioms rankPair_quote
#print axioms quantifierGroupsCode_quote
#print axioms quantifierBoundedCode_quote_iff
#print axioms QuantifierBoundedCode.defined
#print axioms rankPair_neg
#print axioms rankPair_shift
#print axioms rankPair_subst

end LeanProofs.BoundedPAConsistency.CodedHierarchyAudit
