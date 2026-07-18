import BoundedPAConsistency.QuantifierFreeTruth

/-!
# Kernel audit for coded quantifier-free truth

The evaluator is meaningful only on the explicitly represented rank-zero
domain.  These checks keep that boundary visible and ask Lean to report the
assumptions of its represented graph and semantic clauses.
-/

namespace LeanProofs.BoundedPAConsistency.QuantifierFreeTruthAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.QuantifierFreeTruth

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]

example : HierarchySymbol.DefinablePred (V := V)
    HierarchySymbol.deltaOne IsQuantifierFreeCode := inferInstance

example : HierarchySymbol.DefinableFunction₃ (V := V)
    HierarchySymbol.sigmaOne (qfValue : V → V → V → V) := inferInstance

example : HierarchySymbol.DefinableRel₃ (V := V)
    HierarchySymbol.sigmaOne (QFTrue : V → V → V → Prop) := inferInstance

#check qfValue_eq_atom_iff
#check qfValue_neq_atom_iff
#check qfValue_lt_atom_iff
#check qfValue_nlt_atom_iff
#check qfValue_and_eq_one_iff
#check qfValue_or_eq_one_iff
#check qfValue_isBit
#check qfTrue_iff_not_qfFalse

#print axioms qfValue.defined
#print axioms qfValue_eq_atom_iff
#print axioms qfValue_nlt_atom_iff
#print axioms qfValue_isBit
#print axioms qfTrue_iff_not_qfFalse

end LeanProofs.BoundedPAConsistency.QuantifierFreeTruthAudit
