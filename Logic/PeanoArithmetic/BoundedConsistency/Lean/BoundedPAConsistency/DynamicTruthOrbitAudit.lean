import BoundedPAConsistency.DynamicTruthOrbit

/-!
# Audit surface for the represented dynamic-truth orbit

This file is deliberately theorem-free.  It makes the public construction
and its critical equations easy to inspect, and asks Lean to report the
axioms used by the two internally inducted syntactic invariants.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthOrbitAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit

#check parameterArity
#check successorCodeWithParameters
#check truthFormulaZeroDef
#check truthFormulaSuccDef
#check LeanProofs.BoundedPAConsistency.DynamicTruthOrbit.blueprint
#check LeanProofs.BoundedPAConsistency.DynamicTruthOrbit.construction
#check truthFormulaParameters
#check successorCodeWithParameters_eq
#check truthFormulaComputationGraph
#check truthFormulaComputation_defined
#check truthFormulaCode_definable

#check truthFormulaCode_zero
#check truthFormulaCode_succ
#check truthFormulaCode_isSemiformula
#check truthFormulaCode_shift
#check truthFormula
#check truthFormula_zero
#check truthFormula_succ
#check truthFormula_shift

#print axioms successorCodeWithParameters_eq
#print axioms truthFormulaComputation_defined
#print axioms truthFormulaCode_definable
#print axioms truthFormulaCode_zero
#print axioms truthFormulaCode_succ
#print axioms truthFormulaCode_isSemiformula
#print axioms truthFormulaCode_shift

end LeanProofs.BoundedPAConsistency.DynamicTruthOrbitAudit
