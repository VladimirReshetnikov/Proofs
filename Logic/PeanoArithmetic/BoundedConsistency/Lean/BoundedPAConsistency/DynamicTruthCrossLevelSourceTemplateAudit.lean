import BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate

/-!
# Audit: structural positive cross-level source interface

These checks expose the two-predicate prior context, the unary successor
invariant, their exact arbitrary-model specializations, and their literal
alignment with both adjacent fields of the represented truth orbit.
-/

namespace LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplateAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.DynamicTruthFormula
open LeanProofs.BoundedPAConsistency.DynamicTruthOrbit
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelFormula
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters
open LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplate

#check SourceLanguage
#check predecessorAtom
#check currentAtom
#check sourcePriorCrossLevelBody
#check sourcePriorCrossLevelPredicate
#check sourcePriorCrossLevelContext
#check sourceCurrentSuccessorTruth
#check sourceNextCrossLevelBody
#check sourceNextCrossLevelInvariant
#check directCrossLevelBodyFormula
#check directCrossLevelFormula
#check translate_sourcePriorCrossLevelContext
#check translate_sourceNextCrossLevelInvariant
#check translate_sourceNextCrossLevelInvariant_closure
#check directCrossLevelFormula_successor
#check translate_sourcePriorCrossLevelContext_base
#check translate_sourcePriorCrossLevelContext_orbit
#check translate_sourceNextCrossLevelInvariant_orbit
#check translate_sourceNextCrossLevelInvariant_orbit_closure

#print axioms translate_sourcePriorCrossLevelBody
#print axioms translate_sourcePriorCrossLevelContext
#print axioms translate_sourceCurrentSuccessorTruth
#print axioms translate_sourceNextCrossLevelBody
#print axioms translate_sourceNextCrossLevelInvariant
#print axioms translate_sourceNextCrossLevelInvariant_closure
#print axioms directCrossLevelFormula_successor
#print axioms translate_sourcePriorCrossLevelContext_base
#print axioms translate_sourcePriorCrossLevelContext_orbit
#print axioms translate_sourceNextCrossLevelInvariant_orbit_closure

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

noncomputable section

/-- The fixed source context retains both arbitrary model-coded predicates;
it does not replace the preceding law by an opaque nullary assumption. -/
example (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    translateFormula predecessor current levels
        (Rewriting.emb sourcePriorCrossLevelContext) =
      directCrossLevelFormula predecessor current (levels 0) :=
  translate_sourcePriorCrossLevelContext predecessor current levels

/-- The invariant's closure is the advertised concrete successor field for
arbitrary predicates and possibly nonstandard named levels. -/
example (predecessor current : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (levels : Fin 3 → V) :
    (∀⁰ translateFormula predecessor current levels
        (Rewriting.emb sourceNextCrossLevelInvariant)) =
      crossLevelFormula current (levels 1) (levels 2) :=
  translate_sourceNextCrossLevelInvariant_closure predecessor current levels

/-- At an arbitrary positive orbit index, the source context is exactly the
field assumed from the current certificate. -/
example (n : V) :
    translateFormula (truthFormula n) (truthFormula (n + 1))
        ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
        (Rewriting.emb sourcePriorCrossLevelContext) =
      orbitSuccessorCrossLevelFormula n :=
  translate_sourcePriorCrossLevelContext_orbit n

/-- Closing the same specialization's invariant is exactly the field needed
by the next certificate. -/
example (n : V) :
    (∀⁰ translateFormula (truthFormula n) (truthFormula (n + 1))
        ![n + 1, n + 1 + 1, n + 1 + 1 + 1]
        (Rewriting.emb sourceNextCrossLevelInvariant)) =
      orbitSuccessorCrossLevelFormula (n + 1) :=
  translate_sourceNextCrossLevelInvariant_orbit_closure n

end

end LeanProofs.BoundedPAConsistency.DynamicTruthCrossLevelSourceTemplateAudit
