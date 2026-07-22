import BoundedPAConsistency.ModelCodedTwoPredicateParameters

/-!
# Audit: two-predicate proof-template specialization

The examples below ensure that the two source relation symbols are kept
independent and become the exact supplied model-coded formulas.  They also
expose the compiler and its represented PA-proof endpoint to the axiom
auditor.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParametersAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParameters

#check twoPredicateParameterLanguage
#check translateTerm
#check translateFormula
#check translateFormula_neg
#check translateFormula_shift
#check translateFormula_subst
#check translation
#check arithmeticHom
#check twoPredicateParameterPeano
#check theoryTranslation
#check compilePeanoTemplate
#check compilePeanoTemplate_isPAProof

#print axioms translateFormula_neg
#print axioms translateFormula_shift
#print axioms translateFormula_subst
#print axioms translateFormula_lMap_arithmetic_emb
#print axioms compilePeanoTemplate
#print axioms compilePeanoTemplate_isPAProof

/-- A nullary occurrence of the first placeholder. -/
def firstAtom :
    Sentence (twoPredicateParameterLanguage 0 3 2) :=
  .rel (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate)) ![]

/-- A ternary occurrence of the second placeholder. -/
def secondAtom :
    Semisentence (twoPredicateParameterLanguage 0 3 2) 3 :=
  .rel (Sum.inr (Sum.inr (Sum.inl
    ModelCodedPredicateTemplate.PlaceholderRel.predicate)))
    ![#0, #1, #2]

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The first relation specializes to the closed context formula. -/
example (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) :
    translateFormula context lower parameters
        (Rewriting.emb firstAtom) = context := by
  simp [firstAtom, translateFormula]

/-- The second relation independently specializes to the ternary lower
truth formula. -/
example (context : Bootstrapping.Formula V ℒₒᵣ)
    (lower : Bootstrapping.Semiformula V ℒₒᵣ 3)
    (parameters : Fin 2 → V) :
    translateFormula context lower parameters
        (Rewriting.emb secondAtom) = lower := by
  simp [secondAtom, translateFormula]
  apply Bootstrapping.Semiformula.subst_eq_self
  intro i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          cases i using Fin.cases with
          | zero => rfl
          | succ i => exact i.elim0

end LeanProofs.BoundedPAConsistency.ModelCodedTwoPredicateParametersAudit
