import BoundedPAConsistency.OrientedHierarchy

/-!
# Kernel audit for polarity-oriented coded hierarchy domains

The examples deliberately quantify over arbitrary model elements for the
formula code and hierarchy bound.  They therefore exercise the interface used
for nonstandard proof codes, rather than only its behavior on quotations of
ordinary Lean syntax.
-/

namespace LeanProofs.BoundedPAConsistency.OrientedHierarchyAudit

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.CodedHierarchy
open LeanProofs.BoundedPAConsistency.OrientedHierarchy

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable {L : Language} [L.Encodable] [L.LORDefinable]

#check IsSigmaCode.definable
#check IsPiCode.definable
#check quantifierBoundedCode_iff_sigma_or_pi
#check rankCode_balanced
#check QuantifierBoundedCode.toSigmaSucc
#check QuantifierBoundedCode.toPiSucc
#check isSigmaCode_and_iff
#check isPiCode_or_iff
#check isSigmaCode_exs_succ_iff
#check isPiCode_all_succ_iff
#check isSigmaCode_all_add_two_iff
#check isPiCode_exs_add_two_iff
#check isSigmaCode_neg_iff
#check isPiCode_neg_iff
#check isSigmaCode_shift_iff
#check isPiCode_subst_iff
#check isSigmaCode_free_iff

example {n p : V} :
    QuantifierBoundedCode L n p ↔
      IsSigmaCode L n p ∨ IsPiCode L n p :=
  quantifierBoundedCode_iff_sigma_or_pi

example {n p : V} (hp : IsUFormula L p) :
    IsSigmaCode L (n + 1 + 1) (^∀ p) ↔
      IsPiCode L (n + 1) p :=
  isSigmaCode_all_add_two_iff hp

example {n p : V} (hp : IsUFormula L p) :
    IsSigmaCode L n (neg L p) ↔ IsPiCode L n p :=
  isSigmaCode_neg_iff hp

example {b p : V} (hp : IsSemiformula L 1 p) :
    IsPiCode L b (free L p) ↔ IsPiCode L b p :=
  isPiCode_free_iff hp

#print axioms quantifierBoundedCode_iff_sigma_or_pi
#print axioms rankCode_balanced
#print axioms QuantifierBoundedCode.toSigmaSucc
#print axioms isSigmaCode_and_iff
#print axioms isSigmaCode_exs_succ_iff
#print axioms isSigmaCode_all_add_two_iff
#print axioms isSigmaCode_neg_iff
#print axioms isSigmaCode_shift_iff
#print axioms isPiCode_subst_iff
#print axioms isSigmaCode_free_iff

end LeanProofs.BoundedPAConsistency.OrientedHierarchyAudit
