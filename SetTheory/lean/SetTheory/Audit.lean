/-
  Audit.lean — the Lean analogue of the Coq files' trailing `Check` /
  `Print Assumptions` commands: type-check the headline results and print
  the axioms each depends on.  Expected: only Lean's standard classical
  axioms (`Classical.choice`, `propext`, `Quot.sound`) — no `sorry`.
-/
import SetTheory

open SetTheory

-- the headline: full deductive equivalence T ⊢ φ ⟺ ZF ⊢ φ
#check @T_iff_ZF
#print axioms T_iff_ZF
#print axioms T_iff_ZF_via_theory_equiv

-- syntactic directions and same-models
#check @ZF_implies_T
#check @T_implies_ZF
#check @T_ZF_same_models
#print axioms T_ZF_same_models

-- Gödel completeness layer
#check @completeness
#check @prov_iff_valid
#check @completeness_inf
#check @theory_equiv
#print axioms prov_iff_valid

-- calculus soundness and the deep reverse (internal recursion theorem)
#check @soundness
#check @ClosureFO_of_ZF
#print axioms ClosureFO_of_ZF

-- PA/HF Ackermann/von-Neumann semantic bi-interpretability checkpoint
#check @AckermannHF.PA_biinterpretable_with_HF_standard
#print axioms AckermannHF.PA_biinterpretable_with_HF_standard

-- the shallow self-contained pair, with their free dependency audits
#check @Forward.Pairing
#check @Forward.Union
#check @Forward.Replacement
#check @Forward.Infinity
#print axioms Forward.Pairing
#check @Reverse.Closure_holds
#print axioms Reverse.Closure_holds
