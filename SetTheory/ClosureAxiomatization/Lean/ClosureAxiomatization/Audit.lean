import ClosureAxiomatization

/-! Assumption audit for Closure <-> ZF. -/

open SetTheory

#check @T_iff_ZF
#check @T_iff_ZF_via_theory_equiv
#check @ZF_implies_T
#check @T_implies_ZF
#check @T_ZF_same_models
#print axioms T_iff_ZF
#print axioms T_ZF_same_models

#check @Forward.Pairing
#check @Forward.Union
#check @Forward.Replacement
#check @Forward.Infinity
#print axioms Forward.Pairing
#check @Reverse.Closure_holds
#print axioms Reverse.Closure_holds
