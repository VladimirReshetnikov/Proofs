import FirstOrder

/-! Assumption audit for the reusable first-order logic library. -/

open SetTheory

#check @soundness
#check @completeness
#check @prov_iff_valid
#check @completeness_inf
#check @theory_transfer
#check @theory_equiv
#print axioms soundness
#print axioms prov_iff_valid
#print axioms theory_transfer
