import FirstOrder

/-! Assumption audit for the reusable first-order logic library. -/

open SetTheory
open SetTheory.FirstOrderCompactness

#check @soundness
#check @completeness
#check @prov_iff_valid
#check @completeness_inf
#check @theory_transfer
#check @theory_equiv
#check @TheoryHasModel
#check @FiniteSubtheoriesHaveModels
#check @theoryHasModel_finiteSubtheoriesHaveModels
#check @theoryHasModel_of_finiteSubtheoriesHaveModels
#check @compactness
#check @relativize_rename
#check @Free_relativize
#check @Sentence_relativize_iff
#check @Sat_relativize
#print axioms soundness
#print axioms prov_iff_valid
#print axioms theory_transfer
#print axioms compactness
#print axioms Sat_relativize
