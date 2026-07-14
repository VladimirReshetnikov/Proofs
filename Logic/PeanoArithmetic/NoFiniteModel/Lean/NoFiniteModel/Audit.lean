import NoFiniteModel

/-! Kernel-assumption audit for the PA no-finite-model theorem. -/

open LeanProofs.NoFinitePAModel

#check @IsFiniteType
#check fin_isFiniteType
#check @fin_surjective_of_injective
#check @surjective_of_injective_of_equiv_fin
#check @finite_self_surjective_of_injective
#check @finite_carrier_cannot_have_injective_successor_missing_zero
#check @model_carrier_not_finite
#check @no_finite_PA_model
#check @no_finite_type_supports_PA_model
#check no_PA_model_on_fin
#check nat_not_finite

#print axioms fin_isFiniteType
#print axioms FinEquiv.toFun_injective
#print axioms FinEquiv.invFun_injective
/- `propext` enters through Lean core's finite equality/predecessor
implementation.  There is no `Classical.choice` or excluded-middle axiom. -/
#print axioms swapZero
#print axioms swapZero_involutive
#print axioms swapZero_injective
#print axioms Fin.pred
#print axioms fin_surjective_of_injective
#print axioms surjective_of_injective_of_equiv_fin
#print axioms finite_self_surjective_of_injective
#print axioms finite_carrier_cannot_have_injective_successor_missing_zero
#print axioms model_carrier_not_finite
#print axioms no_finite_PA_model
#print axioms no_finite_type_supports_PA_model
#print axioms no_PA_model_on_fin
#print axioms nat_not_finite
