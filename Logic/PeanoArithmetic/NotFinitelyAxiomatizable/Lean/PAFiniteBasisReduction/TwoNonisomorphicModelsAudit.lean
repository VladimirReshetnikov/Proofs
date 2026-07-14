import PAFiniteBasisReduction.TwoNonisomorphicModels

/-! Focused kernel-assumption audit for the two-model theorem. -/

open LeanProofs.PAFiniteBasisReduction

#check TwoNonisomorphicModels.FirstOrderPAModel
#check @TwoNonisomorphicModels.RawPAIso
#check @TwoNonisomorphicModels.NumeralGenerated
#check TwoNonisomorphicModels.standardPAModel
#check TwoNonisomorphicModels.nonstandardPAModel_exists
#check TwoNonisomorphicModels.peano_arithmetic_has_two_nonisomorphic_models

#print axioms TwoNonisomorphicModels.peano_arithmetic_has_two_nonisomorphic_models
