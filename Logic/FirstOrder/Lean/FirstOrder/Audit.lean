import FirstOrder

/-! Assumption audit for the reusable first-order logic library. -/

open SetTheory
open SetTheory.FirstOrderCompactness
open SetTheory.FirstOrderClassicalCompleteness

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
#check @SemanticConsequence
#check @SyntacticConsequence
#check @TheorySemanticConsequence
#check @TheorySyntacticConsequence
#check @TheoryConsistent
#check @theoryConsistent_iff_BCon
#check @godel_original_completeness
#check @godel_completeness
#check @godel_soundness_and_completeness
#check @godel_completeness_for_theories
#check @godel_soundness_and_completeness_for_theories
#check @godel_model_existence
#check @theory_consistent_iff_has_model
#check @relativize_rename
#check @Free_relativize
#check @Sentence_relativize_iff
#check @Sat_relativize
#print axioms soundness
#print axioms prov_iff_valid
#print axioms theory_transfer
#print axioms compactness
#print axioms theoryConsistent_iff_BCon
#print axioms godel_original_completeness
#print axioms godel_soundness_and_completeness_for_theories
#print axioms godel_model_existence
#print axioms theory_consistent_iff_has_model
#print axioms Sat_relativize
