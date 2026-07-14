From FirstOrder Require Import Fol Relativization Calculus Completeness Compactness
  ClassicalCompleteness.

Import FirstOrderCompactness.
Import FirstOrderClassicalCompleteness.

Check soundness.
Check completeness.
Check prov_iff_valid.
Check completeness_inf.
Check theory_transfer.
Check theory_equiv.
Check TheoryHasModel.
Check FiniteSubtheoriesHaveModels.
Check theoryHasModel_finiteSubtheoriesHaveModels.
Check theoryHasModel_of_finiteSubtheoriesHaveModels.
Check compactness.
Check SemanticConsequence.
Check SyntacticConsequence.
Check TheorySemanticConsequence.
Check TheorySyntacticConsequence.
Check TheoryConsistent.
Check godel_original_completeness.
Check godel_completeness.
Check godel_soundness_and_completeness.
Check godel_completeness_for_theories.
Check godel_soundness_and_completeness_for_theories.
Check godel_model_existence.
Check relativize_rename.
Check Free_relativize.
Check Sentence_relativize.
Check Sat_relativize.
Print Assumptions prov_iff_valid.
Print Assumptions theory_transfer.
Print Assumptions compactness.
Print Assumptions godel_original_completeness.
Print Assumptions godel_soundness_and_completeness_for_theories.
Print Assumptions godel_model_existence.
Print Assumptions Sat_relativize.
