(**
  Focused assumption and kernel audit for Diophantine tetration.

  Like the focused exponentiation audit, this target deliberately excludes
  [NumberTheoryFactorization] and its separate MathComp dependency.  The
  proof below depends only on the standard library and the constructive
  Diophantine trace machinery in the vendored Undecidability development.
*)

From PAListCoding Require Import
  ExponentiationDiophantine TetrationDiophantine.

Check PAListTetrationDiophantine.tetration.
Check PAListTetrationDiophantine.stateCode.
Check PAListTetrationDiophantine.stateCode_injective.
Check PAListTetrationDiophantine.TetrationStep.
Check PAListTetrationDiophantine.TetrationStep_dio_rel.
Check PAListTetrationDiophantine.rel_iter_TetrationStep.
Check PAListTetrationDiophantine.tetration_rel_iter.
Check PAListTetrationDiophantine.Tetration_dio_rel.
Check PAListTetrationDiophantine.tetrationDiophantineFormula.
Check PAListTetrationDiophantine.tetrationDiophantineFormula_spec.
Check PAListTetrationDiophantine.tetrationDiophantineEquation.
Check PAListTetrationDiophantine.TetrationVector.
Check PAListTetrationDiophantine.Tetration_Diophantine.

Print Assumptions PAListTetrationDiophantine.stateCode_injective.
Print Assumptions PAListTetrationDiophantine.TetrationStep_dio_rel.
Print Assumptions PAListTetrationDiophantine.rel_iter_TetrationStep.
Print Assumptions PAListTetrationDiophantine.tetration_rel_iter.
Print Assumptions PAListTetrationDiophantine.Tetration_dio_rel.
Print Assumptions
  PAListTetrationDiophantine.tetrationDiophantineFormula_spec.
Print Assumptions PAListTetrationDiophantine.Tetration_Diophantine.
