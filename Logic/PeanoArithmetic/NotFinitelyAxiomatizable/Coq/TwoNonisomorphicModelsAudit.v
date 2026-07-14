(** Focused kernel-assumption audit for the two-model theorem. *)

From PAFiniteBasisReduction Require Import TwoNonisomorphicModels.

Import PATwoNonisomorphicModels.

Check FirstOrderPAModel.
Check RawPAIso.
Check NumeralGenerated.
Check standardPAModel.
Check nonstandardPAModel_exists.
Check peano_arithmetic_has_two_nonisomorphic_models.

Print Assumptions peano_arithmetic_has_two_nonisomorphic_models.
