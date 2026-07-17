(**
  Focused assumption and kernel audit for Diophantine exponentiation.

  This target deliberately excludes [NumberTheoryFactorization], whose
  MathComp dependency currently requires an older Rocq release.  The direct
  Matiyasevich proof and the finite-vector single-equation bridge use only the
  standard library and the vendored Undecidability development.
*)

From PAListCoding Require Import
  NumberTheory ExponentiationDiophantine.

Check PAListNumberTheory.PowerNat.
Check PAListExponentiationDiophantine.finiteEnv.
Check PAListExponentiationDiophantine.dio_rel_Diophantine.
Check PAListExponentiationDiophantine.NatPowFunction.
Check PAListExponentiationDiophantine.nat_pow_dio_fun.
Check PAListExponentiationDiophantine.PowerNat_dio_rel.
Check PAListExponentiationDiophantine.powerNatDiophantineFormula.
Check PAListExponentiationDiophantine.powerNatDiophantineFormula_spec.
Check PAListExponentiationDiophantine.powerNatDiophantineEquation.
Check PAListExponentiationDiophantine.PowerNatVector.
Check PAListExponentiationDiophantine.PowerNat_Diophantine.

Print Assumptions PAListExponentiationDiophantine.nat_pow_eq_mscal.
Print Assumptions PAListExponentiationDiophantine.dio_rel_Diophantine.
Print Assumptions PAListExponentiationDiophantine.nat_pow_dio_fun.
Print Assumptions PAListExponentiationDiophantine.PowerNat_dio_rel.
Print Assumptions
  PAListExponentiationDiophantine.powerNatDiophantineFormula_spec.
Print Assumptions PAListExponentiationDiophantine.PowerNat_Diophantine.
