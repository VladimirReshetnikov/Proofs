import Mathlib.NumberTheory.FLT.Four

/-!
# Fermat's Last Theorem, exponent 4

This module records the classical `n = 4` case of Fermat's Last Theorem in
the positive-natural-number form.
-/

namespace LeanProofs

/-- Fermat's Last Theorem for exponent `4`, in the usual positive natural-number form. -/
theorem fermat_four_no_positive_nat_solutions
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 + b ^ 4 ≠ c ^ 4 := by
  exact fermatLastTheoremFour a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)

/-- The stronger descent statement used in the classical proof of the exponent `4` case. -/
theorem fermat_four_no_square_right_int_solutions
    {a b c : Int} (ha : a ≠ 0) (hb : b ≠ 0) :
    a ^ 4 + b ^ 4 ≠ c ^ 2 := by
  exact not_fermat_42 ha hb

end LeanProofs
