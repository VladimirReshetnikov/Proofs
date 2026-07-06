import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Set.Card

/-!
# Initial values of OEIS A198683

OEIS A198683 counts the distinct principal values of all binary
parenthesizations of `i^i^...^i`.  This module defines the value set directly
over `ℂ`, with principal power interpreted as `exp (log z * w)`.

The accepted OEIS data currently run through `n = 11`; `n = 12` is deliberately
not included in the OEIS data field because the local corpus records it as
still awaiting a proof-quality certificate.
-/

namespace LeanProofs

noncomputable section

open Complex

/-- Principal complex power, written separately from Lean's `Pow` instance so
the definition used for the sequence is visible in this module. -/
def principalPow (z w : ℂ) : ℂ :=
  Complex.exp (Complex.log z * w)

scoped infixr:80 " ^^ " => principalPow

/--
The set of values produced by all binary parenthesizations of `n` copies of
`i`, with every binary node interpreted as principal complex power.

The `0` case is an empty convenience case; OEIS A198683 has offset `1`.
-/
def a198683ValueSet : Nat → Set ℂ
  | 0 => ∅
  | 1 => {Complex.I}
  | n + 2 =>
      {z | ∃ k : Fin (n + 1),
        ∃ x ∈ a198683ValueSet (k.1 + 1),
        ∃ y ∈ a198683ValueSet (n + 1 - k.1),
          z = x ^^ y}
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- OEIS A198683, as a cardinality of the semantic value set above. -/
def a198683 (n : Nat) : Nat :=
  (a198683ValueSet n).ncard

/-- `A198683(1) = 1`. -/
theorem a198683_one : a198683 1 = 1 := by
  simp [a198683, a198683ValueSet]

end

end LeanProofs
