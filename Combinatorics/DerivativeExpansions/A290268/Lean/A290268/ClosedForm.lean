import A290268.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# A290268: the closed form, its linear recurrence, and the g.f. denominator

[A290268](https://oeis.org/A290268) publishes the conjectured description of
the sequence in three interchangeable shapes: the closed form (recorded in
`LeanProofs/A290268.lean` as `closedForm`), the order-12 linear recurrence
with signature `(0, 2, 0, -1, 0, 0, 0, 1, 0, -2, 0, 1)`, and the rational
generating function with denominator `(1-x)(1-x²)(1-x⁸)`.

This module proves that `closedForm` satisfies all of them, so any of the
three may be taken as *the* conjectured formula:

* `closedForm_even` / `closedForm_odd` — the bisected polynomial forms
  `a(2m) = 2m² + 2m + 1` and `a(2m+1) = 2(m+1)² - ⌊(m+1)/4⌋`;
* `closedForm_initial` — the twelve initial values `1, 2, 5, 8, 13, 18, 25,
  31, 41, 49, 61, 71`, which together with either recurrence pin the
  sequence down uniquely;
* `closedForm_linear_recurrence` — the signature recurrence
  `a(n+12) = 2a(n+10) - a(n+8) + a(n+4) - 2a(n+2) + a(n)`, stated
  additively to avoid natural subtraction;
* `closedForm_gf_recurrence` — the recurrence read off the denominator
  `(1-x)(1-x²)(1-x⁸) = 1 - x - x² + x³ - x⁸ + x⁹ + x¹⁰ - x¹¹`; since the
  numerator of the generating function has degree 9 < 11, it holds for all
  `n ≥ 0`.

All proofs follow one pattern: split `n` by parity, rewrite every shifted
argument into the `2*_` / `2*_+1` shape handled by `closedForm_even` and
`closedForm_odd`, expand the squares into `m*m` by `ring`, generalize the
single nonlinear atom `m*m`, and close with `omega` (which decides the
remaining linear arithmetic with `/4` and truncated subtraction).
-/

namespace LeanProofs

namespace A290268

/-- Every natural number is `2*m` or `2*m + 1`.  (Stated with `2*_` rather
than mathlib's `Even`/`Odd` so the witnesses plug directly into
`closedForm_even` and `closedForm_odd`.) -/
private theorem two_mul_or_two_mul_add_one (n : ℕ) :
    (∃ m, n = 2 * m) ∨ (∃ m, n = 2 * m + 1) :=
  (Nat.mod_two_eq_zero_or_one n).imp
    (fun h => ⟨n / 2, by omega⟩) (fun h => ⟨n / 2, by omega⟩)

/-- The even bisection of the closed form: `a(2m) = 2m² + 2m + 1`
(the centered square numbers). -/
theorem closedForm_even (m : ℕ) : closedForm (2 * m) = 2 * m ^ 2 + 2 * m + 1 := by
  simp only [closedForm]
  rw [if_pos (show 2 * m % 2 = 0 by omega),
    show (2 * m) ^ 2 = 4 * (m * m) by ring, show m ^ 2 = m * m by ring]
  generalize m * m = s
  omega

/-- The odd bisection of the closed form: `a(2m+1) = 2(m+1)² - ⌊(m+1)/4⌋`. -/
theorem closedForm_odd (m : ℕ) :
    closedForm (2 * m + 1) = 2 * (m + 1) ^ 2 - (m + 1) / 4 := by
  simp only [closedForm]
  rw [if_neg (show ¬(2 * m + 1) % 2 = 0 by omega),
    show (2 * m + 1 + 1) ^ 2 = 4 * (m * m) + 8 * m + 4 by ring,
    show (m + 1) ^ 2 = m * m + 2 * m + 1 by ring]
  generalize m * m = s
  omega

/-- The first twelve values of the closed form.  Together with the order-12
recurrence `closedForm_linear_recurrence` these determine the whole
sequence, so they make the recurrence description equivalent to the closed
form. -/
theorem closedForm_initial :
    closedForm 0 = 1 ∧ closedForm 1 = 2 ∧ closedForm 2 = 5 ∧ closedForm 3 = 8 ∧
    closedForm 4 = 13 ∧ closedForm 5 = 18 ∧ closedForm 6 = 25 ∧ closedForm 7 = 31 ∧
    closedForm 8 = 41 ∧ closedForm 9 = 49 ∧ closedForm 10 = 61 ∧ closedForm 11 = 71 := by
  decide

/-- The OEIS order-12 linear recurrence with signature
`(0, 2, 0, -1, 0, 0, 0, 1, 0, -2, 0, 1)`, i.e.
`a(n+12) = 2a(n+10) - a(n+8) + a(n+4) - 2a(n+2) + a(n)`, rearranged
additively to avoid natural subtraction.  Its characteristic polynomial
`1 - 2x² + x⁴ - x⁸ + 2x¹⁰ - x¹² = (1-x²)²(1-x⁸)` is the generating-function
denominator `(1-x)(1-x²)(1-x⁸)` times the extra factor `(1+x)`, so this
recurrence is implied by `closedForm_gf_recurrence` (but is proved here
directly). -/
theorem closedForm_linear_recurrence (n : ℕ) :
    closedForm (n + 12) + closedForm (n + 8) + 2 * closedForm (n + 2)
      = 2 * closedForm (n + 10) + closedForm (n + 4) + closedForm n := by
  rcases two_mul_or_two_mul_add_one n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even case: all six arguments are even, and the recurrence is a
    -- polynomial identity with no floors, so `ring` closes it.
    rw [show 2 * m + 12 = 2 * (m + 6) by ring, show 2 * m + 10 = 2 * (m + 5) by ring,
      show 2 * m + 8 = 2 * (m + 4) by ring, show 2 * m + 4 = 2 * (m + 2) by ring,
      show 2 * m + 2 = 2 * (m + 1) by ring]
    simp only [closedForm_even]
    ring
  · -- odd case: all six arguments are odd; after expanding the squares the
    -- goal is linear in `m` and `s = m*m` with `/4` floors, which `omega`
    -- decides.
    rw [show 2 * m + 1 + 12 = 2 * (m + 6) + 1 by ring,
      show 2 * m + 1 + 10 = 2 * (m + 5) + 1 by ring,
      show 2 * m + 1 + 8 = 2 * (m + 4) + 1 by ring,
      show 2 * m + 1 + 4 = 2 * (m + 2) + 1 by ring,
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring]
    simp only [closedForm_odd]
    rw [show (m + 6 + 1) ^ 2 = m * m + 14 * m + 49 by ring,
      show (m + 5 + 1) ^ 2 = m * m + 12 * m + 36 by ring,
      show (m + 4 + 1) ^ 2 = m * m + 10 * m + 25 by ring,
      show (m + 2 + 1) ^ 2 = m * m + 6 * m + 9 by ring,
      show (m + 1 + 1) ^ 2 = m * m + 4 * m + 4 by ring,
      show (m + 1) ^ 2 = m * m + 2 * m + 1 by ring]
    generalize m * m = s
    omega

/-- The recurrence read off the generating-function denominator
`(1-x)(1-x²)(1-x⁸) = 1 - x - x² + x³ - x⁸ + x⁹ + x¹⁰ - x¹¹`:
`a(n+11) - a(n+10) - a(n+9) + a(n+8) - a(n+3) + a(n+2) + a(n+1) - a(n) = 0`,
stated additively.  The numerator of the generating function has degree
9 < 11, so the identity holds for all `n ≥ 0` (checked: at `n = 0` both
sides are `71 + 41 + 5 + 2 = 61 + 49 + 8 + 1 = 119`).

Note the grouping: the `x³` and `x⁸` coefficients of the denominator are
`+1` and `-1`, so `a(n+8)` and `a(n+2), a(n+1)` sit on the left while
`a(n+3)` and `a(n)` sit on the right — not the other way around. -/
theorem closedForm_gf_recurrence (n : ℕ) :
    closedForm (n + 11) + closedForm (n + 8) + closedForm (n + 2) + closedForm (n + 1)
      = closedForm (n + 10) + closedForm (n + 9) + closedForm (n + 3) + closedForm n := by
  rcases two_mul_or_two_mul_add_one n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- even case: `n, n+2, n+8, n+10` are even and `n+1, n+3, n+9, n+11` odd.
    rw [show 2 * m + 11 = 2 * (m + 5) + 1 by ring,
      show 2 * m + 10 = 2 * (m + 5) by ring,
      show 2 * m + 9 = 2 * (m + 4) + 1 by ring,
      show 2 * m + 8 = 2 * (m + 4) by ring,
      show 2 * m + 3 = 2 * (m + 1) + 1 by ring,
      show 2 * m + 2 = 2 * (m + 1) by ring]
    simp only [closedForm_even, closedForm_odd]
    -- Note: `rw` abstracts occurrences up to defeq, so the pattern
    -- `(m + 4 + 1) ^ 2` also rewrites the defeq `(m + 5) ^ 2`, etc.
    rw [show (m + 5 + 1) ^ 2 = m * m + 12 * m + 36 by ring,
      show (m + 4 + 1) ^ 2 = m * m + 10 * m + 25 by ring,
      show (m + 1 + 1) ^ 2 = m * m + 4 * m + 4 by ring,
      show (m + 4) ^ 2 = m * m + 8 * m + 16 by ring,
      show (m + 1) ^ 2 = m * m + 2 * m + 1 by ring,
      show m ^ 2 = m * m by ring]
    generalize m * m = s
    omega
  · -- odd case: `n, n+2, n+8, n+10` are odd and `n+1, n+3, n+9, n+11` even.
    rw [show 2 * m + 1 + 11 = 2 * (m + 6) by ring,
      show 2 * m + 1 + 10 = 2 * (m + 5) + 1 by ring,
      show 2 * m + 1 + 9 = 2 * (m + 5) by ring,
      show 2 * m + 1 + 8 = 2 * (m + 4) + 1 by ring,
      show 2 * m + 1 + 3 = 2 * (m + 2) by ring,
      show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by ring,
      show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    simp only [closedForm_even, closedForm_odd]
    -- `(m + 6) ^ 2` also rewrites the defeq `(m + 5 + 1) ^ 2`, etc.
    rw [show (m + 6) ^ 2 = m * m + 12 * m + 36 by ring,
      show (m + 5) ^ 2 = m * m + 10 * m + 25 by ring,
      show (m + 2) ^ 2 = m * m + 4 * m + 4 by ring,
      show (m + 1) ^ 2 = m * m + 2 * m + 1 by ring]
    generalize m * m = s
    omega

end A290268

end LeanProofs
