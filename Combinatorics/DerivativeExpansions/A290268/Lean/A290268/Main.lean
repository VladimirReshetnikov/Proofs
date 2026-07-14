import A290268.Core
import A290268.Count

/-!
# A290268: reduction of the conjecture to the support characterization

The conjecture asserts `a n = closedForm n`, where `a n` is the number of terms
in the fully expanded n-th derivative of `x^(x²)` and `closedForm` is the
quasi-polynomial of the OEIS entry (proved interchangeable with the linear
recurrence and generating function in `A290268.ClosedForm`).

This module records the exact reduction: the whole conjecture is equivalent to
the statement that the *support* of the coefficient array — the set of pairs
`(j, k)` with `coeff n j k ≠ 0` — is the conjectured set `S n` of
`A290268.Count`.  Since `(S n).card = closedForm n` is proved unconditionally
there, `a n = closedForm n` follows the moment the support is pinned down.

The support equality splits into two inclusions:

* the **structural** inclusion `coeff n j k ≠ 0 → (j, k) ∈ S n` (nonzero
  coefficients avoid the wrong parity, the region outside the triangle, and the
  hole line); this is the "easy" half, provable from the structural zero lemmas
  of `A290268.Core` together with the hole-vanishing theorem, and
* the **nonvanishing** inclusion `(j, k) ∈ S n → coeff n j k ≠ 0`; this is the
  genuinely open half of the conjecture (see `Oeis/A290268/README.md`).

`a_eq_closedForm_of_support` below consumes both as a single hypothesis, and
`a_eq_closedForm_of_two_sided` keeps them separate so downstream work can
discharge the structural half unconditionally and leave a lone nonvanishing
obligation.
-/

namespace LeanProofs

namespace A290268

open Finset

/-- The nonzero-coefficient set of the n-th derivative, as a `Finset`, is the
filter of the counting window `a` ranges over. -/
theorem support_filter_eq_of_support (n : ℕ)
    (hsupp : ∀ j k, coeff n j k ≠ 0 ↔ (j, k) ∈ S n) :
    (((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (0 : ℤ) n)).filter
        fun p => coeff n p.1 p.2 ≠ 0) = S n := by
  ext ⟨j, k⟩
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, hne⟩; exact (hsupp j k).mp hne
  · intro hmem; exact ⟨S_subset_window n hmem, (hsupp j k).mpr hmem⟩

/-- **Support-to-count reduction.**  If the nonzero-coefficient set of the n-th
derivative of `x^(x²)` is exactly the conjectured support set `S n`, then the
term count equals the closed form.  This isolates the entire remaining content
of the A290268 conjecture into the single statement that the support is `S n`. -/
theorem a_eq_closedForm_of_support (n : ℕ)
    (hsupp : ∀ j k, coeff n j k ≠ 0 ↔ (j, k) ∈ S n) :
    a n = closedForm n := by
  unfold a
  rw [support_filter_eq_of_support n hsupp, card_S]

/-- The same reduction with the two inclusions kept separate: the structural
inclusion (nonzero implies in `S n`) and the nonvanishing inclusion (in `S n`
implies nonzero). -/
theorem a_eq_closedForm_of_two_sided (n : ℕ)
    (hstruct : ∀ j k, coeff n j k ≠ 0 → (j, k) ∈ S n)
    (hnonvanish : ∀ j k, (j, k) ∈ S n → coeff n j k ≠ 0) :
    a n = closedForm n :=
  a_eq_closedForm_of_support n fun j k => ⟨hstruct j k, hnonvanish j k⟩

/-- The full A290268 conjecture, stated as a single hypothesis over all `n`:
the coefficient support is the conjectured set `S n` at every order.  Under this
hypothesis the sequence equals the closed form (hence, via
`A290268.ClosedForm`, satisfies the OEIS linear recurrence and generating
function). -/
theorem a_eq_closedForm_of_support_all
    (hsupp : ∀ n j k, coeff n j k ≠ 0 ↔ (j, k) ∈ S n) (n : ℕ) :
    a n = closedForm n :=
  a_eq_closedForm_of_support n (hsupp n)

end A290268

end LeanProofs
