import A290268.Core

/-!
# A290268: a memoized coefficient table and the machine-checked OEIS range

The counting function `a n` of
[A290268](https://oeis.org/A290268) is defined in `A290268.Core` from the
four-branch differentiation recurrence `coeff`.  Evaluating `coeff n j k`
directly is a tree recursion of size `4 ^ n`, so `native_decide` on `a n` is
infeasible even for small `n`.

This module gives a **memoized presentation** of the same recurrence as a
dense `107 × 55` array of `ℤ`s (`step`, `tbl`), and proves — by induction on
`n`, using only the `coeff` recurrence and its support (vanishing) lemmas —
the agreement theorem

```text
get_tbl : ∀ n ≤ 53, ∀ j k, get (tbl n) (j + 53) k = coeff n j k.
```

Because `get_tbl` identifies the *table* entries with the *recurrence*
coefficients, the number of nonzero table entries (`tblCount n`) equals the
number of nonzero coefficients (`a n`) on the whole range `n ≤ 53`
(`a_eq_tblCount`).  The table is computed in compiled code by a single
`native_decide`, which therefore certifies a statement about `a` itself:

```text
a_values_le_53 : ∀ n ≤ 53, a n = closedForm n.
```

This verifies the OEIS A290268 conjecture (`a n = closedForm n`)
*unconditionally* on the entire published range `n = 0, …, 53`.

## The array layout

Columns `j ∈ [-53, 53]` are indexed by `jj = j + 53 ∈ [0, 106]` (width `107`);
log-degrees `k ∈ [0, 54]` are indexed directly (width `55`, the extra slot
`k = 54` giving zero padding so the `k + 1` reads stay in range).  `get`
returns `0` outside the window, matching the fact that `coeff n j k` vanishes
there for every `n ≤ 53`.
-/

namespace LeanProofs

namespace A290268

/-- Read entry `(x, y)` of a table, in the shifted coordinates
`x = j + 53 ∈ [0, 106]`, `y = k ∈ [0, 54]`; out of that window, and for the
padding column `y = 54`'s neighbours, the value is `0`. -/
def get (T : Array (Array ℤ)) (x y : ℤ) : ℤ :=
  if 0 ≤ x ∧ x ≤ 106 ∧ 0 ≤ y ∧ y ≤ 54 then (T.getD x.toNat #[]).getD y.toNat 0 else 0

/-- One differentiation step on the dense table.  With `x = j + 53`, `y = k`,
the weight `(j + 1)` becomes `x - 52` and the four branches are the parent
cells `(j-1, k-1)`, `(j-1, k)`, `(j+1, k)`, `(j+1, k+1)`. -/
def step (T : Array (Array ℤ)) : Array (Array ℤ) :=
  Array.ofFn (n := 107) fun jj : Fin 107 => Array.ofFn (n := 55) fun kk : Fin 55 =>
    2 * get T ((jj.val : ℤ) - 1) ((kk.val : ℤ) - 1)
      + get T ((jj.val : ℤ) - 1) (kk.val : ℤ)
      + ((jj.val : ℤ) - 52) * get T ((jj.val : ℤ) + 1) (kk.val : ℤ)
      + ((kk.val : ℤ) + 1) * get T ((jj.val : ℤ) + 1) ((kk.val : ℤ) + 1)

/-- The memoized coefficient table: `tbl 0` has a single `1` at the origin
`(j, k) = (0, 0)`, i.e. cell `[53][0]`, and each further row is one `step`. -/
def tbl : ℕ → Array (Array ℤ)
  | 0 =>
      Array.ofFn (n := 107) fun jj : Fin 107 => Array.ofFn (n := 55) fun kk : Fin 55 =>
        if jj.val = 53 ∧ kk.val = 0 then (1 : ℤ) else 0
  | n + 1 => step (tbl n)

/-- `Array.getD` on `Array.ofFn` at an in-range index reads the corresponding
value of the generating function. -/
theorem ofFn_getD_of_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) {i : ℕ}
    (h : i < m) : (Array.ofFn f).getD i d = f ⟨i, h⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos h, Option.getD_some]

/-- `get` of a single `step`, expressed directly in terms of the parent
table's `get`.  In the window the four differentiation branches appear;
outside it the value is `0`. -/
theorem get_step (T : Array (Array ℤ)) (x y : ℤ) :
    get (step T) x y =
      if 0 ≤ x ∧ x ≤ 106 ∧ 0 ≤ y ∧ y ≤ 54 then
        2 * get T (x - 1) (y - 1) + get T (x - 1) y
          + (x - 52) * get T (x + 1) y + (y + 1) * get T (x + 1) (y + 1)
      else 0 := by
  rw [get]
  by_cases hw : 0 ≤ x ∧ x ≤ 106 ∧ 0 ≤ y ∧ y ≤ 54
  · rw [if_pos hw, if_pos hw]
    obtain ⟨hx0, hx1, hy0, hy1⟩ := hw
    have hxlt : x.toNat < 107 := by omega
    have hylt : y.toNat < 55 := by omega
    rw [step, ofFn_getD_of_lt _ _ hxlt]
    dsimp only
    rw [ofFn_getD_of_lt _ _ hylt]
    dsimp only
    rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0]
  · rw [if_neg hw, if_neg hw]

/-- **Agreement theorem.**  On the entire published range `n ≤ 53`, the
memoized table reproduces the differentiation recurrence: the shifted table
entry `get (tbl n) (j + 53) k` equals `coeff n j k`.  Proved by induction on
`n`, with the induction hypothesis quantified over all `j, k`. -/
theorem get_tbl : ∀ (n : ℕ), n ≤ 53 → ∀ (j k : ℤ), get (tbl n) (j + 53) k = coeff n j k := by
  intro n
  induction n with
  | zero =>
    intro _ j k
    rw [coeff_zero, get]
    by_cases hw : 0 ≤ j + 53 ∧ j + 53 ≤ 106 ∧ 0 ≤ k ∧ k ≤ 54
    · rw [if_pos hw]
      obtain ⟨h1, h2, h3, h4⟩ := hw
      have hjlt : (j + 53).toNat < 107 := by omega
      have hklt : k.toNat < 55 := by omega
      rw [tbl, ofFn_getD_of_lt _ _ hjlt]
      dsimp only
      rw [ofFn_getD_of_lt _ _ hklt]
      dsimp only
      split_ifs <;> omega
    · rw [if_neg hw, if_neg (by rintro ⟨rfl, rfl⟩; exact hw (by omega))]
  | succ n ih =>
    intro hn j k
    have ihjk := ih (by omega)
    rw [tbl, get_step]
    by_cases hw : 0 ≤ j + 53 ∧ j + 53 ≤ 106 ∧ 0 ≤ k ∧ k ≤ 54
    · rw [if_pos hw]
      have r1 : j + 53 - 1 = j - 1 + 53 := by ring
      have r2 : j + 53 + 1 = j + 1 + 53 := by ring
      rw [r1, r2, ihjk (j - 1) (k - 1), ihjk (j - 1) k, ihjk (j + 1) k,
        ihjk (j + 1) (k + 1), coeff_succ]
      ring
    · rw [if_neg hw]
      symm
      by_cases hk0 : k < 0
      · exact coeff_eq_zero_of_k_neg _ _ _ hk0
      · by_cases hjhi : (53 : ℤ) < j
        · exact coeff_eq_zero_of_gt _ _ _ (by omega)
        · by_cases hjlo : j < -53
          · exact coeff_eq_zero_of_lt _ _ _ (by omega)
          · exact coeff_eq_zero_of_two_k_gt _ _ _ (by omega)

/-- The memoized count: the number of nonzero table entries inside the
counting window.  The `let` binds `tbl n` so that it is evaluated once, not
once per lattice point, which keeps the compiled evaluation fast. -/
def tblCount (n : ℕ) : ℕ :=
  let T := tbl n
  (((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (0 : ℤ) (n : ℤ))).filter
    fun p => get T (p.1 + 53) p.2 ≠ 0).card

/-- On the range `n ≤ 53`, the memoized count equals `a n`: `get_tbl` makes the
table's nonzero-entry count a statement about the coefficient array itself. -/
theorem a_eq_tblCount (n : ℕ) (hn : n ≤ 53) : a n = tblCount n := by
  have hpred : ∀ p : ℤ × ℤ,
      (get (tbl n) (p.1 + 53) p.2 ≠ 0) = (coeff n p.1 p.2 ≠ 0) := by
    intro p; rw [get_tbl n hn p.1 p.2]
  simp only [a, tblCount, hpred]

/-- A single compiled evaluation checking `tblCount n = closedForm n` for all
`n < 54`. -/
theorem tblCount_check :
    (List.range 54).all (fun n => decide (tblCount n = closedForm n)) = true := by
  native_decide

theorem tblCount_eq_closedForm (n : ℕ) (hn : n < 54) : tblCount n = closedForm n := by
  have h := tblCount_check
  rw [List.all_eq_true] at h
  exact of_decide_eq_true (h n (List.mem_range.mpr hn))

/-- **The machine-checked OEIS range.**  For every `n ≤ 53`, the term count
`a n` of the fully expanded `n`-th derivative of `x ^ (x²)` equals the
conjectured closed form.  Via `a_eq_tblCount` (hence `get_tbl`), this is an
unconditional verification of the A290268 conjecture on its entire published
range `n = 0, …, 53`. -/
theorem a_values_le_53 : ∀ n, n ≤ 53 → a n = closedForm n := by
  intro n hn
  rw [a_eq_tblCount n hn, tblCount_eq_closedForm n (by omega)]

end A290268

end LeanProofs
