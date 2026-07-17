import Mathlib.NumberTheory.Dioph

/-!
# Compiling integer polynomials to sparse-cipher circuits

Matiyasevich's bounded-universal construction evaluates one fixed integer
polynomial simultaneously at every index below a variable bound.  This file
contains the finite, syntax-directed part of that construction.  An integer
polynomial is first split into a pair of natural expressions `(positive,
negative)`; sparse ciphers can then evaluate those expressions columnwise
using only constant, addition, and multiplication gates.

Keeping this compiler separate from the eventual quantifier-elimination
theorem makes two points explicit:

* the number of circuit gates is fixed by the polynomial in the metatheory;
* the number of rows is the input-dependent quantity hidden by the cipher.
-/

namespace PAListCoding

namespace PolynomialCipher

open scoped BigOperators

universe u

/-! ## A syntax tree recovered from Mathlib's semantic polynomials -/

/-- The four constructors used by Mathlib's `IsPoly`, retained as data so
that the same fixed circuit can be evaluated over many rows at once. -/
inductive Expr (α : Type u) where
  | proj (a : α)
  | const (z : ℤ)
  | sub (left right : Expr α)
  | mul (left right : Expr α)

/-- Ordinary integer evaluation of the recovered expression. -/
def Expr.eval {α : Type u} : Expr α → (α → ℕ) → ℤ
  | .proj a, v => v a
  | .const z, _ => z
  | .sub e f, v => e.eval v - f.eval v
  | .mul e f, v => e.eval v * f.eval v

/-- Every semantic `IsPoly` derivation has a finite expression tree.  This
statement lives in `Prop`: Lean quite properly forbids eliminating a proof
directly into data, and the next definition uses classical choice only after
the existence theorem has been established. -/
theorem Expr.exists_ofIsPoly {α : Type u} {f : (α → ℕ) → ℤ}
    (hf : IsPoly f) : ∃ e : Expr α, ∀ v, e.eval v = f v := by
  induction hf with
  | proj a => exact ⟨.proj a, fun _ => rfl⟩
  | const z => exact ⟨.const z, fun _ => rfl⟩
  | sub _ _ ihf ihg =>
      rcases ihf with ⟨e, he⟩
      rcases ihg with ⟨g, hg⟩
      exact ⟨.sub e g, fun v => by simp only [eval, he v, hg v]⟩
  | mul _ _ ihf ihg =>
      rcases ihf with ⟨e, he⟩
      rcases ihg with ⟨g, hg⟩
      exact ⟨.mul e g, fun v => by simp only [eval, he v, hg v]⟩

/-- A fixed expression representing a bundled Mathlib polynomial. -/
noncomputable def Expr.ofPoly {α : Type u} (p : Poly α) : Expr α :=
  Classical.choose (Expr.exists_ofIsPoly p.isPoly)

theorem Expr.eval_ofPoly {α : Type u} (p : Poly α) (v : α → ℕ) :
    (Expr.ofPoly p).eval v = p v :=
  Classical.choose_spec (Expr.exists_ofIsPoly p.isPoly) v

/-! ## Positive/negative natural evaluation -/

/-- Natural positive and negative parts of every intermediate expression.
The subtraction and multiplication clauses are the usual identities

`(a-b)-(c-d) = (a+d)-(b+c)` and
`(a-b)(c-d) = (ac+bd)-(ad+bc)`.
-/
def Expr.evalPN {α : Type u} : Expr α → (α → ℕ) → ℕ × ℕ
  | .proj a, v => (v a, 0)
  | .const z, _ => (z.toNat, (-z).toNat)
  | .sub e f, v =>
      let ep := e.evalPN v
      let fp := f.evalPN v
      (ep.1 + fp.2, ep.2 + fp.1)
  | .mul e f, v =>
      let ep := e.evalPN v
      let fp := f.evalPN v
      (ep.1 * fp.1 + ep.2 * fp.2,
        ep.1 * fp.2 + ep.2 * fp.1)

theorem int_toNat_sub_neg_toNat (z : ℤ) :
    (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by
  cases z <;> simp [Int.negSucc_eq]

/-- The natural pair denotes exactly the original integer expression. -/
theorem Expr.eval_eq_evalPN_sub {α : Type u} (e : Expr α) (v : α → ℕ) :
    e.eval v = (e.evalPN v).1 - (e.evalPN v).2 := by
  induction e with
  | proj a => simp [eval, evalPN]
  | const z => simpa [eval, evalPN] using (int_toNat_sub_neg_toNat z).symm
  | sub e f ihe ihf =>
      simp only [eval, evalPN]
      rw [ihe, ihf]
      push_cast
      ring
  | mul e f ihe ihf =>
      simp only [eval, evalPN]
      rw [ihe, ihf]
      push_cast
      ring

/-- Equality to zero is therefore equality of the two natural columns. -/
theorem Expr.eval_eq_zero_iff {α : Type u} (e : Expr α) (v : α → ℕ) :
    e.eval v = 0 ↔ (e.evalPN v).1 = (e.evalPN v).2 := by
  rw [Expr.eval_eq_evalPN_sub]
  rw [Int.sub_eq_zero, Int.ofNat_inj]

/-! ## A uniform elementary size bound

Besides the root value, a cipher circuit must hold every intermediate gate.
`circuitSize` deliberately overestimates all of them.  Summing this positive
quantity over the finitely many rows gives one spacing parameter that works
for the entire circuit.
-/

/-- A positive majorant for both natural values at every node below `e`. -/
def Expr.circuitSize {α : Type u} : Expr α → (α → ℕ) → ℕ
  | .proj a, v => v a + 1
  | .const z, _ => z.toNat + (-z).toNat + 1
  | .sub e f, v =>
      let ep := e.evalPN v
      let fp := f.evalPN v
      e.circuitSize v + f.circuitSize v +
        (ep.1 + fp.2) + (ep.2 + fp.1) + 1
  | .mul e f, v =>
      let ep := e.evalPN v
      let fp := f.evalPN v
      e.circuitSize v + f.circuitSize v +
        (ep.1 * fp.1 + ep.2 * fp.2) +
        (ep.1 * fp.2 + ep.2 * fp.1) + 1

theorem Expr.evalPN_fst_lt_circuitSize {α : Type u}
    (e : Expr α) (v : α → ℕ) : (e.evalPN v).1 < e.circuitSize v := by
  cases e with
  | proj a => simp [evalPN, circuitSize]
  | const z =>
      simp only [evalPN, circuitSize]
      omega
  | sub e f =>
      simp only [evalPN, circuitSize]
      omega
  | mul e f =>
      simp only [evalPN, circuitSize]
      omega

theorem Expr.evalPN_snd_lt_circuitSize {α : Type u}
    (e : Expr α) (v : α → ℕ) : (e.evalPN v).2 < e.circuitSize v := by
  cases e with
  | proj a => simp [evalPN, circuitSize]
  | const z =>
      simp only [evalPN, circuitSize]
      omega
  | sub e f =>
      simp only [evalPN, circuitSize]
      omega
  | mul e f =>
      simp only [evalPN, circuitSize]
      omega

/-- Every recursive subcircuit also fits under the root's majorant. -/
theorem Expr.sub_circuitSize_lt_left {α : Type u} {e f : Expr α}
    (v : α → ℕ) :
    e.circuitSize v < (Expr.sub e f).circuitSize v := by
  simp [circuitSize]
  omega

theorem Expr.sub_circuitSize_lt_right {α : Type u} {e f : Expr α}
    (v : α → ℕ) :
    f.circuitSize v < (Expr.sub e f).circuitSize v := by
  simp [circuitSize]
  omega

theorem Expr.mul_circuitSize_lt_left {α : Type u} {e f : Expr α}
    (v : α → ℕ) :
    e.circuitSize v < (Expr.mul e f).circuitSize v := by
  simp [circuitSize]
  omega

theorem Expr.mul_circuitSize_lt_right {α : Type u} {e f : Expr α}
    (v : α → ℕ) :
    f.circuitSize v < (Expr.mul e f).circuitSize v := by
  simp [circuitSize]
  omega

/-- A single parameter, larger than the row count and all circuit values. -/
def spacing (len : ℕ) {α : Type u} (e : Expr α)
    (rows : ℕ → α → ℕ) : ℕ :=
  len + 2 + ∑ i ∈ Finset.range len, e.circuitSize (rows i)

theorem spacing_rows {α : Type u} (len : ℕ) (e : Expr α)
    (rows : ℕ → α → ℕ) : len + 1 < spacing len e rows := by
  unfold spacing
  omega

theorem circuitSize_lt_spacing {α : Type u} {len i : ℕ} (e : Expr α)
    (rows : ℕ → α → ℕ) (hi : i < len) :
    e.circuitSize (rows i) < spacing len e rows := by
  have hle : e.circuitSize (rows i) ≤
      ∑ j ∈ Finset.range len, e.circuitSize (rows j) := by
    exact Finset.single_le_sum
      (fun j _hj => Nat.zero_le (e.circuitSize (rows j)))
      (Finset.mem_range.mpr hi)
  unfold spacing
  omega

theorem evalPN_lt_two_pow_spacing {α : Type u} {len i : ℕ} (e : Expr α)
    (rows : ℕ → α → ℕ) (hi : i < len) :
    (e.evalPN (rows i)).1 < 2 ^ spacing len e rows ∧
      (e.evalPN (rows i)).2 < 2 ^ spacing len e rows := by
  have hq : e.circuitSize (rows i) < spacing len e rows :=
    circuitSize_lt_spacing e rows hi
  have hpow : spacing len e rows < 2 ^ spacing len e rows :=
    Nat.lt_pow_self (by omega)
  exact
    ⟨(e.evalPN_fst_lt_circuitSize _).trans (hq.trans hpow),
      (e.evalPN_snd_lt_circuitSize _).trans (hq.trans hpow)⟩

end PolynomialCipher

end PAListCoding
