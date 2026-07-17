import PAListCoding.BoundedDioph
import PAListCoding.CipherCircuit

/-!
# Semantic certificate for variable bounded universals

This file assembles the sparse polynomial circuit into the exact semantic
certificate needed for Matiyasevich's bounded-universal theorem.  The params
valuation has one distinguished coordinate containing the row count.  For a
polynomial with coordinates `Option α ⊕ β`, its columns have three meanings:

* `inl none` is the row-index column `0,1,...,len-1`;
* `inl (some a)` is the constant column containing params parameter `a`;
* `inr b` is an arbitrary column of existential witnesses.

The theorem at the end proves that one finite cipher circuit exists exactly
when every row below the variable bound has a polynomial witness.  No
Diophantine-closure claim is made here; the companion compiler establishes
that the displayed finite certificate is itself Diophantine.
-/

namespace PAListCoding

namespace BoundedCipher

open PolynomialCipher CipherCircuit SparseCipher

universe u

/-- Coordinates of the polynomial defining one instance of the relation. -/
abbrev Coordinate (α β : Type u) := Option α ⊕ β

/-- The three kinds of source columns used by the simultaneous circuit. -/
def Atom {α β : Type u} (params : Option α → ℕ) :
    AtomRelation (Coordinate α β)
  | .inl none, len, q, code => IndexCode len q code
  | .inl (some a), len, q, code =>
      ConstCode len q (params (some a)) code
  | .inr _, len, q, code => Code len q code

/-- `CipherCircuit` takes operands first and output last, whereas the Rocq
`MulCodes` convention takes output first. -/
def MulRel (len q left right output : ℕ) : Prop :=
  MulCodes len q output left right

theorem mulRel_pointwise : HasPointwiseMulSpec MulRel := by
  intro len q ca cb cc a b c ha hb hc
  exact mul_spec hc ha hb

theorem mulRel_canonical_complete : CanonicalMulComplete MulRel := by
  intro len q a b ha hb hc
  exact (mul_spec hc ha hb).mpr fun _i _hi => rfl

/-- The finite certificate attached to a bundled integer polynomial. -/
def Certificate {α β : Type u} (p : Poly (Coordinate α β))
    (params : Option α → ℕ) : Prop :=
  let e := Expr.ofPoly p
  ∃ q columns positive negative,
    Circuit (Atom params) MulRel e (params none) q columns positive negative ∧
      positive = negative

/-! ## Canonical rows and source-column correctness -/

/-- Extend params parameters with a row index and a row of private witnesses. -/
def rowValue {α β : Type u} (params : Option α → ℕ)
    (witnesses : ℕ → β → ℕ) (i : ℕ) : Coordinate α β → ℕ
  | .inl none => i
  | .inl (some a) => params (some a)
  | .inr b => witnesses i b

/-- Every atom relation in a completed certificate denotes the corresponding
decoded row values.  Private columns are decoded canonically with `entry`, so
no global choice of their representing sequences is needed. -/
theorem atom_sound {α β : Type u} {params : Option α → ℕ}
    {len q : ℕ} {columns : Coordinate α β → ℕ} :
    ∀ x, Atom params x len q (columns x) →
      IsCipher len q
        (fun i =>
          match x with
          | .inl none => i
          | .inl (some a) => params (some a)
          | .inr b => entry q (columns (.inr b)) i)
        (columns x) := by
  intro x hx
  rcases x with (_ | a) | b
  · exact hx
  · exact hx
  · rcases hx with ⟨f, hf⟩
    apply isCipher_congr hf
    intro i hi
    exact (entry_isCipher hf hi).symm

/-! ## Exact semantic equivalence -/

/-- One finite cipher circuit exists exactly when every row below the params
bound admits values for the polynomial's existential coordinates. -/
theorem certificate_iff_bounded_witnesses {α β : Type u}
    (p : Poly (Coordinate α β)) (params : Option α → ℕ) :
    Certificate p params ↔
      ∀ i, i < params none →
        ∃ witnesses : β → ℕ,
          p (Sum.elim (BoundedDioph.consValue i (params ∘ some)) witnesses) = 0 := by
  let e := Expr.ofPoly p
  constructor
  · rintro ⟨q, columns, positive, negative, hcircuit, heq⟩
    let rows : ℕ → Coordinate α β → ℕ := fun i x =>
      match x with
      | .inl none => i
      | .inl (some a) => params (some a)
      | .inr b => entry q (columns (.inr b)) i
    have hatom : ∀ x, Atom params x (params none) q (columns x) →
        IsCipher (params none) q (fun i => rows i x) (columns x) := by
      intro x hx
      simpa only [rows] using
        (atom_sound (params := params) (columns := columns) x hx)
    obtain ⟨hpositive, hnegative⟩ :=
      Circuit.sound mulRel_pointwise e hatom hcircuit
    have hpn : ∀ i, i < params none →
        (e.evalPN (rows i)).1 = (e.evalPN (rows i)).2 := by
      rw [heq] at hpositive
      exact isCipher_inj hpositive hnegative
    intro i hi
    let witnesses : β → ℕ := fun b => entry q (columns (.inr b)) i
    refine ⟨witnesses, ?_⟩
    have heZero : e.eval (rows i) = 0 :=
      (Expr.eval_eq_zero_iff e (rows i)).mpr (hpn i hi)
    have hpZero : p (rows i) = 0 := by
      rw [← Expr.eval_ofPoly p (rows i)]
      exact heZero
    have hrows : rows i =
        Sum.elim (BoundedDioph.consValue i (params ∘ some)) witnesses := by
      funext x
      rcases x with (_ | a) | b <;> rfl
    simpa only [hrows] using hpZero
  · intro hall
    let witnesses : ℕ → β → ℕ := fun i =>
      if hi : i < params none then Classical.choose (hall i hi)
      else fun _ => 0
    have hwitnesses : ∀ i, i < params none →
        p (Sum.elim (BoundedDioph.consValue i (params ∘ some))
          (witnesses i)) = 0 := by
      intro i hi
      simpa only [witnesses, dif_pos hi] using
        Classical.choose_spec (hall i hi)
    let rows : ℕ → Coordinate α β → ℕ := rowValue params witnesses
    have hrowEq : ∀ i,
        rows i = Sum.elim (BoundedDioph.consValue i (params ∘ some))
          (witnesses i) := by
      intro i
      funext x
      rcases x with (_ | a) | b <;> rfl
    let q := PolynomialCipher.spacing (params none) e rows
    let columns : Coordinate α β → ℕ := fun x =>
      encode (params none) q fun i => rows i x
    let positive := encode (params none) q fun i => (e.evalPN (rows i)).1
    let negative := encode (params none) q fun i => (e.evalPN (rows i)).2
    have hlen : params none + 1 < q := by
      exact PolynomialCipher.spacing_rows (params none) e rows
    have hcircuitBound : ∀ i, i < params none →
        e.circuitSize (rows i) < 2 ^ q := by
      intro i hi
      have hsize : e.circuitSize (rows i) < q := by
        exact PolynomialCipher.circuitSize_lt_spacing e rows hi
      exact hsize.trans (Nat.lt_pow_self (by omega))
    have hatom : ∀ x,
        (∀ i, i < params none → rows i x < 2 ^ q) →
        Atom params x (params none) q
          (encode (params none) q fun i => rows i x) := by
      intro x hx
      rcases x with (_ | a) | b
      · apply indexCode_iff.mpr
        refine ⟨hlen, ?_⟩
        unfold rows rowValue
        rfl
      · unfold Atom ConstCode
        apply isCipher_encode hlen
        intro i hi
        simpa only [rows, rowValue] using hx i hi
      · exact code_of_isCipher (isCipher_encode hlen hx)
    have hcircuit : Circuit (Atom params) MulRel e (params none) q columns
        positive negative := by
      simpa only [columns, positive, negative] using
        Circuit.complete mulRel_canonical_complete e hlen hcircuitBound hatom
    refine ⟨q, columns, positive, negative, hcircuit, ?_⟩
    unfold positive negative encode
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < params none := Finset.mem_range.mp hi
    have hpZero : p (rows i) = 0 := by
      rw [hrowEq i]
      exact hwitnesses i hi'
    have heZero : e.eval (rows i) = 0 := by
      rw [Expr.eval_ofPoly]
      exact hpZero
    have hpneq := (Expr.eval_eq_zero_iff e (rows i)).mp heZero
    change (e.evalPN (rows i)).1 * radix q ^ place i =
      (e.evalPN (rows i)).2 * radix q ^ place i
    rw [hpneq]

end BoundedCipher

end PAListCoding
