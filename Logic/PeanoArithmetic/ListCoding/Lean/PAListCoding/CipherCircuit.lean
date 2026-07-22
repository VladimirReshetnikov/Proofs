import PAListCoding.PolynomialCipher
import PAListCoding.SparseCipher

/-!
# Sparse-cipher evaluation of fixed polynomial circuits

This module connects the finite expression trees from `PolynomialCipher` to
the semantic sparse ciphers.  Multiplication is parameterized by a relation
with the expected pointwise specification.  That separation lets the circuit
correctness proof depend only on the public contract of the nontrivial binary
mask construction, rather than on its implementation.
-/

namespace PAListCoding

namespace CipherCircuit

open PolynomialCipher SparseCipher

universe u

/-- Two multiplication certificates are interchangeable for the circuit
compiler when they have this behavior on three well-formed ciphers. -/
def HasPointwiseMulSpec
    (MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {len q ca cb cc : ℕ} {a b c : ℕ → ℕ},
    IsCipher len q a ca →
    IsCipher len q b cb →
    IsCipher len q c cc →
    (MulRel len q ca cb cc ↔ ∀ i, i < len → c i = a i * b i)

/-- An atomic relation explains how one input column is represented.  In the
bounded-universal application its three cases are the row-index column, a
constant public parameter column, and an arbitrary existential-witness
column. -/
abbrev AtomRelation (γ : Type u) := γ → ℕ → ℕ → ℕ → Prop

/-- A fixed positive/negative circuit evaluated columnwise.  Every output is
also required to be a well-formed cipher; these apparently redundant `Code`
clauses are what rule out spurious arithmetic equalities with carries. -/
def Circuit {γ : Type u} (atom : AtomRelation γ)
    (MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) :
    Expr γ → ℕ → ℕ → (γ → ℕ) → ℕ → ℕ → Prop
  | .proj x, len, q, columns, positive, negative =>
      atom x len q (columns x) ∧
      positive = columns x ∧
      ConstCode len q 0 negative
  | .const z, len, q, _columns, positive, negative =>
      ConstCode len q z.toNat positive ∧
      ConstCode len q (-z).toNat negative
  | .sub e f, len, q, columns, positive, negative =>
      ∃ ep en fp fn,
        Circuit atom MulRel e len q columns ep en ∧
        Circuit atom MulRel f len q columns fp fn ∧
        Code len q positive ∧ Code len q negative ∧
        positive = ep + fn ∧ negative = en + fp
  | .mul e f, len, q, columns, positive, negative =>
      ∃ ep en fp fn pp nn pn np,
        Circuit atom MulRel e len q columns ep en ∧
        Circuit atom MulRel f len q columns fp fn ∧
        Code len q pp ∧ Code len q nn ∧
        Code len q pn ∧ Code len q np ∧
        MulRel len q ep fp pp ∧ MulRel len q en fn nn ∧
        MulRel len q ep fn pn ∧ MulRel len q en fp np ∧
        Code len q positive ∧ Code len q negative ∧
        positive = pp + nn ∧ negative = pn + np

/-! ## Small preservation lemmas -/

/-- A cipher may be transported across pointwise equality on its represented
prefix.  Values beyond `len` are intentionally irrelevant. -/
theorem isCipher_congr {len q code : ℕ} {f g : ℕ → ℕ}
    (hf : IsCipher len q f code)
    (hfg : ∀ i, i < len → f i = g i) :
    IsCipher len q g code := by
  rcases hf with ⟨hlen, hbound, hcode⟩
  refine ⟨hlen, fun i hi => ?_, ?_⟩
  · simpa [← hfg i hi] using hbound i hi
  · rw [hcode]
    unfold encode
    apply Finset.sum_congr rfl
    intro i hi
    rw [hfg i (Finset.mem_range.mp hi)]

/-- The canonical encoding is a cipher as soon as its entries satisfy the
standard bound. -/
theorem isCipher_encode {len q : ℕ} {f : ℕ → ℕ}
    (hlen : len + 1 < q) (hf : ∀ i, i < len → f i < 2 ^ q) :
    IsCipher len q f (encode len q f) :=
  ⟨hlen, hf, rfl⟩

theorem code_of_isCipher {len q code : ℕ} {f : ℕ → ℕ}
    (hf : IsCipher len q f code) : Code len q code :=
  ⟨f, hf⟩

/-! ## Soundness -/

/-- If each atom code denotes the requested row values, every circuit output
denotes the positive and negative evaluations of the expression. -/
theorem Circuit.sound {γ : Type u} {atom : AtomRelation γ}
    {MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (hmul : HasPointwiseMulSpec MulRel) :
    ∀ (e : Expr γ) {len q : ℕ} {columns : γ → ℕ}
      {positive negative : ℕ} {rows : ℕ → γ → ℕ},
      (∀ x, atom x len q (columns x) →
        IsCipher len q (fun i => rows i x) (columns x)) →
      Circuit atom MulRel e len q columns positive negative →
      IsCipher len q (fun i => (e.evalPN (rows i)).1) positive ∧
        IsCipher len q (fun i => (e.evalPN (rows i)).2) negative := by
  intro e
  induction e with
  | proj x =>
      intro len q columns positive negative rows hatom hcircuit
      rcases hcircuit with ⟨hx, rfl, hzero⟩
      exact ⟨hatom x hx, hzero⟩
  | const z =>
      intro len q columns positive negative rows _hatom hcircuit
      simpa only [Circuit, Expr.evalPN, ConstCode] using hcircuit
  | sub e f ihe ihf =>
      intro len q columns positive negative rows hatom hcircuit
      rcases hcircuit with
        ⟨ep, en, fp, fn, he, hf, hpositive, hnegative, hposEq, hnegEq⟩
      obtain ⟨hep, hen⟩ := ihe hatom he
      obtain ⟨hfp, hfn⟩ := ihf hatom hf
      rcases hpositive with ⟨positiveSeq, hpositiveSeq⟩
      rcases hnegative with ⟨negativeSeq, hnegativeSeq⟩
      have hposPoint : ∀ i, i < len →
          positiveSeq i =
            (e.evalPN (rows i)).1 + (f.evalPN (rows i)).2 :=
        (add_spec hpositiveSeq hep hfn).mp hposEq
      have hnegPoint : ∀ i, i < len →
          negativeSeq i =
            (e.evalPN (rows i)).2 + (f.evalPN (rows i)).1 :=
        (add_spec hnegativeSeq hen hfp).mp hnegEq
      exact
        ⟨isCipher_congr hpositiveSeq (by
            intro i hi
            simpa only [Expr.evalPN] using hposPoint i hi),
          isCipher_congr hnegativeSeq (by
            intro i hi
            simpa only [Expr.evalPN] using hnegPoint i hi)⟩
  | mul e f ihe ihf =>
      intro len q columns positive negative rows hatom hcircuit
      rcases hcircuit with
        ⟨ep, en, fp, fn, pp, nn, pn, np, he, hf,
          hppCode, hnnCode, hpnCode, hnpCode,
          hppMul, hnnMul, hpnMul, hnpMul,
          hpositiveCode, hnegativeCode, hposEq, hnegEq⟩
      obtain ⟨hep, hen⟩ := ihe hatom he
      obtain ⟨hfp, hfn⟩ := ihf hatom hf
      rcases hppCode with ⟨ppSeq, hppSeq⟩
      rcases hnnCode with ⟨nnSeq, hnnSeq⟩
      rcases hpnCode with ⟨pnSeq, hpnSeq⟩
      rcases hnpCode with ⟨npSeq, hnpSeq⟩
      have hppPoint := (hmul hep hfp hppSeq).mp hppMul
      have hnnPoint := (hmul hen hfn hnnSeq).mp hnnMul
      have hpnPoint := (hmul hep hfn hpnSeq).mp hpnMul
      have hnpPoint := (hmul hen hfp hnpSeq).mp hnpMul
      have hppExact : IsCipher len q
          (fun i => (e.evalPN (rows i)).1 * (f.evalPN (rows i)).1) pp :=
        isCipher_congr hppSeq hppPoint
      have hnnExact : IsCipher len q
          (fun i => (e.evalPN (rows i)).2 * (f.evalPN (rows i)).2) nn :=
        isCipher_congr hnnSeq hnnPoint
      have hpnExact : IsCipher len q
          (fun i => (e.evalPN (rows i)).1 * (f.evalPN (rows i)).2) pn :=
        isCipher_congr hpnSeq hpnPoint
      have hnpExact : IsCipher len q
          (fun i => (e.evalPN (rows i)).2 * (f.evalPN (rows i)).1) np :=
        isCipher_congr hnpSeq hnpPoint
      rcases hpositiveCode with ⟨positiveSeq, hpositiveSeq⟩
      rcases hnegativeCode with ⟨negativeSeq, hnegativeSeq⟩
      have hposPoint := (add_spec hpositiveSeq hppExact hnnExact).mp hposEq
      have hnegPoint := (add_spec hnegativeSeq hpnExact hnpExact).mp hnegEq
      exact
        ⟨isCipher_congr hpositiveSeq (by
            intro i hi
            simpa only [Expr.evalPN] using hposPoint i hi),
          isCipher_congr hnegativeSeq (by
            intro i hi
            simpa only [Expr.evalPN] using hnegPoint i hi)⟩

/-! ## Completeness -/

/-- A semantic multiplication specification supplies a certificate for the
three canonical ciphers whenever the target pointwise products fit. -/
def CanonicalMulComplete
    (MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {len q : ℕ} {a b : ℕ → ℕ},
    IsCipher len q a (encode len q a) →
    IsCipher len q b (encode len q b) →
    IsCipher len q (fun i => a i * b i)
      (encode len q fun i => a i * b i) →
    MulRel len q (encode len q a) (encode len q b)
      (encode len q fun i => a i * b i)

/-- Under one uniform circuit bound, canonical encodings satisfy the entire
fixed circuit.  The atom premise is deliberately conditional on a digit
bound, so unused existential coordinates need no global bound. -/
theorem Circuit.complete {γ : Type u} {atom : AtomRelation γ}
    {MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (hmul : CanonicalMulComplete MulRel) :
    ∀ (e : Expr γ) {len q : ℕ} {rows : ℕ → γ → ℕ},
      len + 1 < q →
      (∀ i, i < len → e.circuitSize (rows i) < 2 ^ q) →
      (∀ x, (∀ i, i < len → rows i x < 2 ^ q) →
        atom x len q (encode len q fun i => rows i x)) →
      Circuit atom MulRel e len q
        (fun x => encode len q fun i => rows i x)
        (encode len q fun i => (e.evalPN (rows i)).1)
        (encode len q fun i => (e.evalPN (rows i)).2) := by
  intro e
  induction e with
  | proj x =>
      intro len q rows hlen hbound hatom
      have hxBound : ∀ i, i < len → rows i x < 2 ^ q := by
        intro i hi
        exact (Expr.evalPN_fst_lt_circuitSize (.proj x) (rows i)).trans
          (hbound i hi)
      refine ⟨hatom x hxBound, rfl, ?_⟩
      exact isCipher_encode hlen (fun _i _hi => Nat.two_pow_pos q)
  | const z =>
      intro len q rows hlen hbound _hatom
      constructor
      · apply isCipher_encode hlen
        intro i hi
        exact (Expr.evalPN_fst_lt_circuitSize (.const z) (rows i)).trans
          (hbound i hi)
      · apply isCipher_encode hlen
        intro i hi
        exact (Expr.evalPN_snd_lt_circuitSize (.const z) (rows i)).trans
          (hbound i hi)
  | sub e f ihe ihf =>
      intro len q rows hlen hbound hatom
      have heBound : ∀ i, i < len → e.circuitSize (rows i) < 2 ^ q := by
        intro i hi
        exact (Expr.sub_circuitSize_lt_left (e := e) (f := f) (rows i)).trans
          (hbound i hi)
      have hfBound : ∀ i, i < len → f.circuitSize (rows i) < 2 ^ q := by
        intro i hi
        exact (Expr.sub_circuitSize_lt_right (e := e) (f := f) (rows i)).trans
          (hbound i hi)
      let ep := encode len q fun i => (e.evalPN (rows i)).1
      let en := encode len q fun i => (e.evalPN (rows i)).2
      let fp := encode len q fun i => (f.evalPN (rows i)).1
      let fn := encode len q fun i => (f.evalPN (rows i)).2
      refine ⟨ep, en, fp, fn, ihe hlen heBound hatom, ihf hlen hfBound hatom, ?_⟩
      have hpositive : IsCipher len q
          (fun i => ((Expr.sub e f).evalPN (rows i)).1)
          (encode len q fun i => ((Expr.sub e f).evalPN (rows i)).1) :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize (.sub e f) (rows i)).trans (hbound i hi)
      have hnegative : IsCipher len q
          (fun i => ((Expr.sub e f).evalPN (rows i)).2)
          (encode len q fun i => ((Expr.sub e f).evalPN (rows i)).2) :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize (.sub e f) (rows i)).trans (hbound i hi)
      have hep : IsCipher len q (fun i => (e.evalPN (rows i)).1) ep :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize e (rows i)).trans (heBound i hi)
      have hen : IsCipher len q (fun i => (e.evalPN (rows i)).2) en :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize e (rows i)).trans (heBound i hi)
      have hfp : IsCipher len q (fun i => (f.evalPN (rows i)).1) fp :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize f (rows i)).trans (hfBound i hi)
      have hfn : IsCipher len q (fun i => (f.evalPN (rows i)).2) fn :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize f (rows i)).trans (hfBound i hi)
      refine ⟨code_of_isCipher hpositive, code_of_isCipher hnegative, ?_, ?_⟩
      · exact (add_spec hpositive hep hfn).mpr fun _i _hi => rfl
      · exact (add_spec hnegative hen hfp).mpr fun _i _hi => rfl
  | mul e f ihe ihf =>
      intro len q rows hlen hbound hatom
      have heBound : ∀ i, i < len → e.circuitSize (rows i) < 2 ^ q := by
        intro i hi
        exact (Expr.mul_circuitSize_lt_left (e := e) (f := f) (rows i)).trans
          (hbound i hi)
      have hfBound : ∀ i, i < len → f.circuitSize (rows i) < 2 ^ q := by
        intro i hi
        exact (Expr.mul_circuitSize_lt_right (e := e) (f := f) (rows i)).trans
          (hbound i hi)
      let ep := encode len q fun i => (e.evalPN (rows i)).1
      let en := encode len q fun i => (e.evalPN (rows i)).2
      let fp := encode len q fun i => (f.evalPN (rows i)).1
      let fn := encode len q fun i => (f.evalPN (rows i)).2
      let pp := encode len q fun i =>
        (e.evalPN (rows i)).1 * (f.evalPN (rows i)).1
      let nn := encode len q fun i =>
        (e.evalPN (rows i)).2 * (f.evalPN (rows i)).2
      let pn := encode len q fun i =>
        (e.evalPN (rows i)).1 * (f.evalPN (rows i)).2
      let np := encode len q fun i =>
        (e.evalPN (rows i)).2 * (f.evalPN (rows i)).1
      refine ⟨ep, en, fp, fn, pp, nn, pn, np,
        ihe hlen heBound hatom, ihf hlen hfBound hatom, ?_⟩
      have hep : IsCipher len q (fun i => (e.evalPN (rows i)).1) ep :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize e (rows i)).trans (heBound i hi)
      have hen : IsCipher len q (fun i => (e.evalPN (rows i)).2) en :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize e (rows i)).trans (heBound i hi)
      have hfp : IsCipher len q (fun i => (f.evalPN (rows i)).1) fp :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize f (rows i)).trans (hfBound i hi)
      have hfn : IsCipher len q (fun i => (f.evalPN (rows i)).2) fn :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize f (rows i)).trans (hfBound i hi)
      have hpp : IsCipher len q
          (fun i => (e.evalPN (rows i)).1 * (f.evalPN (rows i)).1) pp :=
        isCipher_encode hlen fun i hi => by
          have hroot :=
            (Expr.evalPN_fst_lt_circuitSize (.mul e f) (rows i)).trans
              (hbound i hi)
          simp only [Expr.evalPN] at hroot
          omega
      have hnn : IsCipher len q
          (fun i => (e.evalPN (rows i)).2 * (f.evalPN (rows i)).2) nn := by
        apply isCipher_encode hlen
        intro i hi
        have hroot := hbound i hi
        simp only [Expr.circuitSize] at hroot
        omega
      have hpn : IsCipher len q
          (fun i => (e.evalPN (rows i)).1 * (f.evalPN (rows i)).2) pn := by
        apply isCipher_encode hlen
        intro i hi
        have hroot := hbound i hi
        simp only [Expr.circuitSize] at hroot
        omega
      have hnp : IsCipher len q
          (fun i => (e.evalPN (rows i)).2 * (f.evalPN (rows i)).1) np := by
        apply isCipher_encode hlen
        intro i hi
        have hroot := hbound i hi
        simp only [Expr.circuitSize] at hroot
        omega
      have hpositive : IsCipher len q
          (fun i => ((Expr.mul e f).evalPN (rows i)).1)
          (encode len q fun i => ((Expr.mul e f).evalPN (rows i)).1) :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_fst_lt_circuitSize (.mul e f) (rows i)).trans (hbound i hi)
      have hnegative : IsCipher len q
          (fun i => ((Expr.mul e f).evalPN (rows i)).2)
          (encode len q fun i => ((Expr.mul e f).evalPN (rows i)).2) :=
        isCipher_encode hlen fun i hi =>
          (Expr.evalPN_snd_lt_circuitSize (.mul e f) (rows i)).trans (hbound i hi)
      refine ⟨code_of_isCipher hpp, code_of_isCipher hnn,
        code_of_isCipher hpn, code_of_isCipher hnp,
        hmul hep hfp hpp, hmul hen hfn hnn,
        hmul hep hfn hpn, hmul hen hfp hnp,
        code_of_isCipher hpositive, code_of_isCipher hnegative, ?_, ?_⟩
      · exact (add_spec hpositive hpp hnn).mpr fun _i _hi => rfl
      · exact (add_spec hnegative hpn hnp).mpr fun _i _hi => rfl

end CipherCircuit

end PAListCoding
