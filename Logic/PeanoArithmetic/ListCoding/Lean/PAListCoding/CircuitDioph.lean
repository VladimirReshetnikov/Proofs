import PAListCoding.CipherCircuit

/-!
# Diophantine closure for fixed sparse-cipher circuits

`CipherCircuit.Circuit` is a finite syntax-directed certificate: only the
number of represented rows is variable.  This file proves that every fixed
circuit is Diophantine once its three primitive relations are stable under
substitution of Diophantine functions:

* atom columns;
* the predicate saying that an integer is some well-formed cipher; and
* pointwise multiplication certificates.

Constants are kept as a fourth primitive because their eventual arithmetic
certificate is substantially stronger than merely fixing the represented
value in the metatheory.  Addition gates need no primitive hypothesis: their
code equation is ordinary natural addition.

The recursive proof allocates one finite tuple of fresh wire values at each
subtraction or multiplication node and eliminates that tuple with
`Dioph.ex_dioph`.  Thus no variable-length family of existential variables is
introduced here; all witness types are fixed by the expression tree.
-/

namespace PAListCoding

namespace CircuitDioph

open PolynomialCipher CipherCircuit SparseCipher
open scoped Dioph

universe u

/-! ## Substitution-stable primitive relations -/

/-- Closure contract for a ternary relation under arbitrary Diophantine
functions.  The intended arguments are `(length, spacing, code)`. -/
def TernarySubstitutionClosed (R : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {ι : Type} {a b c : (ι → ℕ) → ℕ},
    Dioph.DiophFn a → Dioph.DiophFn b → Dioph.DiophFn c →
      Dioph {v : ι → ℕ | R (a v) (b v) (c v)}

/-- Closure contract for the five arguments of a multiplication
certificate `(length, spacing, left, right, output)`. -/
def QuinarySubstitutionClosed
    (R : ℕ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {ι : Type} {a b c d e : (ι → ℕ) → ℕ},
    Dioph.DiophFn a → Dioph.DiophFn b → Dioph.DiophFn c →
    Dioph.DiophFn d → Dioph.DiophFn e →
      Dioph {v : ι → ℕ | R (a v) (b v) (c v) (d v) (e v)}

/-- A readable conjunction wrapper around Mathlib's set intersection
closure theorem. -/
theorem and_dioph {ι : Type} {P Q : (ι → ℕ) → Prop}
    (hP : Dioph {v | P v}) (hQ : Dioph {v | Q v}) :
    Dioph {v | P v ∧ Q v} := by
  apply Dioph.ext (Dioph.inter hP hQ)
  intro v
  rfl

/-- The equation `x = y + z` is Diophantine after substituting arbitrary
Diophantine functions. -/
theorem eq_add_dioph {ι : Type} {x y z : (ι → ℕ) → ℕ}
    (hx : Dioph.DiophFn x) (hy : Dioph.DiophFn y)
    (hz : Dioph.DiophFn z) :
    Dioph {v : ι → ℕ | x v = y v + z v} :=
  Dioph.eq_dioph hx (Dioph.add_dioph hy hz)

/-! ## Fresh finite wire tuples -/

private abbrev SubWire := Fin 4
private abbrev MulWire := Fin 8

private def subValues (ep en fp fn : ℕ) : SubWire → ℕ :=
  ![ep, en, fp, fn]

private def mulValues (ep en fp fn pp nn pn np : ℕ) : MulWire → ℕ :=
  ![ep, en, fp, fn, pp, nn, pn, np]

/-! ## The compiler theorem -/

/-- Every fixed cipher circuit is Diophantine under substitution-stable
primitive certificates.  The statement is deliberately fully compositional:
all public circuit inputs may themselves be arbitrary Diophantine functions
of a surrounding valuation. -/
theorem circuit_dioph
    {γ : Type u} {atom : AtomRelation γ}
    {MulRel : ℕ → ℕ → ℕ → ℕ → ℕ → Prop}
    (hatom : ∀ x, TernarySubstitutionClosed (atom x))
    (hcode : TernarySubstitutionClosed Code)
    (hconst : ∀ k, TernarySubstitutionClosed
      (fun len q code ↦ ConstCode len q k code))
    (hmul : QuinarySubstitutionClosed MulRel) :
    ∀ (e : Expr γ) {ι : Type}
      {lenFn qFn positiveFn negativeFn : (ι → ℕ) → ℕ}
      {columnFn : γ → (ι → ℕ) → ℕ},
      Dioph.DiophFn lenFn → Dioph.DiophFn qFn →
      (∀ x, Dioph.DiophFn (columnFn x)) →
      Dioph.DiophFn positiveFn → Dioph.DiophFn negativeFn →
      Dioph {v : ι → ℕ |
        Circuit atom MulRel e (lenFn v) (qFn v)
          (fun x ↦ columnFn x v) (positiveFn v) (negativeFn v)} := by
  intro e
  induction e with
  | proj x =>
      intro ι lenFn qFn positiveFn negativeFn columnFn
        dlen dq dcolumn dpositive dnegative
      have hAtom := hatom x dlen dq (dcolumn x)
      have hPositive : Dioph {v : ι → ℕ | positiveFn v = columnFn x v} :=
        Dioph.eq_dioph dpositive (dcolumn x)
      have hNegative := hconst 0 dlen dq dnegative
      simpa only [Circuit] using
        and_dioph hAtom (and_dioph hPositive hNegative)
  | const z =>
      intro ι lenFn qFn positiveFn negativeFn columnFn
        dlen dq _dcolumn dpositive dnegative
      simpa only [Circuit] using
        and_dioph (hconst z.toNat dlen dq dpositive)
          (hconst (-z).toNat dlen dq dnegative)
  | sub e f ihe ihf =>
      intro ι lenFn qFn positiveFn negativeFn columnFn
        dlen dq dcolumn dpositive dnegative
      -- The four new coordinates are precisely the positive and negative
      -- output wires of the two child circuits.  Every public input is
      -- pulled back along `Sum.inl`, while a wire is an ordinary projection
      -- from the right summand.
      have dlen' : Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => lenFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dlen
      have dq' : Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => qFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dq
      have dcolumn' : ∀ x, Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => columnFn x (v ∘ Sum.inl)) :=
        fun x => Dioph.reindex_diophFn Sum.inl (dcolumn x)
      have dpositive' : Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => positiveFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dpositive
      have dnegative' : Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => negativeFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dnegative
      have dwire (i : SubWire) : Dioph.DiophFn
          (fun v : (ι ⊕ SubWire) → ℕ => v (Sum.inr i)) :=
        Dioph.proj_dioph (Sum.inr i)
      have de := ihe dlen' dq' dcolumn' (dwire 0) (dwire 1)
      have df := ihf dlen' dq' dcolumn' (dwire 2) (dwire 3)
      have dbody : Dioph {v : (ι ⊕ SubWire) → ℕ |
          Circuit atom MulRel e (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (fun x => columnFn x (v ∘ Sum.inl))
              (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
          Circuit atom MulRel f (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (fun x => columnFn x (v ∘ Sum.inl))
              (v (Sum.inr 2)) (v (Sum.inr 3)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (positiveFn (v ∘ Sum.inl)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (negativeFn (v ∘ Sum.inl)) ∧
          positiveFn (v ∘ Sum.inl) = v (Sum.inr 0) + v (Sum.inr 3) ∧
          negativeFn (v ∘ Sum.inl) = v (Sum.inr 1) + v (Sum.inr 2)} :=
        and_dioph de <| and_dioph df <|
          and_dioph (hcode dlen' dq' dpositive') <|
          and_dioph (hcode dlen' dq' dnegative') <|
          and_dioph (eq_add_dioph dpositive' (dwire 0) (dwire 3))
            (eq_add_dioph dnegative' (dwire 1) (dwire 2))
      apply Dioph.ext (Dioph.ex_dioph dbody)
      intro v
      simp only [Set.mem_setOf_eq, Circuit, Sum.elim_inr]
      constructor
      · rintro ⟨w, he, hf, hp, hn, hpos, hneg⟩
        exact ⟨w 0, w 1, w 2, w 3, he, hf, hp, hn, hpos, hneg⟩
      · rintro ⟨ep, en, fp, fn, he, hf, hp, hn, hpos, hneg⟩
        exact ⟨subValues ep en fp fn, by
          simpa [subValues] using
            (show
              Circuit atom MulRel e (lenFn v) (qFn v)
                  (fun x => columnFn x v) ep en ∧
              Circuit atom MulRel f (lenFn v) (qFn v)
                  (fun x => columnFn x v) fp fn ∧
              Code (lenFn v) (qFn v) (positiveFn v) ∧
              Code (lenFn v) (qFn v) (negativeFn v) ∧
              positiveFn v = ep + fn ∧ negativeFn v = en + fp
              from ⟨he, hf, hp, hn, hpos, hneg⟩)⟩
  | mul e f ihe ihf =>
      intro ι lenFn qFn positiveFn negativeFn columnFn
        dlen dq dcolumn dpositive dnegative
      -- Besides the four child-output wires, multiplication introduces the
      -- four signed products `pp`, `nn`, `pn`, and `np`.  Packing all eight
      -- values into one `Fin 8` tuple lets one use `ex_dioph` exactly once.
      have dlen' : Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => lenFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dlen
      have dq' : Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => qFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dq
      have dcolumn' : ∀ x, Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => columnFn x (v ∘ Sum.inl)) :=
        fun x => Dioph.reindex_diophFn Sum.inl (dcolumn x)
      have dpositive' : Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => positiveFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dpositive
      have dnegative' : Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => negativeFn (v ∘ Sum.inl)) :=
        Dioph.reindex_diophFn Sum.inl dnegative
      have dwire (i : MulWire) : Dioph.DiophFn
          (fun v : (ι ⊕ MulWire) → ℕ => v (Sum.inr i)) :=
        Dioph.proj_dioph (Sum.inr i)
      have de := ihe dlen' dq' dcolumn' (dwire 0) (dwire 1)
      have df := ihf dlen' dq' dcolumn' (dwire 2) (dwire 3)
      have dbody : Dioph {v : (ι ⊕ MulWire) → ℕ |
          Circuit atom MulRel e (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (fun x => columnFn x (v ∘ Sum.inl))
              (v (Sum.inr 0)) (v (Sum.inr 1)) ∧
          Circuit atom MulRel f (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (fun x => columnFn x (v ∘ Sum.inl))
              (v (Sum.inr 2)) (v (Sum.inr 3)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 4)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 5)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 6)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 7)) ∧
          MulRel (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 0)) (v (Sum.inr 2)) (v (Sum.inr 4)) ∧
          MulRel (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 1)) (v (Sum.inr 3)) (v (Sum.inr 5)) ∧
          MulRel (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 0)) (v (Sum.inr 3)) (v (Sum.inr 6)) ∧
          MulRel (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (v (Sum.inr 1)) (v (Sum.inr 2)) (v (Sum.inr 7)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (positiveFn (v ∘ Sum.inl)) ∧
          Code (lenFn (v ∘ Sum.inl)) (qFn (v ∘ Sum.inl))
              (negativeFn (v ∘ Sum.inl)) ∧
          positiveFn (v ∘ Sum.inl) = v (Sum.inr 4) + v (Sum.inr 5) ∧
          negativeFn (v ∘ Sum.inl) = v (Sum.inr 6) + v (Sum.inr 7)} :=
        and_dioph de <| and_dioph df <|
          and_dioph (hcode dlen' dq' (dwire 4)) <|
          and_dioph (hcode dlen' dq' (dwire 5)) <|
          and_dioph (hcode dlen' dq' (dwire 6)) <|
          and_dioph (hcode dlen' dq' (dwire 7)) <|
          and_dioph (hmul dlen' dq' (dwire 0) (dwire 2) (dwire 4)) <|
          and_dioph (hmul dlen' dq' (dwire 1) (dwire 3) (dwire 5)) <|
          and_dioph (hmul dlen' dq' (dwire 0) (dwire 3) (dwire 6)) <|
          and_dioph (hmul dlen' dq' (dwire 1) (dwire 2) (dwire 7)) <|
          and_dioph (hcode dlen' dq' dpositive') <|
          and_dioph (hcode dlen' dq' dnegative') <|
          and_dioph (eq_add_dioph dpositive' (dwire 4) (dwire 5))
            (eq_add_dioph dnegative' (dwire 6) (dwire 7))
      apply Dioph.ext (Dioph.ex_dioph dbody)
      intro v
      simp only [Set.mem_setOf_eq, Circuit, Sum.elim_inr]
      constructor
      · rintro ⟨w, he, hf, hppCode, hnnCode, hpnCode, hnpCode,
          hppMul, hnnMul, hpnMul, hnpMul, hpCode, hnCode, hpos, hneg⟩
        exact ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7,
          he, hf, hppCode, hnnCode, hpnCode, hnpCode,
          hppMul, hnnMul, hpnMul, hnpMul, hpCode, hnCode, hpos, hneg⟩
      · rintro ⟨ep, en, fp, fn, pp, nn, pn, np,
          he, hf, hppCode, hnnCode, hpnCode, hnpCode,
          hppMul, hnnMul, hpnMul, hnpMul, hpCode, hnCode, hpos, hneg⟩
        exact ⟨mulValues ep en fp fn pp nn pn np, by
          simpa [mulValues] using
            (show
              Circuit atom MulRel e (lenFn v) (qFn v)
                  (fun x => columnFn x v) ep en ∧
              Circuit atom MulRel f (lenFn v) (qFn v)
                  (fun x => columnFn x v) fp fn ∧
              Code (lenFn v) (qFn v) pp ∧
              Code (lenFn v) (qFn v) nn ∧
              Code (lenFn v) (qFn v) pn ∧
              Code (lenFn v) (qFn v) np ∧
              MulRel (lenFn v) (qFn v) ep fp pp ∧
              MulRel (lenFn v) (qFn v) en fn nn ∧
              MulRel (lenFn v) (qFn v) ep fn pn ∧
              MulRel (lenFn v) (qFn v) en fp np ∧
              Code (lenFn v) (qFn v) (positiveFn v) ∧
              Code (lenFn v) (qFn v) (negativeFn v) ∧
              positiveFn v = pp + nn ∧ negativeFn v = pn + np
              from ⟨he, hf, hppCode, hnnCode, hpnCode, hnpCode,
                hppMul, hnnMul, hpnMul, hnpMul, hpCode, hnCode,
                hpos, hneg⟩)⟩

end CircuitDioph

end PAListCoding
