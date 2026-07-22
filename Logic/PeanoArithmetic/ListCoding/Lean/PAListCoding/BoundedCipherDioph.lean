import PAListCoding.BoundedCipher
import PAListCoding.CircuitDioph

/-!
# Compiling bounded cipher certificates to Diophantine formulas

The semantic theorem in `BoundedCipher` reduced a variable bounded family of
polynomial equations to one finite `StaticCertificate`.  This file proves the
formal compilation step, parameterized by substitution theorems for the four
arithmetic cipher primitives.  Keeping those hypotheses explicit isolates the
long number-theoretic construction of code masks from the finite logical
assembly performed here.
-/

namespace PAListCoding

namespace BoundedCipherDioph

open BoundedDioph BoundedCipher CipherCircuit CircuitDioph
open PolynomialCipher SparseCipher
open scoped Dioph

/-! ## One additional substitution contract -/

/-- Closure contract for the four arguments of a constant-column relation
`(length, spacing, value, code)`. -/
def QuaternarySubstitutionClosed
    (R : ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {ι : Type} {a b c d : (ι → ℕ) → ℕ},
    Dioph.DiophFn a → Dioph.DiophFn b →
    Dioph.DiophFn c → Dioph.DiophFn d →
      Dioph {v : ι → ℕ | R (a v) (b v) (c v) (d v)}

theorem true_dioph {ι : Type} : Dioph {_v : ι → ℕ | True} := by
  apply Dioph.of_no_dummies _ (0 : Poly ι)
  intro v
  simp

/-! ## The finite parameter-constraint tree -/

/-- `ParameterConstraints` is Diophantine because it has one clause for each
projection occurrence in the fixed expression, not one clause for each input
row. -/
theorem parameterConstraints_dioph
    (hconst : QuaternarySubstitutionClosed ConstCode) :
    ∀ {α β : Type} (e : Expr (Coordinate α β))
      {ι : Type} {lenFn qFn : (ι → ℕ) → ℕ}
      {paramsFn : Option α → (ι → ℕ) → ℕ}
      {columnFn : Coordinate α β → (ι → ℕ) → ℕ},
      Dioph.DiophFn lenFn → Dioph.DiophFn qFn →
      (∀ x, Dioph.DiophFn (paramsFn x)) →
      (∀ x, Dioph.DiophFn (columnFn x)) →
      Dioph {v : ι → ℕ |
        ParameterConstraints (fun x => paramsFn x v) e
          (lenFn v) (qFn v) (fun x => columnFn x v)} := by
  intro α β e
  induction e with
  | proj x =>
      intro ι lenFn qFn paramsFn columnFn dlen dq dparams dcolumns
      rcases x with (_ | a) | b
      · simpa only [ParameterConstraints] using (true_dioph (ι := ι))
      · simpa only [ParameterConstraints] using
          hconst dlen dq (dparams (some a)) (dcolumns (.inl (some a)))
      · simpa only [ParameterConstraints] using (true_dioph (ι := ι))
  | const z =>
      intro ι lenFn qFn paramsFn columnFn dlen dq dparams dcolumns
      simpa only [ParameterConstraints] using (true_dioph (ι := ι))
  | sub e f ihe ihf =>
      intro ι lenFn qFn paramsFn columnFn dlen dq dparams dcolumns
      simpa only [ParameterConstraints] using
        and_dioph (ihe dlen dq dparams dcolumns)
          (ihf dlen dq dparams dcolumns)
  | mul e f ihe ihf =>
      intro ι lenFn qFn paramsFn columnFn dlen dq dparams dcolumns
      simpa only [ParameterConstraints] using
        and_dioph (ihe dlen dq dparams dcolumns)
          (ihf dlen dq dparams dcolumns)

theorem staticAtom_closed {α β : Type}
    (hindex : TernarySubstitutionClosed IndexCode)
    (hcode : TernarySubstitutionClosed Code) :
    ∀ x : Coordinate α β, TernarySubstitutionClosed (StaticAtom x) := by
  intro x
  unfold TernarySubstitutionClosed at hindex hcode ⊢
  intro ι aFn bFn cFn da db dc
  rcases x with (_ | a) | b
  · simpa only [StaticAtom] using hindex da db dc
  · simpa only [StaticAtom] using hcode da db dc
  · simpa only [StaticAtom] using hcode da db dc

/-! ## Hiding the outer certificate tuple -/

private abbrev CertificateWire (γ : Type) := Fin 3 ⊕ γ

private def certificateValues {γ : Type}
    (q positive negative : ℕ) (columns : γ → ℕ) :
    CertificateWire γ → ℕ
  | .inl i => ![q, positive, negative] i
  | .inr x => columns x

/-- Under the primitive closure contracts, the complete static certificate
for any fixed polynomial is Diophantine. -/
theorem staticCertificate_dioph
    {α β : Type}
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel)
    (p : Poly (Coordinate α β)) :
    Dioph {params : Option α → ℕ | StaticCertificate p params} := by
  let e := Expr.ofPoly p
  let γ := Coordinate α β
  let W := CertificateWire γ
  have dparams (x : Option α) : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (Sum.inl x)) :=
    Dioph.proj_dioph (Sum.inl x)
  have dlen : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (.inl none)) :=
    dparams none
  have dq : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (.inr (.inl 0))) :=
    Dioph.proj_dioph (Sum.inr (Sum.inl 0))
  have dpositive : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (.inr (.inl 1))) :=
    Dioph.proj_dioph (Sum.inr (Sum.inl 1))
  have dnegative : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (.inr (.inl 2))) :=
    Dioph.proj_dioph (Sum.inr (Sum.inl 2))
  have dcolumns (x : γ) : Dioph.DiophFn
      (fun v : (Option α ⊕ W) → ℕ => v (.inr (.inr x))) :=
    Dioph.proj_dioph (Sum.inr (Sum.inr x))
  have dcircuit : Dioph {v : (Option α ⊕ W) → ℕ |
      Circuit StaticAtom MulRel e (v (.inl none)) (v (.inr (.inl 0)))
        (fun x => v (.inr (.inr x)))
        (v (.inr (.inl 1))) (v (.inr (.inl 2)))} :=
    circuit_dioph (staticAtom_closed hindex hcode) hcode hconstFixed hmul e
      dlen dq dcolumns dpositive dnegative
  have dconstraints : Dioph {v : (Option α ⊕ W) → ℕ |
      ParameterConstraints (fun x => v (.inl x)) e
        (v (.inl none)) (v (.inr (.inl 0)))
        (fun x => v (.inr (.inr x)))} :=
    parameterConstraints_dioph hconst e dlen dq dparams dcolumns
  have deq : Dioph {v : (Option α ⊕ W) → ℕ |
      v (.inr (.inl 1)) = v (.inr (.inl 2))} :=
    Dioph.eq_dioph dpositive dnegative
  have dbody : Dioph {v : (Option α ⊕ W) → ℕ |
      Circuit StaticAtom MulRel e (v (.inl none)) (v (.inr (.inl 0)))
          (fun x => v (.inr (.inr x)))
          (v (.inr (.inl 1))) (v (.inr (.inl 2))) ∧
        ParameterConstraints (fun x => v (.inl x)) e
          (v (.inl none)) (v (.inr (.inl 0)))
          (fun x => v (.inr (.inr x))) ∧
        v (.inr (.inl 1)) = v (.inr (.inl 2))} :=
    and_dioph dcircuit (and_dioph dconstraints deq)
  apply Dioph.ext (Dioph.ex_dioph dbody)
  intro params
  simp only [Set.mem_setOf_eq, StaticCertificate]
  constructor
  · rintro ⟨w, hcircuit, hparams, heq⟩
    exact ⟨w (.inl 0), fun x => w (.inr x), w (.inl 1), w (.inl 2),
      hcircuit, hparams, heq⟩
  · rintro ⟨q, columns, positive, negative, hcircuit, hparams, heq⟩
    refine ⟨certificateValues q positive negative columns, ?_⟩
    simpa [certificateValues] using
      (show
        Circuit StaticAtom MulRel e (params none) q columns positive negative ∧
          ParameterConstraints params e (params none) q columns ∧
          positive = negative
        from ⟨hcircuit, hparams, heq⟩)

/-! ## The bounded-universal closure theorem, conditional only on primitives -/

/-- Canonical projection-bound form of bounded universal elimination. -/
theorem projectionBoundedForall_dioph
    {α : Type} {R : Set (Option α → ℕ)}
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel)
    (dR : Dioph R) :
    Dioph {params : Option α → ℕ |
      ∀ i, i < params none → consValue i (params ∘ some) ∈ R} := by
  rcases dR with ⟨β, p, hp⟩
  have dcertificate :=
    staticCertificate_dioph hcode hconstFixed hconst hindex hmul p
  apply Dioph.ext dcertificate
  intro params
  change StaticCertificate p params ↔
    ∀ i, i < params none → consValue i (params ∘ some) ∈ R
  rw [staticCertificate_iff_bounded_witnesses]
  constructor
  · intro h i hi
    exact (hp (consValue i (params ∘ some))).mpr (h i hi)
  · intro h i hi
    exact (hp (consValue i (params ∘ some))).mp (h i hi)

/-- Matiyasevich bounded-universal closure after substituting any
Diophantine bound function. -/
theorem boundedForall_dioph
    {α : Type} {R : Set (Option α → ℕ)}
    {bound : (α → ℕ) → ℕ}
    (hcode : TernarySubstitutionClosed Code)
    (hconstFixed : ∀ k, TernarySubstitutionClosed
      (fun len q code => ConstCode len q k code))
    (hconst : QuaternarySubstitutionClosed ConstCode)
    (hindex : TernarySubstitutionClosed IndexCode)
    (hmul : QuinarySubstitutionClosed MulRel)
    (dbound : Dioph.DiophFn bound) (dR : Dioph R) :
    Dioph (BoundedForall bound R) := by
  have dcanonical := projectionBoundedForall_dioph
    hcode hconstFixed hconst hindex hmul dR
  apply Dioph.ext (Dioph.diophFn_comp1 dcanonical dbound)
  intro v
  rfl

end BoundedCipherDioph

end PAListCoding
