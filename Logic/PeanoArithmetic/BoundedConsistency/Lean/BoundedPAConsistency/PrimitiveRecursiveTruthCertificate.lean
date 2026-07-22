import BoundedPAConsistency.TruthCertificateProofCompiler
import BoundedPAConsistency.UniformProofPackage
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
# Represented primitive recursion of typed truth certificates

`TruthCertificateProofCompiler` produces genuine proof codes in an arbitrary
PA model, but a uniform selector additionally needs a represented recursion
which can be iterated to a nonstandard model element.  Foundation's
`PR.Construction` is exactly that API: its zero and successor functions come
with fixed Sigma-one graph formulae, and `PR.Construction.result` is the
internally represented iterate obtained from a coded HFS computation
sequence.

This file connects that recursion API to `UniformProofPackage`.  A certificate
family consists of the five reusable fields from the typed proof compiler;
the sixth field is fixed here to the requested bounded-consistency formula.
A package witness is not an abstract state: it is the actual PA proof code of
the resulting six-field master certificate.  The final proof selector is
obtained by applying the typed final-field projection to that proof code.

Thus the remaining uniform-construction obligation is sharply isolated: give
a `PR.Construction` whose represented successor graph agrees, on valid master
proofs, with a `PAInductiveTruthCertificateStep`.  No external recursion over
`Nat` and no decoding of a possibly nonstandard formula occurs below.
-/

namespace LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
open LeanProofs.BoundedPAConsistency.UniformInternalProvability
open LeanProofs.BoundedPAConsistency.UniformProofPackage

variable {V : Type*} [ORingStructure V]
variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The typed model-coded formula for the requested consistency instance at
an arbitrary (possibly nonstandard) model element. -/
noncomputable def paRestrictedConsistencyFormula (n : V) :
    Bootstrapping.Formula V ℒₒᵣ :=
  (⌜paRestrictedConsistencyTemplate⌝ :
      Bootstrapping.Semiformula V ℒₒᵣ 1).subst
    ![Arithmetic.typedNumeral n]

/-- Its raw code is exactly the code used by the existing uniform selector. -/
@[simp] theorem paRestrictedConsistencyFormula_val (n : V) :
    (paRestrictedConsistencyFormula n).val =
      substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n := by
  simp [paRestrictedConsistencyFormula, substNumeral,
    Arithmetic.typedNumeral]
  rw [← Sentence.quote_eq]

/-- A level-indexed family of the five reusable master-certificate fields.

The final field is deliberately omitted: `fields` below inserts the exact
bounded-consistency target, preventing a package from certifying some easier
unrelated conclusion. -/
structure PATruthCertificateFamily where
  localStep : V → Bootstrapping.Formula V ℒₒᵣ
  crossLevel : V → Bootstrapping.Formula V ℒₒᵣ
  shiftInvariant : V → Bootstrapping.Formula V ℒₒᵣ
  substitutionInvariant : V → Bootstrapping.Formula V ℒₒᵣ
  axiomSound : V → Bootstrapping.Formula V ℒₒᵣ

namespace PATruthCertificateFamily

/-- The six typed fields at level `n`, with the requested target forced into
the last coordinate. -/
noncomputable def fields (family : PATruthCertificateFamily (V := V))
    (n : V) : TruthCertificateFields (V := V) where
  localStep := family.localStep n
  crossLevel := family.crossLevel n
  shiftInvariant := family.shiftInvariant n
  substitutionInvariant := family.substitutionInvariant n
  axiomSound := family.axiomSound n
  finalConsistency := paRestrictedConsistencyFormula n

/-- Raw code of the right-associated six-field master certificate. -/
noncomputable def code (family : PATruthCertificateFamily (V := V))
    (n : V) : V :=
  (family.fields n).sentence.val

set_option backward.isDefEq.respectTransparency false in
/-- Regard a represented proof of the raw master code as a typed proof.

The transparency option only identifies the public PA definability instance
with the same instance stored by `Theory.internalize`; it does not choose or
alter the input proof code. -/
noncomputable def toTProof
    (family : PATruthCertificateFamily (V := V)) {n d : V}
    (h : Proof Peano d (family.code n)) :
    Peano.internalize V ⊢! (family.fields n).sentence :=
  ⟨d, by simpa [Proof, code] using h⟩

set_option backward.isDefEq.respectTransparency false in
/-- A master-certificate proof always yields a proof of the requested final
consistency formula.  This discharges `UniformProofPackage`'s final-extraction
hypothesis rather than leaving it abstract. -/
theorem exists_finalProof_of_masterProof
    (family : PATruthCertificateFamily (V := V)) {n d : V}
    (h : Proof Peano d (family.code n)) :
    ∃ q : V, Proof Peano q
      (substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n) := by
  let master := family.toTProof h
  let final := (family.fields n).finalConsistencyProof master
  have hfinal : Proof Peano final.val
      (family.fields n).finalConsistency.val := by
    simpa [Proof] using final.derivationOf
  have htarget : (family.fields n).finalConsistency.val =
      substNumeral (⌜paRestrictedConsistencyTemplate⌝ : V) n := by
    simp [fields]
  exact ⟨final.val, htarget ▸ hfinal⟩

end PATruthCertificateFamily

/-! ## The represented computation package -/

/-- The canonical package generated by a represented primitive recursion.

`d = compiler.result parameters n` pins the witness to the HFS computation
sequence built by `PR.Construction`.  The second conjunct says that this very
number is a PA proof of the six-field certificate, so the package contains a
genuine coded certificate rather than only a semantic invariant. -/
def PrimitiveRecursivePackage
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V)) (n d : V) : Prop :=
  d = compiler.result parameters n ∧
    Proof Peano d (family.code n)

/-- The canonical package relation is Sigma-one whenever the master-formula
code is Sigma-one definable.  Representability of the iterator itself is
already supplied by `PR.Construction.result_definable`.

The `masterCodeDefinable` premise is the smallest syntax-side theorem still
needed from a concrete dynamic truth-formula development: it asks only for a
graph of the assembled six-field formula code, not for a proof selector. -/
lemma primitiveRecursivePackage_definable
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code) :
    HierarchySymbol.sigmaOne.DefinableRel
      (PrimitiveRecursivePackage compiler parameters family) := by
  have resultDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁
        (fun n : V ↦ compiler.result parameters n) := by
    let inputs : Fin (k + 1) → (Fin 1 → V) → V :=
      fun i ↦ Fin.cases (fun z ↦ z 0) (fun j _ ↦ parameters j) i
    have h := HierarchySymbol.DefinableFunction.substitution
      (f := inputs) (compiler.result_definable) (by
        intro i
        cases i using Fin.cases with
        | zero => exact HierarchySymbol.DefinableFunction.var 0
        | succ i => exact HierarchySymbol.DefinableFunction.const (parameters i))
    simpa [inputs] using h
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁
      (fun n : V ↦ compiler.result parameters n) := resultDefinable
  letI : HierarchySymbol.sigmaOne.DefinableFunction₁ family.code :=
    masterCodeDefinable
  unfold PrimitiveRecursivePackage
  definability

/-- A represented primitive-recursive certificate compiler gives the
arbitrary-model selector required by `UniformInternalProvability`.

The base premise is an actual proof-code judgment.  The successor premise is
only correctness of the already represented function
`compiler.succ`; its Sigma-one graph is part of `PR.Construction`.  Final
extraction is automatic from the sixth certificate field. -/
theorem paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate :
      Proof Peano (compiler.zero parameters) (family.code 0))
    (successorCertificate : ∀ n d : V,
      Proof Peano d (family.code n) →
      Proof Peano (compiler.succ parameters n d) (family.code (n + 1))) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_package
    (Package := PrimitiveRecursivePackage compiler parameters family)
  · exact primitiveRecursivePackage_definable compiler parameters family
      masterCodeDefinable
  · refine ⟨compiler.result parameters 0, ?_⟩
    simpa [PrimitiveRecursivePackage] using baseCertificate
  · intro n d hd
    rcases hd with ⟨rfl, hd⟩
    refine ⟨compiler.result parameters (n + 1), rfl, ?_⟩
    simpa only [PR.Construction.result_succ] using
      successorCertificate n (compiler.result parameters n) hd
  · intro n d hd
    exact family.exists_finalProof_of_masterProof hd.2

/-! ## Direct connection to the typed successor compiler -/

variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-- Exact realization condition for one represented successor code.

For every valid input proof, the represented arithmetic function must agree
with some typed four-induction certificate step, and that step's target must
be the next member of `family`.  This is substantially narrower than assuming
successor correctness: `PAInductiveTruthCertificateStep.compile_isPAProof`
will derive correctness from these two code equalities. -/
def RealizesTypedCertificateSuccessor
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V)) : Prop :=
  ∀ n d : V, ∀ h : Proof Peano d (family.code n),
    ∃ step : PAInductiveTruthCertificateStep (family.fields n),
      step.target.sentence.val = family.code (n + 1) ∧
      compiler.succ parameters n d =
        (step.compile (family.toTProof h)).val

/-- Selector theorem whose successor hypothesis is stated directly in terms
of the typed truth-certificate compiler. -/
theorem paRestrictedConsistencyProofSelectorIn_of_typedPrimitiveRecursivePackage
    {k : ℕ} {blueprint : PR.Blueprint k}
    (compiler : PR.Construction V blueprint) (parameters : Fin k → V)
    (family : PATruthCertificateFamily (V := V))
    (masterCodeDefinable :
      HierarchySymbol.sigmaOne.DefinableFunction₁ family.code)
    (baseCertificate :
      Proof Peano (compiler.zero parameters) (family.code 0))
    (successorRealization :
      RealizesTypedCertificateSuccessor compiler parameters family) :
    PARestrictedConsistencyProofSelectorIn V := by
  apply paRestrictedConsistencyProofSelectorIn_of_primitiveRecursivePackage
    compiler parameters family masterCodeDefinable baseCertificate
  intro n d hd
  rcases successorRealization n d hd with ⟨step, htarget, hcode⟩
  rw [hcode]
  have hproof := step.compile_isPAProof (family.toTProof hd)
  rwa [htarget] at hproof

end LeanProofs.BoundedPAConsistency.PrimitiveRecursiveTruthCertificate
