import BoundedPAConsistency.QuantifierFreePAAxioms
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed

/-!
# PA induction for a model-coded formula

A uniform proof compiler eventually specializes fixed proof templates at a
formula whose code is an element of an arbitrary, possibly nonstandard, PA
model.  Such a formula cannot be decoded into an ordinary Lean syntax tree.
Nevertheless, PA's represented induction-axiom recognizer accepts its
induction body directly.

The only extra premise needed below is `shift K.val = K.val`.  Internal
`shift` raises free-variable indices, so this equation is the coded form of
"`K` has no free variables".  Bound variable zero remains available as the
induction variable.  The proof then gives the recognizer the particularly
simple witnesses `m = 0` and `b = indBody K`: no universal closure is needed
because the induction body is already a closed formula.
-/

namespace LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.QuantifierFreePAAxioms

variable {V : Type*} [ORingStructure V]
variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

local instance : V↓[ℒₒᵣ] ⊧* ISigma 1 := models_of_subtheory hPA

/-- The induction body of any closed model-coded unary formula is recognized
as a PA axiom.

For the internal induction recognizer we choose closure length `m = 0` and
closure body `b = indBodyVal K.val`.  Shift invariance supplies the recognizer's
free-variable-freeness check; typed well-formedness supplies its `bv = 0`
check.  The remaining recovered-core side condition is exactly
`indBodyVal_eq` together with `le_indBodyVal`.
-/
lemma indBody_mem_peano_of_shift_fixed
    (K : Semiformula V ℒₒᵣ 1)
    (hKshift : shift ℒₒᵣ K.val = K.val) :
    (indBody K).val ∈ (Peano : Theory ℒₒᵣ).Δ₁Class := by
  apply mem_pa_delta1Class_iff.mpr
  right
  rw [← indBodyVal_eq K]
  refine ⟨0, by simp, indBodyVal K.val, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · rw [indBodyVal_eq K]
    exact (indBody K).isUFormula
  · rw [indBodyVal_eq K]
    change (indBody K).shift.val = (indBody K).val
    apply congr_arg Semiformula.val
    have hKshift' : K.shift = K := Semiformula.ext hKshift
    let zeroVec : SemitermVec V ℒₒᵣ 1 0 :=
      ![Arithmetic.typedNumeral 0]
    let succVec : SemitermVec V ℒₒᵣ 1 1 :=
      ![Bootstrapping.Semiterm.bvar (V := V) (L := ℒₒᵣ) 0 +
        Arithmetic.typedNumeral 1]
    have hzero : (K.subst zeroVec).shift = K.subst zeroVec := by
      rw [Semiformula.shift_substs, hKshift']
      congr
      funext i
      simp [zeroVec]
    have hsucc : (K.subst succVec).shift = K.subst succVec := by
      rw [Semiformula.shift_substs, hKshift']
      congr
      funext i
      simp [succVec]
    simpa [indBody, zeroVec, succVec, hKshift'] using
      And.intro hzero hsucc
  · have hsemi : IsSemiformula ℒₒᵣ 0 (indBodyVal K.val) := by
      rw [indBodyVal_eq K]
      exact (indBody K).isSemiformula
    simpa [isSemiformula_iff] using hsemi.2
  · have hKsemi : IsSemiformula ℒₒᵣ 1 K.val := by
      simpa using K.isSemiformula
    have hbodySemi : IsSemiformula ℒₒᵣ 0 (indBodyVal K.val) := by
      rw [indBodyVal_eq K]
      exact (indBody K).isSemiformula
    let body : Formula V ℒₒᵣ := ⟨indBodyVal K.val, hbodySemi⟩
    let emptyVec : SemitermVec V ℒₒᵣ 0 0 := ![]
    have hempty : body.subst emptyVec = body := by simp
    have hsubstEmpty : subst ℒₒᵣ (fvarVec 0) (indBodyVal K.val) =
        indBodyVal K.val := by
      rw [fvarVec_zero]
      change (body.subst emptyVec).val = body.val
      rw [hempty]
    refine ⟨K.val, ?_, hKsemi, ?_⟩
    · rw [hsubstEmpty]
      exact le_indBodyVal K.val
    · rw [hsubstEmpty]

/-- A typed, model-internal PA proof of the corresponding induction axiom.

The proof code is a genuine element of `V`.  In particular, this constructor
also applies when `K.val` is nonstandard syntax produced by an internal truth-
formula compiler.
-/
noncomputable def paInductionProofOfShiftFixed
    (K : Semiformula V ℒₒᵣ 1)
    (hKshift : shift ℒₒᵣ K.val = K.val) :
    Peano.internalize V ⊢! indBody K :=
  TProof.byAxm (indBody_mem_peano_of_shift_fixed K hKshift)

/-- Apply the model-coded induction axiom to a base proof and a uniformly
quantified successor-step proof.

This is the proof-producing form needed by a uniform truth-certificate
compiler: both premises may themselves mention a nonstandard formula code,
and the result's `.val` is an internal PA proof code for `∀ x, K(x)`.
-/
noncomputable def paInductionOfShiftFixed
    (K : Semiformula V ℒₒᵣ 1)
    (hKshift : shift ℒₒᵣ K.val = K.val)
    (hzero : Peano.internalize V ⊢!
      K.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝])
    (hsucc : Peano.internalize V ⊢!
      ∀⁰ (K 🡒 K.subst
        ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) :
    Peano.internalize V ⊢! ∀⁰ K := by
  have htail : Peano.internalize V ⊢!
      (∀⁰ (K 🡒 K.subst
        ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])) 🡒 ∀⁰ K := by
    exact TProof.modusPonens
      (paInductionProofOfShiftFixed K hKshift) hzero
  exact TProof.modusPonens htail hsucc

end LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom
