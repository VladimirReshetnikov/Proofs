import BoundedPAConsistency.ModelCodedInductionAxiom

/-!
# Typed proof compiler for uniform truth certificates

The uniform bounded-consistency argument must manipulate proofs whose formula
codes can be nonstandard elements of a model of PA.  A metatheoretic theorem
that merely says that each standard instance is provable cannot do that job.
This file instead builds `TProof` objects.  Consequently every constructor
below returns an actual model-internal derivation code through its `.val`
projection.

The master certificate has six proof-relevant fields.  The first four are the
truth-construction data used at the next hierarchy level:

* `localStep` packages the domain and local Boolean/quantifier clauses;
* `crossLevel` packages the comparison with the preceding truth predicate;
* `shiftInvariant` packages the shift law;
* `substitutionInvariant` packages both free-variable and simultaneous-
  substitution laws.

`axiomSound` packages soundness of the PA axiom recognizer, while
`finalConsistency` is the current bounded-consistency conclusion.  In a
concrete implementation a field may itself be a conjunction of several laws;
the compiler only fixes the outer, reusable interface.

The final section is the important proof-template specialization API.  A
`PAInductionKernel C` is a model-coded unary formula together with closedness
and PA proofs, under context `C`, of its zero and successor cases.  Its
`compile` method invokes the actual PA induction axiom and produces a typed
proof of the universal closure.  Four such kernels, plus the two direct
fields, compile one complete successor certificate.
-/

namespace LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.ModelCodedInductionAxiom

variable {V : Type*} [ORingStructure V]
variable [hISigma : V↓[ℒₒᵣ] ⊧* ISigma 1]

/-- The six outer fields retained by a uniform truth certificate.

These are typed model-coded formulas, rather than external Lean predicates.
They can therefore contain nonstandard codes chosen by the package
construction. -/
structure TruthCertificateFields where
  localStep : Bootstrapping.Formula V ℒₒᵣ
  crossLevel : Bootstrapping.Formula V ℒₒᵣ
  shiftInvariant : Bootstrapping.Formula V ℒₒᵣ
  substitutionInvariant : Bootstrapping.Formula V ℒₒᵣ
  axiomSound : Bootstrapping.Formula V ℒₒᵣ
  finalConsistency : Bootstrapping.Formula V ℒₒᵣ

namespace TruthCertificateFields

/-- The right-associated master sentence stored with one proof code. -/
noncomputable def sentence (F : TruthCertificateFields (V := V)) :
    Bootstrapping.Formula V ℒₒᵣ :=
  F.localStep ⋏
    (F.crossLevel ⋏
      (F.shiftInvariant ⋏
        (F.substitutionInvariant ⋏
          (F.axiomSound ⋏ F.finalConsistency))))

variable {T : InternalTheory V ℒₒᵣ}

/-- Pack proofs of all six fields into one typed proof of the master
certificate.  This is a proof-code constructor, not an existence theorem. -/
noncomputable def intro (F : TruthCertificateFields (V := V))
    (hlocal : T ⊢! F.localStep)
    (hcross : T ⊢! F.crossLevel)
    (hshift : T ⊢! F.shiftInvariant)
    (hsubst : T ⊢! F.substitutionInvariant)
    (haxiom : T ⊢! F.axiomSound)
    (hfinal : T ⊢! F.finalConsistency) :
    T ⊢! F.sentence :=
  Entailment.K_intro hlocal <|
    Entailment.K_intro hcross <|
      Entailment.K_intro hshift <|
        Entailment.K_intro hsubst <|
          Entailment.K_intro haxiom hfinal

/-- Extract the local-step proof without decoding the proof code. -/
noncomputable def localStepProof {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.localStep :=
  Entailment.K_left h

/-- Extract the cross-level proof without decoding the proof code. -/
noncomputable def crossLevelProof {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.crossLevel :=
  Entailment.K_left (Entailment.K_right h)

/-- Extract the shift-invariance proof without decoding the proof code. -/
noncomputable def shiftInvariantProof
    {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.shiftInvariant :=
  Entailment.K_left (Entailment.K_right (Entailment.K_right h))

/-- Extract the substitution-invariance proof without decoding the proof
code. -/
noncomputable def substitutionInvariantProof
    {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.substitutionInvariant :=
  Entailment.K_left
    (Entailment.K_right (Entailment.K_right (Entailment.K_right h)))

/-- Extract the PA-axiom-soundness proof without decoding the proof code. -/
noncomputable def axiomSoundProof {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.axiomSound :=
  Entailment.K_left
    (Entailment.K_right
      (Entailment.K_right (Entailment.K_right (Entailment.K_right h))))

/-- Extract the final bounded-consistency proof without decoding the proof
code. -/
noncomputable def finalConsistencyProof
    {F : TruthCertificateFields (V := V)}
    (h : T ⊢! F.sentence) : T ⊢! F.finalConsistency :=
  Entailment.K_right
    (Entailment.K_right
      (Entailment.K_right
        (Entailment.K_right (Entailment.K_right h))))

end TruthCertificateFields

/-! ## A generic one-step proof transformer -/

/-- Fixed proof templates that derive every field of `next` from the single
master formula of `previous`.

These six implications are exactly the genuinely remaining inputs when the
next fields have already been chosen.  `compile` below applies them to an
actual previous proof and packs the resulting proof codes. -/
structure TruthCertificateStep
    (T : InternalTheory V ℒₒᵣ)
    (previous next : TruthCertificateFields (V := V)) where
  proveLocalStep : T ⊢! previous.sentence 🡒 next.localStep
  proveCrossLevel : T ⊢! previous.sentence 🡒 next.crossLevel
  proveShiftInvariant : T ⊢! previous.sentence 🡒 next.shiftInvariant
  proveSubstitutionInvariant :
    T ⊢! previous.sentence 🡒 next.substitutionInvariant
  proveAxiomSound : T ⊢! previous.sentence 🡒 next.axiomSound
  proveFinalConsistency :
    T ⊢! previous.sentence 🡒 next.finalConsistency

namespace TruthCertificateStep

/-- Apply all six fixed templates to one previous certificate proof.

The returned object is a typed internal proof; `(compile step h).val` is the
successor proof code that a package constructor stores. -/
noncomputable def compile
    {T : InternalTheory V ℒₒᵣ}
    {previous next : TruthCertificateFields (V := V)}
    (step : TruthCertificateStep T previous next)
    (hprevious : T ⊢! previous.sentence) :
    T ⊢! next.sentence :=
  next.intro
    (TProof.modusPonens step.proveLocalStep hprevious)
    (TProof.modusPonens step.proveCrossLevel hprevious)
    (TProof.modusPonens step.proveShiftInvariant hprevious)
    (TProof.modusPonens step.proveSubstitutionInvariant hprevious)
    (TProof.modusPonens step.proveAxiomSound hprevious)
    (TProof.modusPonens step.proveFinalConsistency hprevious)

/-- The compiler's `.val` projection is accepted by the represented proof
predicate.  This is the bridge used when storing the result in a Sigma-one
package relation. -/
lemma compile_isProof
    {T : InternalTheory V ℒₒᵣ}
    {previous next : TruthCertificateFields (V := V)}
    (step : TruthCertificateStep T previous next)
    (hprevious : T ⊢! previous.sentence) :
    Proof T.theory (compile step hprevious).val next.sentence.val := by
  simpa [Proof] using (compile step hprevious).derivationOf

end TruthCertificateStep

/-! ## Specializing inductive proof templates inside PA -/

variable [hPA : V↓[ℒₒᵣ] ⊧* Peano]

/-- Inputs for one formula-induction proof template under a closed context
formula `context`.

Only `predicate` may be nonstandard.  The two derivations are implications
from the previous master certificate, so they are fixed templates that can be
specialized before the previous proof is known.  `shiftFixed` is the coded
closedness side condition required by PA's induction-axiom recognizer. -/
structure PAInductionKernel (context : Bootstrapping.Formula V ℒₒᵣ) where
  predicate : Bootstrapping.Semiformula V ℒₒᵣ 1
  shiftFixed : shift ℒₒᵣ predicate.val = predicate.val
  proveZero : Peano.internalize V ⊢!
    context 🡒 predicate.subst ![⌜(‘0’ : ArithmeticSemiterm ℕ 0)⌝]
  proveSuccessor : Peano.internalize V ⊢!
    context 🡒
      ∀⁰ (predicate 🡒 predicate.subst
        ![⌜(‘#0 + 1’ : ArithmeticSemiterm ℕ 1)⌝])

namespace PAInductionKernel

/-- Specialize the base/successor templates and invoke the model-coded PA
induction axiom. -/
noncomputable def compile {context : Bootstrapping.Formula V ℒₒᵣ}
    (kernel : PAInductionKernel context)
    (hcontext : Peano.internalize V ⊢! context) :
    Peano.internalize V ⊢! ∀⁰ kernel.predicate :=
  paInductionOfShiftFixed kernel.predicate kernel.shiftFixed
    (TProof.modusPonens kernel.proveZero hcontext)
    (TProof.modusPonens kernel.proveSuccessor hcontext)

end PAInductionKernel

/-- The concrete shape of a successor certificate whose four recursive laws
are proved by model-coded formula induction.

The local step and final consistency result are direct proof templates.  The
four middle fields are universal closures generated by their corresponding
`PAInductionKernel`s.  This records precisely which proof templates a future
arithmetic truth-formula construction must supply; packing and induction are
already implemented here. -/
structure PAInductiveTruthCertificateStep
    (previous : TruthCertificateFields (V := V)) where
  localStep : Bootstrapping.Formula V ℒₒᵣ
  crossLevel : PAInductionKernel previous.sentence
  shiftInvariant : PAInductionKernel previous.sentence
  substitutionInvariant : PAInductionKernel previous.sentence
  axiomSound : PAInductionKernel previous.sentence
  finalConsistency : Bootstrapping.Formula V ℒₒᵣ
  proveLocalStep : Peano.internalize V ⊢!
    previous.sentence 🡒 localStep
  proveFinalConsistency : Peano.internalize V ⊢!
    previous.sentence 🡒 finalConsistency

namespace PAInductiveTruthCertificateStep

/-- The six target fields determined by an inductive successor step. -/
noncomputable def target {previous : TruthCertificateFields (V := V)}
    (step : PAInductiveTruthCertificateStep previous) :
    TruthCertificateFields (V := V) where
  localStep := step.localStep
  crossLevel := ∀⁰ step.crossLevel.predicate
  shiftInvariant := ∀⁰ step.shiftInvariant.predicate
  substitutionInvariant := ∀⁰ step.substitutionInvariant.predicate
  axiomSound := ∀⁰ step.axiomSound.predicate
  finalConsistency := step.finalConsistency

/-- Compile one full successor certificate, including four genuine uses of
PA induction on model-coded unary formulas.

No decoding or standardness hypothesis occurs.  In particular, `.val` of the
result is a proof code in the ambient model even when the truth formula and
the hierarchy level stored in the templates are nonstandard. -/
noncomputable def compile
    {previous : TruthCertificateFields (V := V)}
    (step : PAInductiveTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Peano.internalize V ⊢! step.target.sentence :=
  step.target.intro
    (TProof.modusPonens step.proveLocalStep hprevious)
    (step.crossLevel.compile hprevious)
    (step.shiftInvariant.compile hprevious)
    (step.substitutionInvariant.compile hprevious)
    (step.axiomSound.compile hprevious)
    (TProof.modusPonens step.proveFinalConsistency hprevious)

/-- The inductive successor compiler produces a code recognized by the
represented PA proof predicate. -/
lemma compile_isProof
    {previous : TruthCertificateFields (V := V)}
    (step : PAInductiveTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Proof (Peano.internalize V).theory
      (compile step hprevious).val step.target.sentence.val := by
  simpa [Proof] using (compile step hprevious).derivationOf

set_option backward.isDefEq.respectTransparency false in
/-- The same bridge with the public `Peano` theory instance used by package
relations.  The transparency setting only unfolds the `internalize` wrapper;
it does not add an axiom or alter the generated proof code. -/
lemma compile_isPAProof
    {previous : TruthCertificateFields (V := V)}
    (step : PAInductiveTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Proof Peano (compile step hprevious).val step.target.sentence.val := by
  simpa [Proof] using (compile step hprevious).derivationOf

end PAInductiveTruthCertificateStep

end LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler
