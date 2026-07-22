import BoundedPAConsistency.TruthCertificateProofCompiler

/-!
# Staged compilation of uniform truth certificates

The six laws in a truth certificate are not logically independent.  A
typical construction first proves the local clauses, uses them while proving
cross-level coherence, then uses the accumulated truth laws for substitution
and PA-axiom soundness.  Finally, restricted consistency follows from all of
the newly established laws—not merely from the preceding certificate.

`PAInductiveTruthCertificateStep` is useful when every induction kernel can
be proved directly under the previous master sentence.  The structure below
provides the dependency-aware interface needed by the concrete dynamic truth
construction.  Its context grows after every stage:

```
previous
  + local
  + cross-level
  + shift
  + substitution
  + axiom soundness
  -> final consistency.
```

Every edge is represented by a typed PA proof.  `compile` invokes the four
model-coded induction kernels in order, builds each cumulative conjunction by
Hilbert proof constructors, and finally packs the same public six-field
certificate as the original compiler.
-/

namespace LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler

open LO FirstOrder
open LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.BoundedPAConsistency.TruthCertificateProofCompiler

variable {V : Type*} [ORingStructure V]
variable [V↓[ℒₒᵣ] ⊧* ISigma 1]
variable [V↓[ℒₒᵣ] ⊧* Peano]

/-! ## Cumulative contexts -/

/-- Context after the direct local law has been proved. -/
noncomputable def localContext
    (previous : TruthCertificateFields (V := V))
    (localField : Bootstrapping.Formula V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  previous.sentence ⋏ localField

/-- Context after cross-level induction. -/
noncomputable def crossContext
    (previous : TruthCertificateFields (V := V))
    (localField : Bootstrapping.Formula V ℒₒᵣ)
    (cross : Bootstrapping.Formula V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  localContext previous localField ⋏ cross

/-- Context after shift-invariance induction. -/
noncomputable def shiftContext
    (previous : TruthCertificateFields (V := V))
    (localField cross shift : Bootstrapping.Formula V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  crossContext previous localField cross ⋏ shift

/-- Context after substitution-invariance induction. -/
noncomputable def substitutionContext
    (previous : TruthCertificateFields (V := V))
    (localField cross shift substitution : Bootstrapping.Formula V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  shiftContext previous localField cross shift ⋏ substitution

/-- Complete soundness context, immediately before final consistency. -/
noncomputable def soundnessContext
    (previous : TruthCertificateFields (V := V))
    (localField cross shift substitution axiomSound :
      Bootstrapping.Formula V ℒₒᵣ) :
    Bootstrapping.Formula V ℒₒᵣ :=
  substitutionContext previous localField cross shift substitution ⋏
    axiomSound

/-! ## A dependency-aware successor step -/

/-- One successor certificate whose proof obligations are compiled in their
mathematical dependency order.

The four recursive fields remain genuine `PAInductionKernel`s.  Their
contexts name exactly the fields available at that point.  The final direct
proof sees the full new soundness context, so it can invoke the newly proved
truth and axiom laws when excluding a restricted derivation of falsity. -/
structure PAStagedTruthCertificateStep
    (previous : TruthCertificateFields (V := V)) where
  localStep : Bootstrapping.Formula V ℒₒᵣ
  proveLocalStep : Peano.internalize V ⊢!
    previous.sentence 🡒 localStep

  crossLevel : PAInductionKernel (localContext previous localStep)

  shiftInvariant : PAInductionKernel
    (crossContext previous localStep (∀⁰ crossLevel.predicate))

  substitutionInvariant : PAInductionKernel
    (shiftContext previous localStep (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate))

  axiomSound : PAInductionKernel
    (substitutionContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate))

  finalConsistency : Bootstrapping.Formula V ℒₒᵣ
  proveFinalConsistency : Peano.internalize V ⊢!
    soundnessContext previous localStep
      (∀⁰ crossLevel.predicate)
      (∀⁰ shiftInvariant.predicate)
      (∀⁰ substitutionInvariant.predicate)
      (∀⁰ axiomSound.predicate) 🡒 finalConsistency

namespace PAStagedTruthCertificateStep

/-- The public six fields produced by a staged successor step. -/
noncomputable def target
    {previous : TruthCertificateFields (V := V)}
    (step : PAStagedTruthCertificateStep previous) :
    TruthCertificateFields (V := V) where
  localStep := step.localStep
  crossLevel := ∀⁰ step.crossLevel.predicate
  shiftInvariant := ∀⁰ step.shiftInvariant.predicate
  substitutionInvariant := ∀⁰ step.substitutionInvariant.predicate
  axiomSound := ∀⁰ step.axiomSound.predicate
  finalConsistency := step.finalConsistency

/-- Compile all six stages into one typed proof of the successor master
certificate.

The intermediate conjunctions are retained only as proof objects used to
feed the next kernel.  The returned formula is `target.sentence`, exactly the
same right-associated public certificate consumed by the package layer. -/
noncomputable def compile
    {previous : TruthCertificateFields (V := V)}
    (step : PAStagedTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Peano.internalize V ⊢! step.target.sentence := by
  let hlocal : Peano.internalize V ⊢! step.localStep :=
    TProof.modusPonens step.proveLocalStep hprevious
  let hlocalContext : Peano.internalize V ⊢!
      localContext previous step.localStep :=
    Entailment.K_intro hprevious hlocal
  let hcross : Peano.internalize V ⊢! ∀⁰ step.crossLevel.predicate :=
    step.crossLevel.compile hlocalContext
  let hcrossContext : Peano.internalize V ⊢!
      crossContext previous step.localStep
        (∀⁰ step.crossLevel.predicate) :=
    Entailment.K_intro hlocalContext hcross
  let hshift : Peano.internalize V ⊢! ∀⁰ step.shiftInvariant.predicate :=
    step.shiftInvariant.compile hcrossContext
  let hshiftContext : Peano.internalize V ⊢!
      shiftContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate) :=
    Entailment.K_intro hcrossContext hshift
  let hsubstitution : Peano.internalize V ⊢!
      ∀⁰ step.substitutionInvariant.predicate :=
    step.substitutionInvariant.compile hshiftContext
  let hsubstitutionContext : Peano.internalize V ⊢!
      substitutionContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate) :=
    Entailment.K_intro hshiftContext hsubstitution
  let haxiom : Peano.internalize V ⊢! ∀⁰ step.axiomSound.predicate :=
    step.axiomSound.compile hsubstitutionContext
  let hsoundness : Peano.internalize V ⊢!
      soundnessContext previous step.localStep
        (∀⁰ step.crossLevel.predicate)
        (∀⁰ step.shiftInvariant.predicate)
        (∀⁰ step.substitutionInvariant.predicate)
        (∀⁰ step.axiomSound.predicate) :=
    Entailment.K_intro hsubstitutionContext haxiom
  let hfinal : Peano.internalize V ⊢! step.finalConsistency :=
    TProof.modusPonens step.proveFinalConsistency hsoundness
  exact step.target.intro hlocal hcross hshift hsubstitution haxiom hfinal

/-- The staged compiler's value is recognized by the internalized PA proof
predicate. -/
lemma compile_isProof
    {previous : TruthCertificateFields (V := V)}
    (step : PAStagedTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Proof (Peano.internalize V).theory
      (step.compile hprevious).val step.target.sentence.val := by
  simpa [Proof] using (step.compile hprevious).derivationOf

set_option backward.isDefEq.respectTransparency false in
/-- Public-theory version used by the existential package relation. -/
lemma compile_isPAProof
    {previous : TruthCertificateFields (V := V)}
    (step : PAStagedTruthCertificateStep previous)
    (hprevious : Peano.internalize V ⊢! previous.sentence) :
    Proof Peano (step.compile hprevious).val step.target.sentence.val := by
  simpa [Proof] using (step.compile hprevious).derivationOf

end PAStagedTruthCertificateStep

end LeanProofs.BoundedPAConsistency.StagedTruthCertificateProofCompiler
