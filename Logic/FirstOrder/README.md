# First-order completeness and compactness

This directory contains independent Lean and Rocq/Coq proofs of
[Gödel's completeness theorem](https://en.wikipedia.org/wiki/G%C3%B6del%27s_completeness_theorem)
for classical first-order logic, plus the resulting semantic
[compactness theorem](https://en.wikipedia.org/wiki/Compactness_theorem).

## Gödel completeness in Lean and Coq

The repository's from-scratch calculus uses a fixed countable language with
equality and one binary relation (`fMem`).  The textbook consequence relation
is exposed in both proof assistants:

```lean
godel_completeness_for_theories :
  ∀ T phi, Sentences T →
    TheorySemanticConsequence T phi → TheorySyntacticConsequence T phi

godel_soundness_and_completeness_for_theories :
  ∀ T phi, Sentences T →
    (TheorySyntacticConsequence T phi ↔ TheorySemanticConsequence T phi)

godel_model_existence :
  ∀ T, Sentences T → TheoryConsistent T → TheoryHasModel T

theory_consistent_iff_has_model :
  ∀ T, Sentences T → (TheoryConsistent T ↔ TheoryHasModel T)
```

```coq
godel_completeness_for_theories :
  forall T phi, Sentences T ->
    TheorySemanticConsequence T phi -> TheorySyntacticConsequence T phi

godel_soundness_and_completeness_for_theories :
  forall T phi, Sentences T ->
    (TheorySyntacticConsequence T phi <-> TheorySemanticConsequence T phi)

godel_model_existence :
  forall T, Sentences T -> TheoryConsistent T -> TheoryHasModel T

theory_consistent_iff_has_model :
  forall T, Sentences T -> (TheoryConsistent T <-> TheoryHasModel T)
```

Thus the central implication is exactly

```text
T ⊨ phi  ->  T ⊢ phi.
```

`TheorySyntacticConsequence T phi` is `BProv T [] phi`: its witness includes
the finite list of axioms of `T` actually used in the derivation.  The
finite-context theorem is stronger still: `godel_completeness G phi` allows
open formulas and quantifies over every assignment.  The original
empty-context formulation is named `godel_original_completeness`.

`TheoryConsistent T` means exactly that there is no formula `phi` for which
both `T ⊢ phi` and `T ⊢ not phi`.  The proved lemma
`theoryConsistent_iff_BCon` connects this public definition to the internal
condition `T ⊬ false`: modus ponens turns a contradictory pair into falsity,
and explosion turns a proof of falsity into a contradictory pair.  Soundness
then proves that every model makes `T` consistent, while Henkin model
existence proves the converse.

This is not merely an interface to an imported completeness theorem.  The
proof in `Lean/FirstOrder/Completeness.lean` and `Coq/Completeness.v` carries
out the Henkin construction in both kernels:

1. Extend a consistent theory by a Lindenbaum/Henkin chain that decides every
   formula and supplies witnesses.
2. Form the canonical term model, quotienting variables by provable equality.
3. Prove the truth lemma by structural induction on formulas.
4. Obtain a model of every consistent sentence theory.
5. If `T ⊨ phi` but `T ⊬ phi`, consistently add `not phi`; its Henkin model is
   a countermodel, a contradiction.

The public textbook facade is
`Lean/FirstOrder/ClassicalCompleteness.lean` and
`Coq/ClassicalCompleteness.v`.  The corresponding `Audit` files print the
kernel assumptions of the headline results.

The scope is stated deliberately: this independent Lean/Coq development is
for the repository's fixed countable relational language.  It does not claim
an arbitrary-signature syntactic completeness theorem.  The standard coding
argument that reduces any countable signature to a fixed countable relational
signature has not been formalized here.

## Compactness

For arbitrary sentence theories in the fixed language, both kernels prove

```lean
SetTheory.FirstOrderCompactness.compactness :
  ∀ T, Sentences T →
    (TheoryHasModel T ↔ FiniteSubtheoriesHaveModels T)
```

```coq
FirstOrderCompactness.compactness :
  forall T, Sentences T ->
    (TheoryHasModel T <-> FiniteSubtheoriesHaveModels T)
```

The nontrivial direction is a direct corollary of completeness.  A proof of
falsity from `T` uses finitely many axioms; a model of that finite subtheory
would satisfy falsity by soundness.  Hence `T` is consistent, and
`godel_model_existence` supplies a model.

The separate Mathlib-backed Lean target provides arbitrary-language semantic
compactness:

```lean
LeanProofs.FirstOrderCompactness.arbitrary_language_compactness :
  {L : FirstOrder.Language.{u, v}} {T : L.Theory} →
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable
```

That target is an audited re-export of Mathlib's ultraproduct proof, not an
independent reproof.  It is in
`Compactness/Lean/ArbitraryLanguageCompactness.lean`.

## Verification

Build the independent Lean development without Mathlib:

```powershell
lake --dir Logic/FirstOrder/Lean build FirstOrder.ClassicalCompleteness `
  FirstOrder.Compactness FirstOrder.Audit
```

Check the independent Coq development and its imported closure:

```powershell
$q = @('-Q', 'Logic/FirstOrder/Coq', 'FirstOrder')
coqc @q Logic/FirstOrder/Coq/ClassicalCompleteness.v
coqc @q Logic/FirstOrder/Coq/Compactness.v
coqc @q Logic/FirstOrder/Coq/Audit.v
coqchk -silent @q FirstOrder.ClassicalCompleteness `
  FirstOrder.Compactness FirstOrder.Audit
```

The Lean completeness proof uses only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` principles.  The Coq proof uses the
documented standard-library classical choice, propositional and functional
extensionality, and proof irrelevance.  Neither proof contains a project-local
axiom or admission.
