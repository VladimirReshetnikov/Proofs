# First-order compactness

The [compactness theorem](https://en.wikipedia.org/wiki/Compactness_theorem)
says that a set of first-order sentences has a model if and only if every
finite subset has a model.  This directory exposes that statement at two
complementary trust and generality boundaries.

## Arbitrary-language theorem in Lean

`LeanProofs.FirstOrderCompactness.arbitrary_language_compactness` has the
universe-polymorphic type

```lean
{L : FirstOrder.Language.{u, v}} {T : L.Theory} →
  T.IsSatisfiable ↔ T.IsFinitelySatisfiable
```

Here `L` is an arbitrary first-order signature, `T` is a set of `L`-sentences,
and finite satisfiability quantifies over actual `Finset L.Sentence` subsets.
This is the literal general form of the theorem.  The repository theorem is a
thin audited re-export of Mathlib's semantic ultraproduct proof in
`Mathlib.ModelTheory.Satisfiability`; it is not presented as an independent
reproof of that imported result.

The source is `Compactness/Lean/ArbitraryLanguageCompactness.lean`; its
assumption audit is `Compactness/Lean/ArbitraryLanguageCompactness/Audit.lean`.

## Independent fixed-language proof in Lean and Coq

The repository's from-scratch first-order calculus uses the fixed countable
language of equality and one binary relation (`fMem`).  For arbitrary
sentence theories in that language, the exact bidirectional theorem is proved
independently in both kernels:

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

A finite subtheory is represented by a list all of whose members belong to
`T`.  Lists enumerate precisely the finite subcollections relevant to the
theorem; order and repetition do not affect satisfaction.  A model packages
an assignment `nat -> Dom`, which itself guarantees that `Dom` is nonempty.
Because members of `T` are sentences, `Sat_sentence_inv` proves that the
chosen assignment is semantically irrelevant.

The easy direction restricts one model of `T` to each finite subtheory.  For
the converse, suppose the whole theory proved falsity.  Relative provability
contains an explicit finite list of theory axioms supporting that derivation.
Finite satisfiability supplies a model of this list, while soundness says the
same model satisfies falsity—a contradiction.  Thus the theory is
syntactically consistent, and the existing Henkin theorem `model_of_BCon`
constructs a model of all its sentences.

The fixed-language proof is in `Lean/FirstOrder/Compactness.lean` and
`Coq/Compactness.v`; the corresponding `Audit` files check both directions
and print the kernel assumptions.

The distinction is intentional: arbitrary-signature compactness is currently
Lean-only through Mathlib, while the independent repository-native Lean/Coq
proof covers the fixed countable relation language.  No generic Coq parity is
claimed.

## Verification

From the repository root, the independent Lean proof and audit can be built
without Mathlib:

```powershell
lake --dir Logic/FirstOrder/Lean build FirstOrder.Compactness FirstOrder.Audit
```

The general Lean target has its own Mathlib-backed Lake project:

```powershell
lake --dir Logic/FirstOrder/Compactness/Lean exe cache get
lake --dir Logic/FirstOrder/Compactness/Lean build `
  ArbitraryLanguageCompactness ArbitraryLanguageCompactness.Audit
```

With the dependencies in `_CoqProject` compiled, check the Coq proof and its
complete imported closure with:

```powershell
$q = @('-Q', 'Logic/FirstOrder/Coq', 'FirstOrder')
coqc @q Logic/FirstOrder/Coq/Compactness.v
coqc @q Logic/FirstOrder/Coq/Audit.v
coqchk -silent @q FirstOrder.Compactness FirstOrder.Audit
```

The custom Lean theorem uses only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` principles inherited from completeness.
The Coq theorem uses only its documented standard-library classical choice,
extensionality, and proof-irrelevance principles.  Neither proof introduces a
project-local axiom or admission.
