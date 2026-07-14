# PA non-finite axiomatizability: a checked finite-basis reduction

## Status

An informal proof sketch from standard metatheorems is given below. This
directory currently machine-checks only its exact **finite-basis reduction**,
independently in Lean and Coq. It does not yet contain an unconditional
machine proof of the Ryll-Nardzewski--Mostowski finite-fragment theorem. The
conditional boundary is visible in both headline theorem types; there is no
`axiom`, `sorry`, `Admitted`, or hidden oracle for that missing result.

This distinction matters. Showing that PA's displayed induction schema is an
infinite set is not enough: a different finite set of sentences could, in
principle, have exactly the same deductive consequences. Neither compactness
nor the absence of finite PA models rules this out; one first-order sentence
can force all of its models to be infinite.

## The theorem

Write `PA |- phi` for first-order derivability and `Con(T)` for the standard
arithmetical sentence saying that the recursively axiomatized theory `T` has
no proof of a contradiction. Two standard metatheorems give Mostowski's proof:

1. **Reflexivity of PA.** For every finite fragment `Delta` of PA,
   `PA |- Con(Delta)`. A partial satisfaction predicate of sufficiently high
   finite complexity lets PA verify the soundness of each `Delta`-proof.
2. **Goedel's second incompleteness theorem.** A consistent, sufficiently
   strong recursively axiomatized arithmetic theory `T` does not prove
   `Con(T)`.

Suppose, for contradiction, that a finite list of arithmetic sentences
`Gamma` axiomatizes PA. Every member of `Gamma` is a PA theorem, and every
formal proof uses only finitely many PA axioms. Taking the union of those
finitely many proof supports gives a finite fragment `Delta` of PA such that
`Delta |- Gamma`. Enlarge `Delta`, if necessary, by a fixed finite arithmetic
base to which the second incompleteness theorem applies.

By reflexivity, `PA |- Con(Delta)`. Since `Gamma` has exactly PA's sentence
consequences, `Gamma |- Con(Delta)`. But `Delta |- Gamma`, so cutting the two
derivations yields `Delta |- Con(Delta)`. The standard natural-number model
shows that `Delta` is consistent, contradicting Goedel's second incompleteness
theorem. Therefore no such finite `Gamma` exists.

Equivalently, every finite list of genuine PA axioms misses a further PA
theorem. Ryll-Nardzewski's original model-theoretic proof can sharpen the
missing theorem to a further induction instance.

## What is machine-checked here

The Lean and Coq developments use the repository's real arithmetic syntax and
first-order proof calculus from `PAHF`; finite axiomatizability means equality
of all **sentence consequences in the original PA language**.

They prove:

- every arbitrary finite sentence axiomatization equivalent to a sentence
  theory can be replaced by one finite list of genuine axioms of that theory;
- the converse, so finite axiomatizability is equivalent to possessing such a
  finite fragment basis;
- finite-fragment strictness implies that PA is not finitely axiomatizable.

The first implication is the compact proof-support argument above:
`BProv_bound_list` unions the finite PA-axiom lists used by the candidate
axioms, and cut/lifting transfers all sentence consequences to the resulting
finite fragment.

The remaining proposition is deliberately a definition and theorem premise in
both developments:

```text
for every finite Delta subset of PA axioms,
there is a sealed induction instance that Delta does not prove.
```

Completing it requires arithmetized proof predicates, bounded partial
truth/reflection, and second incompleteness (Mostowski), or the
nonstandard-model and definable-cut construction of Ryll-Nardzewski. Those
layers are not present in this repository. The existing `PA.Model` cannot be
used for a shortcut: its structure already assumes induction for every
meta-level predicate, so it cannot represent a model of only finitely many
induction instances.

The maintained Lean library
[FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation)
already has Goedel II, but its missing PA-reflexivity step is itself tracked as
[open issue #701](https://github.com/FormalizedFormalLogic/Foundation/issues/701).
Russell O'Connor's Coq development similarly proves Goedel--Rosser I, not the
needed instantiated reflection/second-incompleteness result.

## Verification

Lean:

```powershell
lake --dir Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean build
lake --dir Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean env lean `
  PAFiniteBasisReduction/Audit.lean
```

Coq:

```powershell
coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/FiniteBasisReduction.v

coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq PAFiniteBasisReduction `
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/Audit.v
```

The audit modules print/check the kernel assumptions of every reduction
theorem. See [`Lean/`](Lean/) and [`Coq/`](Coq/) for the two developments.

## References

- C. Ryll-Nardzewski,
  [*The Role of the Axiom of Induction in the Elementary Arithmetic*](https://eudml.org/doc/213266),
  Fundamenta Mathematicae 39 (1952).
- A. Mostowski,
  [*On Models of Axiomatic Systems*](https://eudml.org/doc/213259),
  Fundamenta Mathematicae 39 (1952), 133--158.
- S. Berdugo Parada,
  [*Non-finite axiomatizability of first-order Peano Arithmetic*](https://diposit.ub.edu/bitstreams/0bda6e0f-6638-4222-b333-707b84556551/download),
  a detailed modern exposition of the Ryll-Nardzewski proof.
