# PA non-finite axiomatizability: a checked finite-basis reduction

## Status

An informal proof sketch from standard metatheorems is given below. This
directory currently machine-checks the exact **finite-basis reduction**, the
standard-model consistency of every finite PA fragment, and the fixed-base
glue of Mostowski's argument, independently in Lean and Coq.  Both sides also
construct an explicit two-successor-chain countermodel for the rank-zero
fragment and thereby prove their first unconditional strictness witness. It
does not yet contain unconditional machine proofs of
finite-fragment reflection or the required instantiated second incompleteness
theorem. Those two conditional boundaries are visible in the theorem types;
there is no `axiom`, `sorry`, `Admitted`, or hidden oracle for either missing
result.

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
base `Base` to which the second incompleteness theorem applies; call the
resulting finite theory `T = Base ++ Delta`.

By reflexivity, `PA |- Con(T)`. Since `Gamma` has exactly PA's sentence
consequences, `Gamma |- Con(T)`. The finite theory `T` proves `Gamma` (it
contains `Delta`), so cutting the two derivations yields `T |- Con(T)`. The
standard natural-number model shows that `T` is consistent, contradicting
Goedel's second incompleteness theorem. Therefore no such finite `Gamma`
exists.

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
- every finite list of genuine PA axioms is consistent, by soundness in the
  standard natural-number model;
- structural ranks for arithmetic terms and formulas, and the canonical
  hierarchy `PARankFragment n` containing the six base axioms plus induction
  instances whose source formula has rank at most `n`;
- exact recursive list enumerations of the terms, formulas, and fragment
  axioms at each bounded rank, so the claimed finiteness of every
  `PARankFragment n` is itself machine-checked;
- cofinality of that hierarchy: every finite list of genuine PA axioms is
  contained in one `PARankFragment n`;
- exact finite-fragment sentence separation implies that PA is not finitely
  axiomatizable;
- conversely, in the classical metatheory, failure of finite
  axiomatizability implies exact finite-fragment sentence separation, so this
  remaining arithmetic proposition is an equivalent boundary rather than a
  merely sufficient one;
- a checked fixed-base Mostowski theorem derives that separation from local
  reflection plus Goedel II;
- a raw semantic bridge: a law-free arithmetic structure (`PA.PreModel` in
  Lean, `RawPAModel` in Coq) satisfying a rank fragment and falsifying a
  genuine PA axiom proves non-derivability by first-order soundness.  These
  structures contain only the four arithmetic operations and assume neither
  the PA laws nor induction;
- explicit law-free models consisting of two disjoint successor chains, which
  satisfy all six non-induction axioms but falsify induction for
  `x = 0 or exists y, x = S(y)`; consequently Lean's
  `rankZero_not_bprov_induction` and Coq's
  `PA_rank_zero_fragment_misses_zero_or_successor_induction`
  unconditionally separate `PARankFragment 0` from PA;

The first implication is the compact proof-support argument above:
`BProv_bound_list` unions the finite PA-axiom lists used by the candidate
axioms, and cut/lifting transfers all sentence consequences to the resulting
finite fragment.

The weakest remaining proposition is deliberately a definition and theorem
premise in both developments:

```text
for every finite Delta subset of PA axioms,
there is a PA-provable sentence that Delta does not prove.
```

`PAInductionFragmentStrictness` retains Ryll-Nardzewski's stronger conclusion
that the missed theorem can be another induction instance. The main boundary,
`PAFiniteFragmentStrictness`, asks only for a missed sentence. In Mostowski's
argument that sentence is `Con(Base ++ Delta)`, where `Base` is one fixed
finite PA fragment strong enough for Goedel II. The formal theorem
`finiteFragmentStrictness_of_mostowski` (and its Coq counterpart) checks the
membership, consistency, and weakening steps with the same consistency
encoding on both sides.

The canonical reformulation `PARankFragmentStrictness` asks only that every
natural-number-indexed rank fragment miss a further induction instance. The
checked theorem `finitePAFragment_bounded_by_rank` turns this into arbitrary
finite-fragment strictness, and
`pa_not_finitely_axiomatizable_of_rankFragmentStrictness` reaches the same
headline. The weaker semantic interface `PARankFragmentCountermodels`
packages raw countermodels that satisfy each rank fragment while falsifying
some PA axiom;
`pa_not_finitely_axiomatizable_of_rankFragmentCountermodels` derives the
headline through soundness. `RankZero.lean` constructs the first such
countermodel: rank zero contains only the six base axioms because every
formula rank is positive. Constructing the uniform family for every positive
rank remains the substantive Ryll-Nardzewski theorem.

Completing its two hypotheses requires arithmetized proof predicates, bounded
partial truth/reflection, and an instantiated second incompleteness theorem,
or alternatively the nonstandard-model and definable-cut construction of
Ryll-Nardzewski. Those layers are not present in this repository. `PA.Model`
cannot be used for a shortcut because it already assumes induction for every
meta-level predicate. The semantics and soundness theorem now also accept the
axiom-free `PA.PreModel`, so genuine finite-fragment countermodels can be
represented without smuggling in full induction; their construction is the
remaining mathematical work.

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
  Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Coq/HierarchyReduction.v

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
