# Proofs

**Machine-checked mathematics in Lean 4 and Rocq/Coq, organized by subject.**

`Proofs` contains formal mathematics, executable proof certificates, and the
research artifacts needed to reproduce difficult certificates. Lean 4 with
mathlib is the primary environment; Rocq/Coq developments provide independent
or complementary checks. Generated data and exploratory computations are not
part of the trusted theorem boundary unless a proved checker connects them to
the formal semantics.

**Toolchains:** Lean `4.31.0` · mathlib `v4.31.0` · Rocq `>= 9.0`
(developed against `9.0.1`) · [MIT-0](LICENSE)

## Repository map

The top-level source directories are mathematical topics. Within each coherent
project, `Lean/` and `Coq/` are siblings; `Research/`, `Support/`, and
`Article/` stay beside the mathematics they document.

| Topic | Contents |
| --- | --- |
| [`Analysis/`](Analysis/) | Exact trigonometric, arctangent, and exponential identities. |
| [`Combinatorics/`](Combinatorics/) | Enumeration of power towers and radical expressions, including OEIS certificates and research corpora. |
| [`Computability/`](Computability/) | Lambda/SK/SKI/Iota universality and the faithful Iota-to-lambda embedding; Busy Beaver semantics, domination, exact small-state scores and times, and certificate bridges. |
| [`Logic/`](Logic/) | First-order logic and completeness, propositional/equational axiom systems, PA infinitude, and PA/HF interpretability. |
| [`NumberTheory/`](NumberTheory/) | FLT for exponent four, floor-square-root sums, rational enumeration, and an arithmetic RH sentence. |
| [`SetTheory/`](SetTheory/) | First-order ZF and the Closure axiomatization's equivalence with ZF. |
| [`lib/`](lib/) | Vendored third-party code only. |

Repository-wide configuration remains at the root. [`Proofs.lean`](Proofs.lean)
is the broad Lean import surface.

## Highlights

- Fermat's Last Theorem for `n = 4`, an exact floor-square-root sum, and a
  bijective Calkin-Wilf rational orbit.
- Exact trigonometric, arctangent, and tiny-exponent-tower identities.
- Formal semantics and finite certificates for OEIS A000081, A002845,
  A158415, A198683, and A199812.
- Nicod's NAND axiom, Wolfram's single Boolean equation, Meredith's basis,
  and checked equational certificates.
- A [first-order completeness and compactness development](Logic/FirstOrder/README.md):
  from-scratch independent Lean/Coq Henkin proofs for the repository's fixed
  countable relation language, plus arbitrary-language semantic compactness
  in Lean.
- Full deductive equivalence between the Closure axiomatization and ZF,
  checked independently in Lean and Coq.
- A deductive bi-interpretation between PA and finite-generation hereditary
  finite set theory.
- A [constructive Lean/Coq proof](Logic/PeanoArithmetic/NoFiniteModel/README.md)
  that Peano arithmetic has no finite model, using only injectivity of
  successor and zero's absence from its image.
- Lean/Coq proofs that first-order Peano arithmetic has two non-isomorphic
  models, separating the numeral-generated standard model from a compactness
  model with an element above every standard numeral.
- Independent Lean and Rocq/Coq proofs that pure SK, SKI, and Iota simulate
  closed weak untyped lambda calculus by compositional positive-step compilers,
  and that Iota embeds faithfully back into closed lambda terms.
- Busy Beaver domination plus exact results `Sigma(2)=4`, `Sigma(3)=6`,
  `Sigma(4)=13` and `BB(2)=6`, `BB(3)=21`, `BB(4)=107` for the documented
  score/time conventions.

## Lean workspace

The root workspace is pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json):

```powershell
lake exe cache get
lake build
```

The broad build is intentionally expensive. Focused examples are:

```powershell
lake build +DiophantineEquations.FermatFour
lake build +ShefferStroke.Sheffer
lake build +FirstOrder.Fol
lake build +ClosureAxiomatization.Forward
lake build +NoFiniteModel
lake build +PAFiniteBasisReduction
lake build +PowerTowers.Core
lake build +CombinatoryLogic
lake build +BusyBeaver.BB2
lake build +BusyBeaver.BB3
lake build +BusyBeaver.Mathlib
```

These projects also have project-local Lake files for focused builds:

```powershell
lake --dir Logic/Propositional/NaturalDeduction/Lean build
lake --dir Logic/Propositional/FiniteMatrixNoncharacterizability/Lean build
lake --dir Logic/Propositional/MonotonicityOfEntailment/Lean build
lake --dir Logic/Propositional/PrincipleOfExplosion/Lean build
lake --dir Logic/QuantifierCommutation/Lean build
lake --dir Logic/FirstOrder/Lean build
lake --dir Logic/FirstOrder/Compactness/Lean build
lake --dir Logic/Interpretability/PAHF/Lean build
lake --dir Logic/PeanoArithmetic/NoFiniteModel/Lean build
lake --dir Logic/PeanoArithmetic/NotFinitelyAxiomatizable/Lean build
lake --dir SetTheory/ZF/Lean build
lake --dir SetTheory/ClosureAxiomatization/Lean build
lake --dir NumberTheory/RiemannHypothesis/PAStatement/Lean build
lake --dir Computability/BusyBeaver/Lean build
```

The Busy Beaver facade excludes the expensive BB2/BB3 classifications and the
mathlib compiler bridge; request those modules explicitly.

## Rocq/Coq workspace

The root [`_CoqProject`](_CoqProject) contains all logical `-Q` mappings and a
dependency-ordered source list, including the vendored certificates under
`lib/Coq-BB5`:

```powershell
coq_makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

Topic READMEs document focused `coqc` commands and Lean/Coq parity boundaries.
The combinatory-logic development checks the same weak-lambda-to-SK-to-SKI-to-
Iota simulation and the converse faithful Iota-to-lambda embedding independently
in both systems. In particular, some other Coq ports check the finite
certificate surface while the analytic or semantic bridge remains Lean-only;
no blanket parity is claimed.

## Trust and status

- Lean statements are checked by Lean's kernel. Sites using `native_decide`
  deliberately include Lean's native compiler/runtime in their trust boundary
  and remain visible in source. The exhaustive Lean BB2/BB3 shards use ordinary
  kernel `decide`.
- Rocq proofs use kernel checking and documented `vm_compute` or VM conversion.
  The vendored Coq-BB5 snapshots retain their assumptions and local hardening
  notes.
- Generated traces, interval tables, and candidate partitions are accepted
  only through proved checkers or explicit theorem hypotheses.
- Conditional theorems remain explicitly conditional. The A198683 research
  ledger distinguishes semantic proofs, finite data checks, conditional
  results, and heuristic evidence.

## Vendored components

Only [`lib/`](lib/) contains vendored code. `lib/Coq-BB5/BB2`, `BB3`, and
`BB4` come from `ccz181078/Coq-BB5` commit `9142e219...`; their nested READMEs
record provenance and repository-local kernel hardening, and their nested MIT
licenses are retained.

## License

Unless a nested license says otherwise, this repository is available under
the [MIT No Attribution License (MIT-0)](LICENSE).
