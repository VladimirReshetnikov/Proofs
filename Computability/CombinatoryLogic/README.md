# Combinatory logic: SK, SKI, and Iota universality

This project proves in Lean 4 and Rocq/Coq that the pure SK, SKI, and
one-combinator Iota calculi are computationally universal.  It includes a
scope-safe untyped lambda calculus, a verified bracket-abstraction compiler,
Chris Barker's compiler from SKI to Iota, and a faithful operational embedding
of Iota back into untyped lambda calculus.

## The checked theorem

The universal reference model is the closed untyped lambda calculus with weak
contextual beta reduction.  Both developments use intrinsically scoped terms,
capture-avoiding substitution, and an occurs-aware bracket-abstraction
compiler into pure SK.  They prove exact preservation of application and map
every beta contraction to one or more SK contractions.  The positive and
reflexive-transitive closures are both preserved.

Pure SK embeds constructor-for-constructor into SKI.  Conversely, the standard
SKI-to-SK compiler replaces `I` by `S K K`.  This compiler is intentionally not
claimed to be injective: primitive `I` and the literal SKI term `S K K` have
the same image, and both developments prove this collision explicitly.

The pure Iota target has exactly one leaf, `ι`, and binary application.  Its
operational semantics uses a separate runtime syntax with auxiliary `S` and
`K` nodes and the context-closed rules

```text
ι x       --> x S K
K x y     --> x
S x y z   --> x z (y z).
```

The auxiliary nodes are runtime values, not Iota source constructors.  This
separation makes it impossible to hide `S` or `K` in a purportedly pure Iota
program.

Both proof developments define the total homomorphic compiler

```text
I    |--> ι ι
K    |--> ι (ι (ι ι))
S    |--> ι (ι (ι (ι ι)))
A B  |--> compile(A) compile(B)
```

and prove that it is injective and simulates every context-closed SKI
contraction by one or more Iota runtime contractions.  Both
reflexive-transitive and positive closures are preserved, the compiler has a
linear size bound, and a compiled SKI omega term has a checked nonempty
reduction cycle.

The converse embedding interprets the complete Iota runtime by the standard
closed lambda terms

```text
K  |--> lambda x. lambda y. x
S  |--> lambda x. lambda y. lambda z. x z (y z)
ι  |--> lambda f. f S K
A B |--> encode(A) encode(B).
```

Both developments prove the exact one-, two-, and three-beta-step head traces
for `ι`, `K`, and `S`, respectively.  They lift those traces through both
application contexts, preserve reflexive-transitive and positive closures,
and prove that the runtime translation is syntactically injective.  Restricting
along the pure-source inclusion therefore gives an injective,
application-homomorphic operational embedding of pure Iota into closed weak
lambda terms.

The three headline witnesses package concrete, application-homomorphic
compilers whose one-step simulations are positive:

- closed weak lambda to pure SK;
- closed weak lambda through SK to SKI;
- closed weak lambda through SK and SKI to pure Iota.

Thus SK, SKI, and Iota inherit Turing completeness from the standard untyped
lambda calculus.  This is a fully checked version of the conventional
expressiveness proof, not merely the three closed folklore identities.

Together, the two directions close the expressiveness loop between pure Iota
and closed weak lambda calculus.  They are forward operational simulations;
the development does not claim that the chosen compilers are mutual syntactic
inverses, reduction-reflecting, or fully abstract.

The exact boundary remains explicit: the repository does not separately
formalize a Turing-machine or partial-recursive-function compiler into the
lambda calculus, nor does forward simulation alone prove a many-one reduction
for normalization.  No such stronger claim is hidden behind the theorem name.

## Layout

- [`Lean/`](Lean/) contains the Lean 4 definitions, simulation proof, and
  assumption audit.
- [`Coq/`](Coq/) contains the independent Rocq/Coq development and audit.

The two developments intentionally share the mathematical architecture, not
proof artifacts or generated certificates.

## Checking

From the repository root, keep Lean's worker pool disabled as required by the
repository build policy:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +CombinatoryLogic
```

Check the Rocq files sequentially (GNU Make is not required):

```powershell
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/Reduction.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/Lambda.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/SKPolynomial.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/SKI.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/SK.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/Iota.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/SKIToSK.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/TuringCompleteness.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/LambdaToSK.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/IotaToLambda.v
coqc -Q Computability/CombinatoryLogic/Coq CombinatoryLogic Computability/CombinatoryLogic/Coq/Audit.v
coqchk -silent -o -Q Computability/CombinatoryLogic/Coq CombinatoryLogic CombinatoryLogic.LambdaToSK
coqchk -silent -o -Q Computability/CombinatoryLogic/Coq CombinatoryLogic CombinatoryLogic.IotaToLambda
```

The Lean `#print axioms` audit exposes only Lean's standard `propext` and
`Quot.sound` principles.  The scoped substitution and Iota-to-lambda proofs
use `propext` through standard simplification/extensionality infrastructure;
the bracket compiler and its transported witnesses additionally use
`Quot.sound`.  The core SK/SKI/Iota runtime simulations and their direct omega
cycles remain axiom-free.  The Rocq `Print Assumptions` and `coqchk` audits are
closed with `Axioms: <none>`.  Neither development adds a project-specific
axiom, admitted obligation, or unsafe reduction rule.

## Sources

- Chris Barker, [*Iota and Jot: the simplest languages?*](https://web.archive.org/web/20160823182917/http://semarch.linguistics.fas.nyu.edu/barker/Iota/), especially the CL-to-Iota compiler and its three base cases.
- [Iota and Jot](https://en.wikipedia.org/wiki/Iota_and_Jot), for the modern syntax summary and the same `I`, `K`, and `S` encodings.
