# Combinatory Logic (Lean)

This Lean 4 development formalizes the SKI and pure SK combinator calculi, the
pure one-leaf `ι` source language, its separate auxiliary runtime with rule
`ι x ↦ x S K`, and Barker's canonical compiler

```text
I ↦ ι ι
K ↦ ι (ι (ι ι))
S ↦ ι (ι (ι (ι ι)))
```

Application is compiled homomorphically.  Purity is enforced by the compiler's
result type, and the compiler is injective.  Every SKI step is simulated by
**one or more** runtime steps, and both reflexive-transitive and positive
closures are preserved.  The positive theorem rules out simulation by
reflexivity alone; the compiled SKI omega term also has a checked nonempty
reduction cycle.

`Compiler.faithful_ski_embedding` instantiates `FaithfulSKIEmbedding`: pure
Iota contains an injective encoding that preserves every finite SKI
reduction.  The stronger `step_simulation` and `stepsPlus_simulation` theorems
retain explicit positive traces.

The SKI-to-SK compiler uses `I ↦ S K K`, preserves positive and finite
reductions, and grows syntax size by at most a factor of five.  Its unavoidable
syntax collision between primitive `I` and literal `S K K` is proved explicitly;
the reverse SK-to-SKI inclusion is injective and preserves both reduction
closures.  Both calculi include checked omega cycles.

Finally, a scope-safe untyped lambda calculus (`Term n`, with `Fin n`
variables) compiles to pure SK through occurs-aware bracket abstraction.  The
compiler commutes with capture-avoiding substitution, and every weak beta step
maps to a nonempty SK reduction.  `sk_turing_complete` packages the concrete
compiler with its homomorphic application law and positive step simulation;
`sk_simulates_weak_lambda` is the corresponding finite-reduction theorem.
The same positive compiler is composed with the SK-to-SKI inclusion and the
SKI-to-iota compiler to obtain `ski_turing_complete` and
`iota_turing_complete`.  The lambda omega cycle is transported through both
compositions as a checked nonempty cycle.

In the reverse direction, `IotaToLambda.encodeRuntimeAt` gives the auxiliary
iota runtime its canonical closed lambda interpretation
`K = λx. λy. x`, `S = λx. λy. λz. x z (y z)`, and
`ι = λx. x S K`.  Application is preserved by definitional equality, and the
runtime `ι`, `K`, and `S` heads are simulated by exactly one, two, and three
weak beta steps.  Contextual steps and both finite-reduction closures are
preserved.  Restriction along the pure-source inclusion is compatible on the
nose and injective; `faithful_iota_lambda_embedding` packages this
compositional, one-way operational simulation without claiming reduction
reflection or full abstraction.  The `encodePure_*` and `encodeRuntime_*`
aliases mirror the independent Coq theorem surface.

The assumption audit reports the standard Lean axiom `propext` for the scoped
substitution lemmas and this iota-to-lambda embedding (including its head and
closure theorems).  No custom axioms are introduced.  The lower-level
SK/SKI/iota runtime simulations remain separately visible as axiom-free.

The headline boundary is explicitly weak untyped lambda calculus; this module
does not separately formalize a Turing-machine or partial-recursive-function
compiler into lambda terms.

From the repository root, after registering the `CombinatoryLogic` source
directory in `lakefile.toml`, build with:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +CombinatoryLogic
```
