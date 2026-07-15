# Peano arithmetic is undecidable

This project proves that the set of syntactic theorems of first-order Peano
arithmetic is not a computable predicate. Here “decidable” has its
computability-theoretic meaning: there is no total computable Boolean function
which, given an encoded arithmetic sentence, says exactly whether that
sentence has a formal PA derivation.

This is different from saying that one particular sentence is independent of
PA. The theorem concerns the algorithmic decision problem for the entire set
of PA theorems.

## Mathematical reduction

The two formalizations use equivalent standard routes.

- The Lean proof starts with mathlib's noncomputability theorem for the
  halting problem. The arithmetization theorem from
  FormalizedFormalLogic/Foundation produces one unary arithmetic formula
  `H(x)` representing that recursively enumerable predicate. For every
  program code `n`, Sigma-1 completeness and standard-model soundness give

  ```text
  program n halts  <->  PA proves H(n).
  ```

  Thus even theoremhood for the single effective family `H(0), H(1), ...` is
  not computable. The public theorem is
  `PAUndecidable.peano_arithmetic_theoremhood_not_decidable`.

- The Coq proof uses the fully mechanized DPRM theorem in the Coq Library of
  Undecidability. A Diophantine equation is translated to the existential PA
  sentence asserting that it has a solution. PA proves the sentence from a
  concrete solution, while soundness in the standard natural-number model
  gives the converse. Since Hilbert's tenth problem is undecidable, PA
  deduction is undecidable. The public theorem is
  `peano_arithmetic_theoremhood_not_decidable`.

Both developments concern the ordinary language with zero, successor,
addition, multiplication, and equality, together with the full first-order PA
induction schema. Neither proof assumes PA's consistency: soundness follows
externally from the standard natural-number model.

## Dependencies

The Lean project uses the repository submodule
`lib/FormalizedFormalLogic-Foundation`, pinned at commit
`484e34cbcbdfb896f6161cbfd2c74788becff00a`, and a Lake lockfile pinning its
mathlib dependency. Foundation is registered directly as a source library so
the proof build does not load Foundation's unrelated documentation tooling.

The Rocq project uses the repository submodule
`lib/Coq-Library-Undecidability-current`, pinned to the upstream Rocq 9.2
revision `c7257b736763d7b2bc3bd25ac47d5fb7ce749c9c`. Initialize submodules
before building a fresh clone. Its declared toolchain is Rocq Core 9.2.0 with
Rocq Stdlib 9.1.0.

## Verification

Lean:

```powershell
$env:LEAN_NUM_THREADS='0'
lake --dir Logic/PeanoArithmetic/Undecidable/Lean build
```

Rocq:

```powershell
Push-Location Logic/PeanoArithmetic/Undecidable/Coq
rocq c -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAUndecidable.v
rocq c -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  Audit.v
rocq check -Q ../../../../lib/Coq-Library-Undecidability-current/theories Undecidability `
  PAUndecidable Audit
Pop-Location
```

The audit modules print the assumptions of the headline results.
