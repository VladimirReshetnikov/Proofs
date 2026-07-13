# Intuitionistic logic is not finitely truth-valued

Machine-checked Lean 4 and Rocq/Coq proofs of Gödel's 1932 theorem that no
single finite deterministic truth-functional matrix characterizes
intuitionistic propositional logic (IPC).  In particular, IPC is not a
three-valued logic with deterministic truth tables for “false”, “undecided”,
and “true”.

The statement is deliberately stronger than ruling out one familiar set of
three-valued tables.  A matrix may have arbitrary total operations for
`false`, `and`, `or`, and `implies`, an arbitrary set of designated values,
and arbitrary names for its finitely many values.  If all IPC theorems are
valid in such a matrix, some non-theorem is valid there too.

## The separating formula

For `n` truth values, take `n + 1` atoms `p₀, …, pₙ` and define

```text
Gₙ = ⋁  ((pᵢ → pⱼ) ∧ (pⱼ → pᵢ)).
     i<j
```

Every valuation into `n` values assigns the same value to two atoms.  If those
atoms are `pᵢ` and `pⱼ`, collapse `pⱼ` to `pᵢ` throughout `Gₙ`.  The renamed
formula is an IPC theorem: its selected disjunct is the derivable
`(pᵢ → pᵢ) ∧ (pᵢ → pᵢ)`.  Truth-functionality and equality of the two atomic
values make the original and renamed formulas evaluate identically.  Thus
every finite matrix that is sound for IPC validates `Gₙ`.

The converse fails in a concrete Kripke model.  Put a root below `n + 1`
incomparable leaves, and force `pᵢ` only at leaf `i`.  For each `i < j`, leaf
`i` refutes `pᵢ → pⱼ`; consequently the root refutes every biconditional and
therefore refutes `Gₙ`.  The formalized Kripke soundness theorem then gives
`IPC ⊬ Gₙ`.

Combining the two halves proves that every finite IPC-sound deterministic
matrix is incomplete.  Specializing to three values gives four atoms and the
six disjuncts for pairs `01`, `02`, `03`, `12`, `13`, and `23`.

## What the theorem does and does not say

The result excludes one **finite deterministic truth-functional matrix** whose
valid formulas are exactly the IPC theorems.  It does not exclude:

- Kripke, topological, categorical, proof, or realizability semantics;
- semantics in infinite Heyting algebras;
- classes of finite Heyting algebras of unbounded size;
- non-deterministic or valuation-restricted finite semantics;
- “undecided” as informal epistemic language.

The mathematical point is that a single undifferentiated third value cannot
retain the branching, future-dependent information used by intuitionistic
implication.  The formalized three-element Heyting chain illustrates this
concretely: it validates `(P → Q) ∨ (Q → P)`, while a two-branch Kripke model
shows that IPC does not prove that formula.

## Formalization map

The Lean development separates syntax/renaming, the constructive pigeonhole
argument, arbitrary matrices, Kripke soundness, the final theorem, and the
concrete `H₃` example into individual modules.  The Coq development proves the
same results in `FiniteMatrixNoncharacterizability.v`, with the `H₃` example in
`ThreeValuedExample.v`.  Both audit modules expose the unconditional finite-
and three-valued results and print their kernel assumptions.

## Sources

- Kurt Gödel, [*On the intuitionistic propositional calculus* (1932)](https://academic.oup.com/book/55022/chapter/422805490), pp. 223–225 in the collected works.
- The [Stanford Encyclopedia of Philosophy's account of Gödel's finite-value theorem](https://plato.stanford.edu/entries/goedel/#IntProLogNotFinVal) states the characteristic-matrix result and records the same pairwise-equivalence formula.

## Checking

From the repository root:

```powershell
lake --dir Logic/Propositional/FiniteMatrixNoncharacterizability/Lean build

coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction `
  Logic/Propositional/NaturalDeduction/Coq/Calculus.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction `
  -Q Logic/Propositional/FiniteMatrixNoncharacterizability/Coq FiniteMatrixNoncharacterizability `
  Logic/Propositional/FiniteMatrixNoncharacterizability/Coq/FiniteMatrixNoncharacterizability.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction `
  -Q Logic/Propositional/FiniteMatrixNoncharacterizability/Coq FiniteMatrixNoncharacterizability `
  Logic/Propositional/FiniteMatrixNoncharacterizability/Coq/ThreeValuedExample.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction `
  -Q Logic/Propositional/FiniteMatrixNoncharacterizability/Coq FiniteMatrixNoncharacterizability `
  Logic/Propositional/FiniteMatrixNoncharacterizability/Coq/Audit.v
```

The audit modules print the assumptions of the main finite- and three-valued
theorems.  Neither development uses an admitted theorem or a classical-logic
axiom.
