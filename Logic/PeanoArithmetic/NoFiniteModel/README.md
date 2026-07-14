# Peano arithmetic has no finite model

Machine-checked Lean 4 and Rocq/Coq proofs that every model of Peano
arithmetic has an infinite carrier.  Both developments reuse the PA model
interfaces already defined by the repository's PA/HF formalization.

Finiteness is constructive and explicit: a carrier `A` is finite when there
are mutually inverse maps between `A` and `Fin n` (Lean) or `Fin.t n` (Coq)
for some natural number `n`.  This includes `n = 0`; a PA model cannot have an
empty carrier because it contains the distinguished element zero.

## Proof

Let `S : A → A` be successor.  PA supplies the two facts

```text
S a = S b  →  a = b
S a ≠ 0.
```

Every injective endomap of a finite carrier is surjective.  Consequently, if
`A` were finite, surjectivity of `S` would provide an `a` with `S a = 0`,
contradicting the second axiom.

Nothing else from PA is needed: the proof does not use addition,
multiplication, their recursion equations, or induction.  The result already
holds for the zero-successor fragment shared with Robinson arithmetic.  The
argument is constructive; it does not use excluded middle or choice.

The conclusion is only that PA has no **finite** model.  It does not make
first-order PA categorical and does not rule out nonstandard infinite models.

## Formalization map

- Lean's `FiniteTypes.lean` defines `FinEquiv`, the proposition-valued
  `IsFiniteType`, and a self-contained induction proving that an injective
  endomap of `Fin n` is surjective.  `Theorem.lean` applies it to
  `SetTheory.PA.Model`; `Examples.lean` rules out a PA structure on every
  concrete `Fin n`.
- Coq's `NoFiniteModel.v` defines the analogous `FinitePresentation` and uses
  the constructive `Endo_Injective_Surjective` theorem from `FinFun`.  It
  provides corollaries for both PA interfaces exposed by `PAHF.v`: the
  top-level `PAModel` and the nested `PA.Model`.
- Both audit modules print the assumptions of the generic finite-endomap
  lemma and all PA corollaries.  Coq reports them closed under the global
  context.  Lean reports only `propext`, inherited from its core `Fin` lemmas;
  no classical choice or excluded-middle axiom occurs.

## Checking

From the repository root:

```powershell
lake --dir Logic/PeanoArithmetic/NoFiniteModel/Lean build
lake --dir Logic/PeanoArithmetic/NoFiniteModel/Lean env lean `
  NoFiniteModel/Audit.lean
```

Once the existing `FirstOrder` and `PAHF` Coq dependencies have been built:

```powershell
coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NoFiniteModel/Coq NoFinitePAModel `
  Logic/PeanoArithmetic/NoFiniteModel/Coq/NoFiniteModel.v
coqc -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NoFiniteModel/Coq NoFinitePAModel `
  Logic/PeanoArithmetic/NoFiniteModel/Coq/Audit.v
coqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/NoFiniteModel/Coq NoFinitePAModel `
  NoFinitePAModel.NoFiniteModel NoFinitePAModel.Audit
```
