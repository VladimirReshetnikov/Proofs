# Presburger arithmetic is decidable

This directory formalizes Cooper quantifier elimination for first-order
arithmetic over the integers with addition, order, equality, congruence, and
Boolean connectives. Multiplication is restricted to multiplication by an
integer constant, as required for Presburger arithmetic.

## Lean

The Lean development is an executable end-to-end decision procedure:

1. `Syntax.lean` defines affine expressions, divisibility atoms,
   quantifier-free formulae, and first-order formulae (universal
   quantification is the derived operation `¬∃¬`).
2. `NormalForm.lean` computes disjunctive normal form, including constructive
   negation of inequalities and divisibility atoms.
3. `Cooper.lean` proves the periodic residue and finite-interval lemmas at the
   heart of Cooper elimination.
4. `Elimination.lean` normalizes coefficients and proves one-variable
   elimination correct.
5. `Decision.lean` recursively eliminates every quantifier and defines the
   Boolean decision procedure `Formula.decideSentence`.

The advertised executable decision definition is

```lean
PresburgerArithmetic.Formula.presburgerArithmetic_decidable
```

and `Audit.lean` prints its axiom dependencies together with the central
correctness theorems.

Focused build:

```powershell
lake --dir Logic/PresburgerArithmetic/Lean build
```

## Rocq/Coq

`Cooper.v` gives an independent constructive proof of the decisive normalized
one-variable Cooper step. For a decidable predicate `P` periodic modulo a
positive `m`, and finite lists of lower and upper bounds, it computes whether

```coq
exists x, all_lower los x /\ all_upper his x /\ P x
```

holds. `cooper_finite_criterion` proves that this unbounded existential is
equivalent to a finite residue search (or finitely many bounded searches), and
`cooper_step_decidable` packages the resulting executable sum-type decision.
This is exactly the non-Boolean step iterated by the Lean quantifier
eliminator; the Coq development independently checks its mathematical core.

Focused check:

```powershell
coqc -Q Logic/PresburgerArithmetic/Coq PresburgerArithmetic Logic/PresburgerArithmetic/Coq/Cooper.v
coqc -Q Logic/PresburgerArithmetic/Coq PresburgerArithmetic Logic/PresburgerArithmetic/Coq/Audit.v
```

The decision procedures are executable and neither development uses `sorry`,
`Admitted`, or a custom arithmetic oracle. The Lean audit exposes only Lean's
standard logical axioms used by mathlib; the Coq audit is closed under the
global context.
