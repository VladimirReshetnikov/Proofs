# Principle of explosion

Machine-checked Lean 4 and Rocq/Coq proofs of the
[principle of explosion](https://en.wikipedia.org/wiki/Principle_of_explosion)
for intuitionistic and classical propositional logic.

The formalization proves all of the standard presentations, for arbitrary
formulas `P` and `Q` and any background context `Γ`:

```text
Γ ⊢ ⊥                      implies  Γ ⊢ Q
Γ ⊢ P  and  Γ ⊢ ¬P         imply    Γ ⊢ Q
P, ¬P, Γ ⊢ Q
P ∧ ¬P, Γ ⊢ Q
Γ ⊢ (P ∧ ¬P) → Q
```

The first statement is the falsity-elimination rule (`⊥E`) built into standard
intuitionistic natural deduction.  The exact Wikipedia sequent `P, ¬P ⊢ Q` is
derived: implication elimination applied to `P` and `P → ⊥` first produces
`⊥`, after which `⊥E` produces `Q`.

The proof is established once for the shared parameterized calculus and then
specialized to:

- intuitionistic logic, with no additional axiom schemas;
- classical logic, with excluded middle as an additional object-level schema.

Excluded middle is not used by explosion.  Accordingly, neither Lean nor Coq
imports ambient classical logic.  The result does not extend to minimal or
paraconsistent logic, whose proof systems omit or restrict a required rule.

## Checking

From the repository root:

```powershell
lake --dir Logic/Propositional/PrincipleOfExplosion/Lean build
lake --dir Logic/Propositional/PrincipleOfExplosion/Lean build +PrincipleOfExplosion.Audit

coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction Logic/Propositional/NaturalDeduction/Coq/Calculus.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction -Q Logic/Propositional/PrincipleOfExplosion/Coq PrincipleOfExplosion Logic/Propositional/PrincipleOfExplosion/Coq/PrincipleOfExplosion.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction -Q Logic/Propositional/PrincipleOfExplosion/Coq PrincipleOfExplosion Logic/Propositional/PrincipleOfExplosion/Coq/Audit.v
```

