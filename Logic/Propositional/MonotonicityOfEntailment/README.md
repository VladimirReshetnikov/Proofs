# Monotonicity of entailment

Machine-checked Lean 4 and Rocq/Coq proofs of the weakening rule described in
[Monotonicity of entailment](https://en.wikipedia.org/wiki/Monotonicity_of_entailment):

```text
       Γ ⊢ C
    -----------
     Γ, A ⊢ C
```

The development proves the stronger statement that `Γ ⊢ C` and `Γ ⊆ Δ`
imply `Δ ⊢ C`.  It uses the shared [propositional natural-deduction
calculus](../NaturalDeduction/),
parameterized by additional zero-premise axioms:

- intuitionistic entailment has no additional axioms;
- classical entailment adds the excluded-middle schema `P ∨ ¬P`.

Weakening is proved constructively for the parameterized calculus and then
specialized to both logics.  Thus the formalization also records why the two
proofs are the same: monotonicity is a structural property and does not depend
on excluded middle.

## Checking

From the repository root:

```powershell
lake --dir Logic/Propositional/MonotonicityOfEntailment/Lean build
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction Logic/Propositional/NaturalDeduction/Coq/Calculus.v
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction -Q Logic/Propositional/MonotonicityOfEntailment/Coq MonotonicityOfEntailment Logic/Propositional/MonotonicityOfEntailment/Coq/MonotonicityOfEntailment.v
```
