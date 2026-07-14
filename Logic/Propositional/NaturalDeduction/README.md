# Propositional natural deduction

Dependency-free syntax and natural-deduction rules shared by the Lean 4 and
Rocq/Coq developments of classical and intuitionistic structural logic.

The calculus is parameterized by additional zero-premise axiom schemas.
Intuitionistic logic supplies none; classical logic supplies excluded middle
`P ∨ ¬P`.  All introduction and elimination rules—including intuitionistic
falsity elimination—are otherwise shared.

The theorem developments using this foundation are:

- [`../MonotonicityOfEntailment/`](../MonotonicityOfEntailment/);
- [`../PrincipleOfExplosion/`](../PrincipleOfExplosion/).

This calculus models standard intuitionistic logic rather than minimal logic:
minimal logic omits falsity elimination and therefore does not validate the
principle of explosion.

## Checking

```powershell
lake --dir Logic/Propositional/NaturalDeduction/Lean build
coqc -Q Logic/Propositional/NaturalDeduction/Coq NaturalDeduction Logic/Propositional/NaturalDeduction/Coq/Calculus.v
```

