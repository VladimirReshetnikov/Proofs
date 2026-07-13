# Quantifier commutation in Rocq/Coq

This dependency-free development constructively proves that adjacent `forall`
quantifiers commute and adjacent `exists` quantifiers commute. It also gives
finite, same-type relations witnessing failure of commutation for nested
`no_exists` (defined as `~ exists`) and Rocq's standard `exists!` quantifier.

The `exists!` countermodel uses the three-element relation
`{(a,a), (b,b), (b,c)}`: its rows are `{a}`, `{b,c}`, and `{}`, while its
columns are `{a}`, `{b}`, and `{b}`. Thus exactly one row, but all three
columns, are singletons.

Here “adjacent `no_exists` quantifiers” means genuine nesting,
`~ exists x, (~ exists y, R x y)`. It is not the flattened notation
`~ exists x, exists y, R x y`; the latter contains only one negation and its
two ordinary existential binders do commute.

From this directory, check everything with:

```powershell
coqc -Q . QuantifierCommutation Commutation.v
coqc -Q . QuantifierCommutation Counterexamples.v
coqc -Q . QuantifierCommutation Audit.v
coqchk -silent -Q . QuantifierCommutation QuantifierCommutation.Commutation QuantifierCommutation.Counterexamples QuantifierCommutation.Audit
```
