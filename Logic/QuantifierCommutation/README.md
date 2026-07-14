# Commutation of adjacent quantifiers

Machine-checked Lean 4 and Rocq/Coq proofs that adjacent universal quantifiers
commute and adjacent existential quantifiers commute, together with explicit
finite counterexamples for “there does not exist” (`∄`) and “there exists
exactly one” (`∃!`).  Every proof is constructive.

For arbitrary types `A`, `B` and relation `R : A → B → Prop`, the positive
laws are

```text
(∀ x, ∀ y, R x y) ↔ (∀ y, ∀ x, R x y)
(∃ x, ∃ y, R x y) ↔ (∃ y, ∃ x, R x y).
```

The first law merely reverses the order in which two arbitrary arguments are
accepted.  The second merely reverses the order in which two witnesses are
packaged.  Neither proof uses excluded middle.

## Why nested `∄` does not commute

Here `∄ x, P x` means `¬ ∃ x, P x`, so the adjacent expression is parsed as

```text
∄ x, (∄ y, R x y)  =  ¬ ∃ x, (¬ ∃ y, R x y).
```

On the two-element type `{a, b}`, let `R x y` hold exactly when `y = a`:

| `R` | `y = a` | `y = b` |
| --- | ---: | ---: |
| `x = a` | ✓ | · |
| `x = b` | ✓ | · |

Every row contains a witness, so `∄ x, ∄ y, R x y` holds.  Column `b` is
empty, so `∄ y, ∄ x, R x y` does not hold.  Thus swapping the adjacent binders
changes the proposition.  Classically these two nestings resemble
`∀ x, ∃ y, R x y` and `∀ y, ∃ x, R x y`, but the formal counterexample itself
is intuitionistic.

This is deliberately different from the flattened abbreviation
`∄ x y, R x y` when that notation means the single negation
`¬ ∃ x, ∃ y, R x y`: the two ordinary existential binders inside that block
do commute.

## Why nested `∃!` does not commute

On `{a, b, c}`, use the relation

| `R` | `y = a` | `y = b` | `y = c` |
| --- | ---: | ---: | ---: |
| `x = a` | ✓ | · | · |
| `x = b` | · | ✓ | ✓ |
| `x = c` | · | · | · |

Exactly one row—row `a`—contains exactly one related element.  Hence
`∃! x, ∃! y, R x y` holds.  All three columns contain exactly one related
element, so there is not exactly one such column; `∃! y, ∃! x, R x y` fails.

Nested unique existence is likewise different from saying that there is a
unique pair `(x, y)` satisfying `R`.

The Lean and Coq audit modules check both positive equivalences, both concrete
one-way separations, and the resulting failures of commutativity.

Dependency-free Lean core does not provide `∃!` notation, so the Lean port
defines its canonical meaning explicitly as
`∃ x, P x ∧ ∀ y, P y → y = x`.  The Coq port uses Coq's standard `exists!`;
the audited statements therefore have the same semantics.

## Checking

From the repository root:

```powershell
lake --dir Logic/QuantifierCommutation/Lean build

coqc -Q Logic/QuantifierCommutation/Coq QuantifierCommutation `
  Logic/QuantifierCommutation/Coq/Commutation.v
coqc -Q Logic/QuantifierCommutation/Coq QuantifierCommutation `
  Logic/QuantifierCommutation/Coq/Counterexamples.v
coqc -Q Logic/QuantifierCommutation/Coq QuantifierCommutation `
  Logic/QuantifierCommutation/Coq/Audit.v
coqchk -silent -Q Logic/QuantifierCommutation/Coq QuantifierCommutation `
  QuantifierCommutation.Commutation QuantifierCommutation.Counterexamples `
  QuantifierCommutation.Audit
```

Neither development contains an admitted theorem or invokes a classical-logic
axiom.
