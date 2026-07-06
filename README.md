# Lean Proofs

- Created (UTC): 2026-07-04T17:38:16Z
- Repository HEAD: afe87774ab8b2530233ade60ef271aa843b2712b

`src/Lean/` is a repository-local Lake workspace for Lean proofs that are
not owned by one of the more specialized subprojects.

The initial module,
[`LeanProofs/FermatFour.lean`](LeanProofs/FermatFour.lean), records the
`n = 4` special case of Fermat's Last Theorem:

```lean
theorem fermat_four_no_positive_nat_solutions
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 + b ^ 4 ≠ c ^ 4
```

This is the positive-natural-number form of the statement that there are no
positive integers satisfying `a^4 + b^4 = c^4`. The same module also records
the stronger integer descent statement `a^4 + b^4 != c^2`, which is the
classical route to Fermat's `n = 4` case.

[`LeanProofs/FloorSqrtSum.lean`](LeanProofs/FloorSqrtSum.lean) records the
reconstructed blurred formula:

```lean
theorem sum_floor_sqrt_eq (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) =
      Nat.sqrt n * (n + 1)
        - Nat.sqrt n * (Nat.sqrt n + 1)
          * (2 * Nat.sqrt n + 1) / 6
```

Here `Nat.sqrt k` is Lean's natural-number floor square-root, and the
formula is stated as a natural-number identity.

[`LeanProofs/RationalFloorOrbit.lean`](LeanProofs/RationalFloorOrbit.lean)
proves that the orbit starting at `0` under
`q ↦ 1 / (1 - q + 2 * floor q)` visits every nonnegative rational exactly
once:

```lean
theorem rationalFloorOrbit_visits_each_nonnegative_rat_exactly_once
    (q : Rat) (hq : 0 ≤ q) :
    ∃ n : Nat, rationalFloorOrbit n = q ∧
      ∀ m : Nat, rationalFloorOrbit m = q → m = n
```

[`LeanProofs/TinyExponentTower.lean`](LeanProofs/TinyExponentTower.lean)
proves the tiny-exponent power-tower floor identity:

```lean
theorem floor_tinyExponentTower_sub :
    ⌊tinyExponentTower⌋ - (10 : Int) ^ (10 ^ 10 : Nat) =
      (2811012357389 : Int)

theorem floor_expanded_tinyExponentTower_sub :
    Int.floor
      ((10 : ℝ) ^
        ((10 : ℝ) ^
          ((10 : ℝ) ^
            ((10 : ℝ) ^
              ((10 : ℝ) ^ (-((10 ^ 10 : Nat) : ℝ))))))) -
      (10 : Int) ^ (10 ^ 10 : Nat) = (2811012357389 : Int)
```

[`LeanProofs/TrigGoldenRatio.lean`](LeanProofs/TrigGoldenRatio.lean) proves
the trigonometric golden-ratio identity from the degree angles in the image:

```lean
theorem sin_deg9_add_sin_deg21_add_sin_deg39 :
    Real.sin (9 * Real.pi / 180) +
        Real.sin (21 * Real.pi / 180) +
        Real.sin (39 * Real.pi / 180) = φ / √2
```

[`LeanProofs/ArctanSquareIdentity.lean`](LeanProofs/ArctanSquareIdentity.lean)
proves the quadratic arctangent identity:

```lean
theorem arctan_square_identity :
    (2939 : ℝ) * Real.arctan (2 : ℝ) ^ 2 -
      1250 * Real.arctan (3 : ℝ) ^ 2 -
      252 * Real.arctan (4 : ℝ) ^ 2 -
      360 * Real.arctan (5 : ℝ) ^ 2 -
      870 * Real.arctan (7 : ℝ) ^ 2 +
      450 * Real.arctan (8 : ℝ) ^ 2 +
      84 * Real.arctan (13 : ℝ) ^ 2 +
      330 * Real.arctan (18 : ℝ) ^ 2 -
      210 * Real.arctan (21 : ℝ) ^ 2 +
      147 * Real.arctan (38 : ℝ) ^ 2 -
      210 * Real.arctan (47 : ℝ) ^ 2 = 0
```

[`LeanProofs/A198683.lean`](LeanProofs/A198683.lean) defines OEIS A198683
semantically as the number of distinct principal complex-power values obtained
from all binary parenthesizations of `i^i^...^i`. It proves the accepted values
through `n = 6` directly over `ℂ`, with public theorems
`a198683_one` through `a198683_six`. Two companion certificate modules record
finite checked data from the local A198683 corpus:
[`LeanProofs/A198683Schoenfield.lean`](LeanProofs/A198683Schoenfield.lean)
checks the Schoenfield labels through `n = 11`,
[`LeanProofs/A198683SchoenfieldRows.lean`](LeanProofs/A198683SchoenfieldRows.lean)
reconstructs the `n = 7` through `n = 10` labels from the source table's
Count/Match rows, and
[`LeanProofs/A198683N12Probe.lean`](LeanProofs/A198683N12Probe.lean) checks
that the strict `n = 12` candidate table has 2925 classes among 5139
candidates and that the documented probe split refines it to 2926 classes.
The latter is intentionally a data-integrity theorem, not a semantic proof of
`a198683 12 = 2926`.

[`LeanProofs/Nicod.lean`](LeanProofs/Nicod.lean) formalizes the
Sheffer-stroke/NAND language for Nicod's one-axiom propositional calculus,
including the exact axiom schema

```text
(p ↑ (q ↑ r)) ↑ ((u ↑ (u ↑ u)) ↑ ((w ↑ q) ↑ ((p ↑ w) ↑ (p ↑ w))))
```

and the exact rule `(p ↑ (q ↑ r)), p ⊢ r`.  Lean uses `↑` for coercions, so
the formal notation uses `⊼` for the same NAND connective.  The module proves
that NAND expresses the usual classical connectives, that the Nicod axiom is
classically valid, that the rule is classically sound, and therefore that every
formula derivable in the one-axiom/one-rule calculus is a classical tautology.
It also derives the three Lukasiewicz Hilbert axiom schemas and standard modus
ponens for NAND-defined implication, formalized as
`Formula.implementsLukasiewicz`, so every theorem of that standard classical
propositional calculus has a Nicod proof.

[`LeanProofs/WolframBoolean.lean`](LeanProofs/WolframBoolean.lean)
formalizes Wolfram's single Sheffer-stroke equation

```text
((a ↑ b) ↑ c) ↑ (a ↑ ((a ↑ c) ↑ a)) = c
```

and Meredith's two-axiom Sheffer-stroke system.  Since Lean uses `↑` for
coercions, the formal notation uses `⊙`.  A small equational checker in
[`LeanProofs/EquationalLogic.lean`](LeanProofs/EquationalLogic.lean), applied
to generated certificates in
[`LeanProofs/WolframBooleanCertificates.lean`](LeanProofs/WolframBooleanCertificates.lean),
proves over an arbitrary carrier with one binary operation that Wolfram's
equation derives the standard three Sheffer axioms, and that Meredith's pair
derives Wolfram's equation.  A second generated certificate in
[`LeanProofs/WolframBooleanHuntingtonCertificates.lean`](LeanProofs/WolframBooleanHuntingtonCertificates.lean)
derives Huntington's three-equation Boolean-algebra basis for the operations
`¬a = a ⊙ a` and `a ∨ b = ¬a ⊙ ¬b`.  The public entry points are:

```lean
theorem wolfram_derives_sheffer_axioms {α : Type u} (op : α → α → α)
    (h : WolframAxiom op) : ShefferAxioms op

theorem meredith_derives_wolfram_axiom {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) : WolframAxiom op

theorem meredith_derives_sheffer_axioms {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) : ShefferAxioms op

theorem wolfram_derives_huntington_axioms {α : Type u} (op : α → α → α)
    (h : WolframAxiom op) :
    HuntingtonAxioms (strokeJoin op) (strokeCompl op)

theorem meredith_derives_huntington_axioms {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) :
    HuntingtonAxioms (strokeJoin op) (strokeCompl op)
```

The same module separately proves that, on the two-element Boolean algebra,
Wolfram's equation and Meredith's pair each have exactly the two Sheffer
truth-table models, NAND and its dual NOR; consequently any Boolean binary
operation satisfying either system expresses every ordinary classical
connective.  It also includes a native-checked finite lower-bound certificate:
for every canonical single equation with at most five primitive
binary-operation occurrences that is true in the Boolean Sheffer tables, one of
30 explicitly listed finite algebras satisfies that short equation while
violating Wolfram's axiom.  Thus no such shorter equation can axiomatize the
same equational class, while Wolfram's equation uses six operation symbols.

## Building

```powershell
cd src/Lean
lake exe cache get
lake build
```
