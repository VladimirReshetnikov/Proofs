# Machine-Checkable Proofs

- Created (UTC): 2026-07-04T17:38:16Z
- Repository HEAD: not pinned; see git history for the exact checkpoint commit

`src/Lean/` is the repository home for machine-checkable proofs and the
research artifacts that support them. Most checked proof modules here are
Lean, but the scope is intentionally broader: Rocq/Coq developments and
associated research code in Python, Wolfram Language, or other languages
belong here when they are part of producing or auditing formal mathematical
certificates.

The root of this directory is a Lake/mathlib workspace named `LeanProofs`.
Additional proof-oriented subject corpora live alongside it:

- [`LeanProofs/`](LeanProofs/) — the root Lean 4 proof library, pinned to
  Lean `4.31.0` and mathlib `v4.31.0`.
- [`Oeis/A198683/`](Oeis/A198683/README.md) — the local research corpus for
  the OEIS A198683 formalization, including Python/Wolfram computations,
  source snapshots, generated data, and the wave reports around the disputed
  `A198683(12)` value.
- [`SetTheory/`](SetTheory/README.md) — the Rocq/Coq and independent Lean 4
  proof of the deductive equivalence between Vladimir's Closure
  axiomatization and ZF, plus the accompanying article.

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

[`LeanProofs/PowTower.lean`](LeanProofs/PowTower.lean) is the shared lexical
layer for the power-tower OEIS formalizations.  It defines the one-token
binary parenthesization syntax `PowTower.Expr`, its canonical semantic
`valueSet`/`valueCard`, and proved computation-oriented bridges such as
`valueSet_eq_recursiveValueSet`, `valueCard_eq_recursiveValueSet_ncard`, and
the finite/memoized recursive finite-set variants used by decidable
interpretations.  Two shared devices keep the per-sequence modules thin:
`eq_recursiveValueSet_of_recurrence` lets any local recursion of the standard
split shape inherit the equivalence with the canonical lexical definition
without repeating the strong induction, and the hash-set fast-level machinery
(`fastLevelFromTable`/`fastLevelTable`/`fastCountsThrough`) is a proved
executable fast path whose duplicate-free rows are shown to enumerate exactly
`recursiveValueFinset`, so large certificate rows never rely on an unproved
backend.  The module also carries the shared size-`1..5` parenthesization
enumeration certificates reused by the sequence modules.

[`LeanProofs/A000081.lean`](LeanProofs/A000081.lean) defines OEIS A000081
from the exponent-function description itself: it enumerates all legal binary
parenthesizations of `x^x^...^x`, interprets them as functions
`{x : ℝ // 0 < x} -> {x : ℝ // 0 < x}`, and counts the resulting semantic
function set.  It proves the listed values through `n = 5` directly from that
definition:

```lean
theorem a000081_zero : a000081 0 = 0
theorem a000081_one : a000081 1 = 1
theorem a000081_two : a000081 2 = 1
theorem a000081_three : a000081 3 = 2
theorem a000081_four : a000081 4 = 4
theorem a000081_five : a000081 5 = 9
```

The `n = 4` proof includes the positive-real identity
`(x^x)^(x^x) = (x^(x^x))^x`; the remaining representatives are separated as
functions by exact exponent comparisons at `x = 3`.  The `n = 5` proof
enumerates the 14 legal binary parenthesizations, collapses them to 9
positive-real functions with proved exponent identities, and proves those 9
representatives distinct by a finite strict-exponent certificate at `x = 3`.
The size-`1..5` parenthesization enumerations are inherited from the shared
`PowTower.Expr` certificates rather than re-checked locally.
No Pólya recurrence or rooted-tree counter is used as a counting shortcut
without a semantic bridge.

[`LeanProofs/A002845.lean`](LeanProofs/A002845.lean) defines OEIS A002845
canonically as the number of distinct natural-number values of all binary
parenthesizations of the literal expression `2^2^...^2`.  The primary
definition is the semantic value set of expression trees evaluated by `Nat`
exponentiation:

```lean
noncomputable def a002845 (n : Nat) : Nat
theorem a002845_eq_logCard (n : Nat) : a002845 n = a002845LogCard n
theorem a002845_eq_directLogCard (n : Nat) : a002845 n = directLogCard n
theorem a002845_eq_certifiedSparseCard (n : Nat) :
  a002845 n = certifiedSparseCard n
theorem a002845_one : a002845 1 = 1
-- ...
theorem a002845_twenty_three : a002845 23 = 9029719
```

The value theorems `a002845_one` through `a002845_six` use a direct finite
computation of the canonical logarithm set, proved equivalent to the semantic
value set by injectivity of `m ↦ 2^m`. The value theorems
`a002845_seven` through `a002845_twelve` use the sparse-log evaluator over the
verified hereditary sparse binary numbers of
[`LeanProofs/SparseBinary.lean`](LeanProofs/SparseBinary.lean).  The value
theorems `a002845_thirteen` through `a002845_twenty_three` come from one
prefix-table certificate over the shared proved hash-set fast table of
`PowTower.Expr` instantiated at atom `Sparse.ofNat 1` and combine
`certifiedCombineLog`; every fast row is Lean-proved to enumerate exactly the
shared finite recurrence.  The combine operation itself is the total verified
`Sparse.shift` — `SparseBinary.lean` proves the comparator numerically correct
on canonical values (`compare_iff`) and proves that the structural
carry-insertion arithmetic (`incr`/`insBit`/`add`/`shift`) returns the
canonical representation of the expected number (`shift_eq_ofNat`) — so no
`implemented_by` substitution is involved anywhere: the executable path *is*
the proved path, and the only remaining trust in the value certificates is
`native_decide` itself.

OEIS A198683 is defined from the canonical lexical syntax of all binary
parenthesizations of `i^i^...^i`, interpreting every binary node as the
principal complex power `exp (log z * w)`, and taking the number of distinct
evaluated values.  Its recursive value-set helper is Lean-proved equivalent to
that lexical definition before being used by the computational proofs.  The
formalization proves the accepted values through `n = 7` directly over `ℂ`,
with public theorems `a198683_one` through `a198683_seven`, split across four
modules:
[`LeanProofs/A198683Tower.lean`](LeanProofs/A198683Tower.lean) holds the
canonical definition layer, the tower constants `p2, ..., p6O` with their
analytic facts (in the shared internal namespace `A198683Support`), and the
values through `n = 4`;
[`LeanProofs/A198683FiveSix.lean`](LeanProofs/A198683FiveSix.lean) proves
`a198683 5 = 7` and `a198683 6 = 15`;
[`LeanProofs/A198683SevenUpper.lean`](LeanProofs/A198683SevenUpper.lean)
carries the representative-list refinement pipeline ending in
`a198683_seven_le_thirty_four`; and
[`LeanProofs/A198683.lean`](LeanProofs/A198683.lean) proves the matching
lower bound `thirty_four_le_a198683_seven`, assembles
`a198683_seven : a198683 7 = 34`, and restates the historical intermediate
bounds as corollaries of the final pair.
Two companion certificate modules record finite checked data from the local
[`Oeis/A198683/`](Oeis/A198683/README.md) corpus:
[`LeanProofs/A198683Schoenfield.lean`](LeanProofs/A198683Schoenfield.lean)
checks the Schoenfield labels through `n = 11`,
[`LeanProofs/A198683SchoenfieldRows.lean`](LeanProofs/A198683SchoenfieldRows.lean)
reconstructs the `n = 7` through `n = 11` labels from the source table's
Count/Match rows, and
[`LeanProofs/A198683N12Probe.lean`](LeanProofs/A198683N12Probe.lean) checks
that the strict `n = 12` candidate table has 2925 classes among 5139
candidates and that the documented probe split refines it to 2926 classes.
[`LeanProofs/A198683N12Magnitude.lean`](LeanProofs/A198683N12Magnitude.lean)
checks that the retained overflow/magnitude metadata isolates candidate `57`.
[`LeanProofs/A198683N12OverflowWitness.lean`](LeanProofs/A198683N12OverflowWitness.lean)
records the traced candidate-57 expression semantically and proves it lies in
the `n = 11` and `n = 12` value sets, with a log-modulus separation criterion
for comparing that overflow witness against candidates whose exponent real
part is certified larger.
[`LeanProofs/A198683N12Symbolic.lean`](LeanProofs/A198683N12Symbolic.lean)
replaces the n = 12 heuristic cluster analysis with exact symbolic Lean
reductions.  It proves that all fourteen representatives from the
near-`i^i` probe class are exactly `i^i = exp(-pi/2)`, and proves the exact
merges of the n = 12 near-zero probe doubleton `{2207, 3777}` and of the
retained near-one pair `{1404, 4239}`.  For the remaining near-one split it
defines representative `25` and reduces the separation of `25` from
`{1404, 4239}` to one conditional pair,
`nearOne25_ne_nearOne1404_of_endpoint_bounds` /
`nearOne25_ne_nearOne4239_of_endpoint_bounds`, whose every hypothesis is a
scalar endpoint estimate for `exp`, `sin`, or `cos` at an explicit rational
point.  The supporting layers are already unconditional: the module certifies
rational boxes for `rho = exp(-pi/2)` (from mathlib's 20-decimal `exp 1`
certificate and a Taylor bound for the residual), for `pi/2` (from mathlib's
20-decimal `pi` certificate), and hence for `theta = (pi/2) * rho`
(`rho_bounds`, `theta_box`), and it exposes the level-by-level reduction
lemmas that propagate an interval certificate from those boxes through
`v = i^(i^(i^i))`, the representative-`25` seed, and the higher tower levels
down to the final sign obligation `nearOne25Base.im < 0`, together with exact
real/imaginary recurrence formulas for the `(-i)^z` seed and lower `i^z`
layers of representative `25`.
These n = 12 companion modules are progress toward, but still not, a semantic
proof of `a198683 12 = 2926`.
The current formalization checkpoint and next directions are summarized in
[`Oeis/A198683/reports/wave-4/a198683-n12-lean-status-and-next-directions.md`](Oeis/A198683/reports/wave-4/a198683-n12-lean-status-and-next-directions.md).

[`LeanProofs/A199812.lean`](LeanProofs/A199812.lean) defines OEIS A199812
from the same shared `PowTower.Expr` lexical syntax used by the other
power-tower OEIS modules, interpreting the atom as ordinal `omega` and each
node as ordinal exponentiation. It uses Cantor normal forms and dynamic
normal-form counts that are direct instances of the shared
`PowTower.Expr` finite recurrence, and certifies the listed values through
`n = 13` from one prefix-table certificate over the shared proved hash-set
fast table (atom `0 : ONote`, combine `a + omega^b` on inner exponents):

```lean
theorem a199812_one : a199812 1 = 1
-- ...
theorem a199812_thirteen : a199812 13 = 20287
```

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

Build the root Lake/mathlib workspace:

```powershell
cd src/Lean
lake exe cache get
lake build
```

Build the SetTheory Rocq/Coq development and its independent Lean port:

```powershell
cd src/Lean/SetTheory
coqc -Q . SetTheory Fol.v
coqc -Q . SetTheory Calculus.v
coqc -Q . SetTheory Completeness.v
coqc -Q . SetTheory Zf.v
coqc -Q . SetTheory Equivalence.v

cd lean
lake build
```
