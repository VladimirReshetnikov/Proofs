# Coq Ports of LeanProofs

- Created (UTC): 2026-07-07T03:24:49Z
- Initial source HEAD: f3be2772be5658f305f509b584b0cb99d97cbe7a

This directory contains Rocq/Coq ports of proof modules from the root
`LeanProofs/` Lean workspace.  The ports are intentionally
Coq-idiomatic rather than line-by-line translations: each module preserves the
mathematical certificate surface where practical, but uses Coq standard-library
definitions, tactics, and proof organization.

The SetTheory project already has its own Coq development in
`SetTheory/`; it is not duplicated here.

## Current ports

- `Sheffer.v` ports the shared Sheffer-stroke vocabulary from
  `Sheffer.lean`: NAND/NOR truth tables, one-stroke formulas, ordinary
  classical propositional formulas, and truth-preserving translations into
  pure NAND and pure NOR syntax.
- `Nicod.v` ports the Nicod axiom/rule derivations, soundness, and
  functional-completeness lemmas from `Nicod.lean`, over the shared NAND-only
  stroke language of `Sheffer.v` (as in the Lean original).
- `ArctanSquareIdentity.v` ports the quadratic arctangent identity proof.
- `TrigGoldenRatio.v` ports the elementary identity
  `sin 9° + sin 21° + sin 39° = φ / √2`.  Coq's standard library does not
  provide the exact `cos (π / 5)` value used by Lean/mathlib, so the port
  derives it locally from the triple-angle formula and the positive quadratic
  root.
- `TinyExponentTower.v` ports the complete floor certificate from
  `TinyExponentTower.lean`. It proves the generic `Zfloor` conversion layer,
  then discharges the concrete logarithmic and exponential bounds
  unconditionally with `coq-interval` and the same first-order remainder
  argument as the Lean proof. The exported `floor_tinyExponentTower_sub` and
  `floor_expanded_tinyExponentTower_sub` theorems therefore have no
  analytic-bound hypotheses.
- `FermatFour.v` ports the project-local wrapper surface from
  `FermatFour.lean`: Coq defines the `a^4 + b^4 = c^2` counterexample
  predicate, proves elementary structural facts and the well-founded infinite
  descent eliminator, records the Pythagorean-triple-of-squares bridge, proves
  scaling, non-primitive both-even descent, and parity obstruction lemmas, then
  derives the stronger integer-square theorem and the positive-natural FLT-4
  statement either from an explicit smaller-counterexample descent-step
  parameter, from the narrower mixed-parity primitive-descent parameter, or
  from the canonical odd-left/even-right primitive-descent parameter.  The
  installed Coq libraries do not include a modern FLT-4 theorem; the old
  self-contained `rocq-archive/fermat4` formalization exists but targets Coq
  8.0 and is not yet modernized here.
- `FloorSqrtSum.v` ports the rational induction core of the floor-square-root
  summation identity from `FloorSqrtSum.lean`.
- `RationalFloorOrbit.v` ports the Calkin-Wilf pair generator core from
  `RationalFloorOrbit.lean`, including fuel adequacy, left/right child
  equations, positivity, coprimality invariants, `pairNext` arithmetic bridge
  lemmas, the successor equation `cwPair (n + 1) = pairNext (cwPair n)`, and
  the inverse-index round trips `cwPair (cwIndex a b) = (a, b)` for positive
  coprime pairs and `cwIndex (cwPair n).1 (cwPair n).2 = n`.  It also embeds
  generated pairs into Coq `Q`, proves the corresponding floor and
  `rationalNext` step lemmas, derives `rationalNext (cwRat n) = cwRat
  (n + 1)` both structurally and up to `Qeq`, defines the recursive
  `rationalFloorOrbit`, proves `rationalFloorOrbit (n + 1) = cwRat n`, and
  characterizes zero as the orbit's initial value.  It also proves reduced
  `Qred` numerator/denominator coprimality, the normalized-rational existence
  and uniqueness lemmas, and the final exact-once enumeration theorem for
  nonnegative Coq rationals.
- `PowTower.v` ports the shared lexical syntax, executable
  parenthesization/evaluation layer, and small recursive-value sanity checks.
- `A198683Tower.v` ports the executable initial-value substrate from
  `A198683Tower.lean`: the shared tower syntax is evaluated into a finite
  symbolic quotient of the named small A198683 value classes through the
  `p6*` layer and the generated n = 7 Schoenfield label collapses, preserving
  the `n <= 4` value counts and the named finite collapses used by the
  following small-value certificates.  The Lean file's
  principal-complex-power analytic interpretation is not yet replayed in Coq.
- `A198683FiveSix.v` ports the finite-count surface from
  `A198683FiveSix.lean`: using the symbolic quotient from `A198683Tower.v`,
  Coq checks the named `p5*`/`p6*` candidate lists and verifies
  `A198683(5) = 7` and `A198683(6) = 15`.
- `A198683SevenUpper.v` ports the finite upper-bound surface from
  `A198683SevenUpper.lean`: the generated n = 7 symbolic quotient checks the
  34 collapsed representatives and verifies the corresponding `<= 34` bound.
- `A198683.v` ports the final executable assembly from `A198683.lean`,
  restating the initial values through `n = 7` and the historical lower/upper
  bound corollaries over the Coq symbolic quotient.  The Lean file's semantic
  complex lower-bound proof is not yet replayed in Coq.
- `A198683EightBounds.v` records the Coq-side level-8 finite certificate
  surface corresponding to `A198683EightBounds.lean`: the raw Coq symbolic
  quotient still has 135 level-8 candidates, while the imported Schoenfield
  certificate normalizes the generated level-8 class table to 77 classes and
  hence lies inside the Lean semantic interval `[16, 127]`.  The analytic
  complex-power bridge proving those bounds for the semantic `a198683 8` is
  not replayed in Coq.
- `A000081.v` ports the finite executable certificate from `A000081.lean`.
  It uses a hereditarily sorted exponent normal form for positive-real tower
  functions, preserving the named small parenthesizations and equality
  certificates such as `e4c = e4d` and `e5f = e5j`.  It certifies the Lean
  values through `n = 5` and extends the same executable normal-form count
  through `n = 8`.
- `A158415.v` ports the finite headline certificate surface from the
  generated `A158415*.lean` corpus: Coq keeps the expression-tree syntax and
  the checked cardinality/value table through `n = 15`, including the public
  `a158415_*` and `recursiveValueSet_*_ncard` theorem names.  The generated
  real-radical ordering and range proof is not replayed in Coq.
- `A199812.v` ports the executable ordinal-note recurrence behind
  `A199812.lean`: inner tower exponents are represented as Cantor-normal-form
  notes below epsilon_0, tower splits combine degrees by
  `a, b |-> a + omega^b`, and the recurrence is connected to the shared
  `PowTower.v` evaluator.  The counts are produced by a memoized level table
  deduplicated with a fueled mergesort over `onoteCompare` and computed once
  into a single vm_computed table, matching the Lean value table through
  `n = 13`; the Lean module's mathlib ordinal-semantics bridge is not yet
  replayed in Coq.
- `SparseBinary.v` ports the proof-facing sparse-arithmetic surface used by
  A002845.  It uses Coq's verified binary natural numbers `N` as the sparse
  carrier, preserving the evaluation/canonicality/comparison and
  increment/add/shift correctness API from `SparseBinary.lean`.
- `A002845.v` ports the exact-logarithm reduction for the natural power tower
  sequence, keeps the binary-`N` executable logarithm bridge for the initial
  direct layer, and adds a hereditary sparse-binary recurrence for the finite
  certificates.  The executable-only `HereditarySparse` level recurrence is
  deduplicated with a tail-recursive fueled mergesort over its fueled
  `compare` and computed once into a single vm-checked binary-`N` count
  table, cross-checked against the quadratic structural-equality dedup on a
  cheap prefix.  It verifies the value table through `n = 17` (the Lean
  module's live table reaches `n = 18`).
- `A198683N12Magnitude.v` ports the finite TSV-metadata layer from
  `A198683N12Magnitude.lean`: the n = 12 huge-negative-exponent,
  negative-exponent-above-ten, and overflow-regime flags are embedded as
  literal transcriptions of the Lean lists over the 5139 retained candidates;
  Coq proves each literal equal to the generated one-hot list by `vm_compute`
  and that candidate 57 is the unique flagged row.  The Lean file's
  complex-analytic exponential separation lemmas are not yet replayed in Coq.
- `A198683N12Probe.v` ports the finite retained-data certificate from
  `A198683N12Probe.lean`: the `strict_class` labels are generated from
  `a198683-n12-candidates.tsv`, Coq checks a witness-based partition
  certificate for 5139 rows and 2925 strict classes, verifies the documented
  strict class-25 cluster and tentative overflow singleton, and checks the
  probe-refined split to 2926 classes.
- `A198683N12OverflowWitness.v` ports the syntactic witness expression from
  `A198683N12OverflowWitness.lean`: the traced n = 11 base and its n = 12
  overflow candidate are represented over the shared `PowTower.v` syntax, and
  Coq verifies their sizes and membership in the corresponding
  parenthesization lists.  The Lean file's semantic complex-valued membership,
  norm formula, and separation criteria are not yet replayed in Coq.
- `A198683N12Symbolic.v` ports the finite symbolic-equality surface from
  `A198683N12Symbolic.lean`: selected n = 12 tower expressions are evaluated
  into a small quotient generated by the exact principal-power rewrites used
  in Lean, checking the `2207 = 3777` near-zero pair, the `1404 = 4239`
  near-one pair, and the 14 retained near-`i^i` representatives.  The Lean
  file's complex principal-log semantics and interval-separation cascade are
  not yet replayed in Coq.
- `A198683Schoenfield.v` ports the finite Schoenfield class-count certificate
  from `A198683Schoenfield.lean`: normalized labels are generated from the
  retained source table, and Coq verifies the Catalan row counts, no-gap
  normalization condition, and published class counts through `n = 11`.
- `A198683SchoenfieldRows.v` ports the row-level Count/Match certificate from
  `A198683SchoenfieldRows.lean`: Coq reconstructs the normalized labels from
  the retained Schoenfield table rows for `n = 7` through `n = 11` and then
  reuses the class-count certificate.
- `A198683N12Bounds.v` certifies the real interval boxes behind the `n = 12`
  near-one analysis with `coq-interval`, including the norm separation used
  to distinguish representatives `25` and `1404`.
- `A198683Complex.v` supplies a reusable Coquelicot complex-number model of
  principal exponentiation, together with the real/imaginary formulas and
  modulus-separation lemmas used by the A198683 tower proofs.
- `A198683N12ComplexTowers.v` instantiates the concrete near-one and overflow
  towers in that complex model, proves their island identities, connects them
  to the interval-box shadows, and derives the genuine complex inequality
  `nearOne25C <> nearOne1404C`.
- `A198683N12Certificate.v` ports the generic `n = 12` partition-witness
  decision tree. It uses a relational distinct-count specification over
  arbitrary evaluated values, so the witness, cover, separation, and
  `2924`/`2925`/`2926` consequences are independent of the concrete complex
  implementation.
- `A198683N12OverflowBound.v` proves with `coq-interval` that the overflow
  base has imaginary part greater than `10^100`, and derives the
  moderate-log-modulus criterion separating candidate `57` from ordinary
  candidates.
- `A198683N12CertificateC.v` instantiates the generic decision tree over
  Coquelicot complex numbers and principal powers. Because the near-one split
  is proved, any partition witness confines the count to `{2925, 2926}`;
  overflow isolation then pins `2926`.
- `A198683N12Endpoints.v` gives the merged Lean endpoint module its own Coq
  import surface, re-exporting the complex-instantiated near-one split and
  n = 12 consequences from `A198683N12CertificateC.v`.
- `EquationalLogic.v` ports the executable first-order equational proof
  checker and its soundness theorem.
- `WolframBooleanCertificates.v` ports the Wolfram/Meredith generated
  equational certificates against that checker.
- `WolframBooleanHuntingtonCertificates.v` ports the generated
  Sheffer-to-Huntington certificate.
- `WolframBoolean.v` exposes the certificate-derived algebraic consequences,
  Boolean truth-table characterization, the NAND/NOR functional-completeness
  layer (over the shared stroke language of `Sheffer.v`), and the executable
  finite-search machinery (over the first-order terms of `EquationalLogic.v`).
  The Lean pair's `native_decide` lower-bound certificate is fully replayed:
  `shortEquationCountermodelCheck = true` is proved by `vm_compute` through a
  proved bridge to lazy `match`-based `forallb`/`existsb` combinators.
  `vm_compute` is call-by-value, so the eager `andb`/`orb` in the original
  definitions would run the full 128-environment sweep and the entire
  countermodel search on every candidate equation; the short-circuiting
  combinators plus hoisting the constant non-Wolfram pool out of the
  per-equation loop bring the whole check to a few seconds, and bridge
  equalities transport the result back to the original eager definitions.
  This yields Coq counterparts of
  `every_short_boolean_sheffer_equation_has_finite_nonwolfram_countermodel`
  and `wolfram_six_operations_is_minimal_for_single_equational_axioms` with
  statements matching the Lean originals.

## Building

The full port requires Rocq/Coq, Coquelicot, and `coq-interval`. Build from the
repository root; the committed `_CoqProject` is dependency-ordered and is the
canonical module list:

```powershell
Get-Content _CoqProject |
  Where-Object { $_ -match '^CoqProofs/.+\.v$' } |
  ForEach-Object {
    & coqc -Q CoqProofs LeanProofsCoq $_
    if ($LASTEXITCODE -ne 0) { throw "coqc failed: $_" }
  }
```
