# Coq Ports of LeanProofs

- Created (UTC): 2026-07-07T03:24:49Z
- Initial source HEAD: f3be2772be5658f305f509b584b0cb99d97cbe7a

This directory contains Rocq/Coq ports of proof modules from the root
`src/Lean/LeanProofs/` Lean workspace.  The ports are intentionally
Coq-idiomatic rather than line-by-line translations: each module preserves the
mathematical certificate surface where practical, but uses Coq standard-library
definitions, tactics, and proof organization.

The SetTheory project already has its own Coq development in
`src/Lean/SetTheory/`; it is not duplicated here.

Current ports:

- `Nicod.v` ports the NAND language, Nicod axiom/rule derivations, soundness,
  and functional-completeness lemmas from `Nicod.lean`.
- `ArctanSquareIdentity.v` ports the quadratic arctangent identity proof.
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
  symbolic quotient of the named small A198683 value classes, preserving the
  `n <= 4` value counts and the `v4b_eq_v4e`/`v4c_eq_v4d` collapses.  The
  Lean file's principal-complex-power analytic interpretation is not yet
  replayed in Coq.
- `A000081.v` ports the finite executable certificate from `A000081.lean`.
  It uses a hereditarily sorted exponent normal form for positive-real tower
  functions, preserving the named small parenthesizations and equality
  certificates such as `e4c = e4d` and `e5f = e5j`.  It certifies the Lean
  values through `n = 5` and extends the same executable normal-form count
  through `n = 8`.
- `A199812.v` ports the executable ordinal-note recurrence behind
  `A199812.lean`: inner tower exponents are represented as Cantor-normal-form
  notes below epsilon_0, tower splits combine degrees by
  `a, b |-> a + omega^b`, and the recurrence is connected to the shared
  `PowTower.v` evaluator.  It certifies the initial values through `n = 8`;
  the Lean module's mathlib ordinal-semantics bridge and longer table through
  `n = 13` are not yet replayed in Coq.
- `SparseBinary.v` ports the proof-facing sparse-arithmetic surface used by
  A002845.  It uses Coq's verified binary natural numbers `N` as the sparse
  carrier, preserving the evaluation/canonicality/comparison and
  increment/add/shift correctness API from `SparseBinary.lean`.
- `A002845.v` ports the exact-logarithm reduction for the natural power tower
  sequence and verifies the first six values through a binary-`N` executable
  logarithm.  It is connected to `SparseBinary.v` by a certified sparse-log
  evaluator that agrees with the exact binary logarithm evaluator.
- `A198683N12Magnitude.v` ports the finite TSV-metadata layer from
  `A198683N12Magnitude.lean`: the n = 12 huge-negative-exponent,
  negative-exponent-above-ten, and overflow-regime flags are represented as
  generated one-hot lists over the 5139 retained candidates, and Coq proves
  that candidate 57 is the unique flagged row.  The Lean file's
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
- `A198683Schoenfield.v` ports the finite Schoenfield class-count certificate
  from `A198683Schoenfield.lean`: normalized labels are generated from the
  retained source table, and Coq verifies the Catalan row counts, no-gap
  normalization condition, and published class counts through `n = 11`.
- `A198683SchoenfieldRows.v` ports the row-level Count/Match certificate from
  `A198683SchoenfieldRows.lean`: Coq reconstructs the normalized labels from
  the retained Schoenfield table rows for `n = 7` through `n = 11` and then
  reuses the class-count certificate.
- `EquationalLogic.v` ports the executable first-order equational proof
  checker and its soundness theorem.
- `WolframBooleanCertificates.v` ports the Wolfram/Meredith generated
  equational certificates against that checker.
- `WolframBooleanHuntingtonCertificates.v` ports the generated
  Sheffer-to-Huntington certificate.
- `WolframBoolean.v` exposes the certificate-derived algebraic consequences,
  Boolean truth-table characterization, NAND/NOR functional-completeness
  theorem layer, and executable finite-search machinery.  The final Lean
  `native_decide` lower-bound theorem is not yet replayed in Coq; the direct
  monolithic `vm_compute`/`native_compute` check was too slow.

Build from `src/Lean/`:

```powershell
coqc -Q CoqProofs LeanProofsCoq CoqProofs/Nicod.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/ArctanSquareIdentity.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/FloorSqrtSum.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/RationalFloorOrbit.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/PowTower.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683Tower.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A000081.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A199812.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/SparseBinary.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A002845.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683N12Magnitude.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683N12Probe.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683N12OverflowWitness.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683Schoenfield.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683SchoenfieldRows.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/EquationalLogic.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanCertificates.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanHuntingtonCertificates.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBoolean.v
```
