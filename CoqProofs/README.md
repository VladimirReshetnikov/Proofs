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
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A000081.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A199812.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/SparseBinary.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A002845.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/A198683N12Magnitude.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/EquationalLogic.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanCertificates.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBooleanHuntingtonCertificates.v
coqc -Q CoqProofs LeanProofsCoq CoqProofs/WolframBoolean.v
```
