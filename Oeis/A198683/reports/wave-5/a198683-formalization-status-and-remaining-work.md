# A198683: honest formalization status and the remaining work, goal by goal

- Status: wave-5 status ledger
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: exactly what is machine-proved about A198683 today, exactly what is
  not, and the measured size of the remaining work for each natural goal
- Created (UTC): 2026-07-09T03:28:29Z
- Repository HEAD: 5762699990018c87f222d73833a84067c7e32f3f (branch
  `claude/lean-coq-proofs-review-6d6444`)

This document exists because the headline results of wave-5 are easy to
over-read.  The two *structurally uncertain* questions behind the disputed
`a(12)` are now unconditionally machine-settled, and the decision tree that
turns a partition certificate into a value of `a(12)` is proved in both Lean
and Rocq/Coq — but **no unconditional value of `a(n)` beyond `n = 7` exists**,
and the certificate the decision tree consumes has not been constructed.
The tables below draw that line precisely.

## 1. The epistemic ladder

Every A198683 claim in this repository sits on exactly one of four rungs:

| rung | meaning | trust base |
|------|---------|-----------|
| **proved** | machine-checked theorem about the actual mathematical objects (complex values, the lexical value set) | Lean kernel / Rocq kernel (+ the standard classical axioms; for interval-backed results also coq-interval's PrimInt63/PrimFloat evaluator axioms) |
| **conditionally proved** | machine-checked implication whose hypothesis (the partition witness) is not yet constructed | same kernels; fires only when fed |
| **data-certified** | machine-checked consistency of a *stored table* (row counts, class counts, label reconstruction) — says nothing about complex numbers | same kernels, but the statement is about retained data |
| **heuristic** | multi-precision numerics and/or Wolfram's symbolic engine agree | no formal trust |

## 2. What is proved, unconditionally (both assistants unless noted)

| result | Lean | Coq |
|--------|------|-----|
| `a(1..7) = 1, 1, 2, 3, 7, 15, 34`, semantically, with the certified value lists (`canonicalReps`) as reusable artifacts | ✅ (`A198683.lean` and the chain below it) | ❌ (quotient shadow only) |
| the lexical value set equals the split-recurrence value set, **for all `n`** — the theorem that makes the recurrence, not the Catalan-many parse trees, the unit of all further work | ✅ | ✅ |
| **the near-`1` split** `nearOne25 ≠ nearOne1404` (wave-3 question Q3, split direction) | ✅ (`A198683N12Endpoints.nearOneSplit`, Taylor endpoint certificates) | ✅ (`nearOne25C_ne_nearOne1404C`, interval-certified norm separation) |
| the fourteen near-`i^i` representatives all equal `i^i` exactly; the near-zero pair `{2207, 3777}` and the near-one pair `{1404, 4239}` are exact merges | ✅ | partially (norm-level; the island identities `i^i = ρ`, `(i^i)^i = −i`, `i^{−i}} = e^{π/2}` are proved in `A198683N12ComplexTowers.v`) |
| **the overflow magnitude** `10^100 < Im(overflowBase11)` and the separation criterion: any principal-power value with log-modulus above `−(π/2)·10^100` differs from candidate `57` — demoting the "no-miracles hypothesis" from a transcendence assumption to a per-class magnitude check | ✅ (~930 lines, 44-digit hand boxes) | ✅ (~250 lines, `interval with (i_prec 200)`) |
| `overflowCandidate12 ∈` value set at `n = 12` | ✅ | ❌ |
| **the decision tree** (see §3) as implications | ✅ | ✅ (membership and 2926-pinning cores fully constructive) |
| two of the original ladder endpoint constants were **false** (endpoint-vs-midpoint transcription); refutations preserved as theorems | ✅ | n/a (Coq never used the decomposed constants) |

Data-certified (not semantic): the Schoenfield label tables for `n ≤ 11`,
the `n = 12` strict/probe-refined tables (5139 rows, 2925/2926 classes), and
the magnitude flag columns isolating candidate `57`.

Heuristic only: `a(8) = 77`, `a(9) = 187`, `a(10) = 462`, `a(11) = 1152`,
`a(12) = 2926`, and the correctness of the probe-refined partition outside
the proved special clusters.

## 3. What is proved conditionally

With `W` = a partition witness (`N12PartitionWitness` in Lean,
`N12PartitionWitnessC` in Coq: 2926 representative expressions, value-cover
of all `n = 12` parenthesizations, pairwise separation outside the overflow
class, distinguished classes pinned to the concrete towers) and
`O` = the overflow-isolation hypothesis (now a per-class magnitude check):

| hypothesis | conclusion |
|------------|------------|
| `W` | `a(12) ∈ {2925, 2926}` |
| `W ∧ O` | `a(12) = 2926` |
| `W ∧ ¬O` | `a(12) = 2925` |

The near-`1` dichotomy no longer appears: it is proved.  **Neither `W` nor
any unconditional surrogate for it exists.**  Consequently:

- `a(12) ∈ {2925, 2926}` is **not** an unconditional theorem;
- no nontrivial unconditional bound on `a(12)` is currently proved (the
  trivial `a(12) ≤ 58786` would be a one-liner; even `a(12) ≤ 5139`
  requires the level-≤ 11 merges, which are witness-grade work);
- if the heuristic partition *over-merged* anywhere, no 2926-shaped witness
  exists and the true `a(12)` exceeds `2926`; if it over-split, the truth is
  below `2925`.  The decision tree cannot detect either failure — it would
  simply never fire.

## 4. The remaining work, measured

The unit of work is the recurrence, not parse trees: with the value lists at
levels `< n` certified, level `n` presents `Σ_{k} a(k)·a(n−k)` candidate
values collapsing to `a(n)` classes.  (Sanity check: this sum at `n = 12`
is `2·(1152 + 462 + 374 + 231 + 238) + 15² = 5139` — exactly the corpus's
candidate count.)

| n | candidates | classes | merge obligations (≤ candidates − classes) | separation obligations |
|---|-----------:|--------:|--------------------------------------------:|------------------------:|
| 8 | 135 | 77 | ~58 | ~76 |
| 9 | 373 | 187 | ~186 | ~186 |
| 10 | 803 | 462 | ~341 | ~461 |
| 11 | 2020 | 1152 | ~868 | ~1151 |
| 12 | 5139 | 2926 | ~2213 | ~2925 + overflow magnitude checks |
| **total** | **8470** | | **~3666** | **~4800** |

Two structural facts keep these numbers linear rather than quadratic:

- **Separations**: with a certified interval box per class value, sorting by
  `(Re, Im)` reduces pairwise distinctness to adjacent-gap checks (`m − 1`
  per level), with only *overlapping* boxes needing special treatment — and
  the known overlapping clusters at `n = 12` (near-`0`, near-`i^i`,
  near-`1`, overflow) are exactly the ones already dispatched.
- **Merges**: a large fraction of collisions are syntactically identical
  terms (the `k ↔ n−k` symmetric splits) or instances of already-proved
  island identities; the genuinely new symbolic content is the
  islands-of-associativity residue, whose only known hard cases at `n = 12`
  (the fourteen-member `i^i` cluster, the near-zero and near-one merges)
  are already proved.

What does **not** yet exist, and must be built once:

1. **The witness generator** — a program emitting, per level: the
   representative list (as `PowTower.Expr` terms), the interval box table,
   the sorted gap-check obligations, and the merge obligations with their
   island decompositions.  (The wave-3 feasibility study sketched this
   engine; the decision-tree modules now give its output a precise type in
   both assistants.)
2. **The batch interval backend** — in Coq, `interval` already discharges
   individual boxes (demonstrated end-to-end this wave); in Lean, the
   endpoint machinery of `A198683N12Endpoints.lean` is the seed but is
   hand-driven.  The generator must emit proof scripts, not just numbers.
3. **The merge prover** — the symbolic normalizer for
   islands-of-associativity collapses; the fourteen-member-cluster proofs
   are the template.

## 5. Goals, in increasing order of ambition

| goal | what it takes | new obligations |
|------|---------------|-----------------|
| **G1: `a(8) = 77` unconditional** (the pilot) | the generator's first run: 135 candidates from the certified `n ≤ 7` lists, ~58 merges (mostly syntactic/island-free), ~76 gap checks | ~10² proof obligations; one new module per assistant |
| **G2: `a(9..11)` unconditional** | ladder iterations of G1; scale grows ×3 per level; no new kinds of work expected | ~10³ obligations cumulative |
| **G3: `a(12) ∈ {2925, 2926}` unconditional** | full witness `W`: G2 plus the `n = 12` level (~2213 merges, ~2925 gap checks); the special clusters are already proved | ~5·10³ obligations cumulative |
| **G4: `a(12) = 2926` unconditional** | G3 plus `O`: per-class log-modulus lower bounds — free by-products of the box table, fed to the proved criterion | negligible marginal cost over G3 |
| **G5: OEIS-grade artifact** | the wave-3 §7 audit trail: the certificate re-runnable from a pinned commit, plus prose | documentation-sized |

The honest bottom line: **G4 is now an engineering campaign, not a research
problem** — every question of mathematical substance identified by waves 1–4
is unconditionally settled, in two independent proof assistants, and the
remaining ~8·10³ obligations are of kinds that have each been demonstrated
end-to-end at least once.  But none of that campaign has run yet, and until
it does, no value of `a(n)` for `n ≥ 8` — including the set membership
`a(12) ∈ {2925, 2926}` — is a theorem.

## 6. Pointers

- Decision tree: `LeanProofs/A198683N12Certificate.lean`,
  `CoqProofs/A198683N12Certificate.v` (+ `A198683N12CertificateC.v`).
- Near-`1` split: `LeanProofs/A198683N12Endpoints.lean`,
  `CoqProofs/A198683N12ComplexTowers.v`.
- Overflow bound: `LeanProofs/A198683N12OverflowBound.lean`,
  `CoqProofs/A198683N12OverflowBound.v`.
- Complex foundation (Coq): `CoqProofs/A198683Complex.v`.
- Interval boxes (Coq): `CoqProofs/A198683N12Bounds.v`.
- The companion result report:
  [`a198683-n12-decision-tree-and-near-one-split.md`](a198683-n12-decision-tree-and-near-one-split.md).
- The engine sketch this plan operationalizes:
  [`../wave-3/a198683-numerics-interval-feasibility.md`](../wave-3/a198683-numerics-interval-feasibility.md).
