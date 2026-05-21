# A198683(12): Post-Wave-2 Research Synthesis

- Status: Synthesis report (wave-3)
- Audience: Vladimir Reshetnikov, OEIS contributors, maintainers, future agents
- Scope: Consolidate the findings of the three wave-2 root-cause analyses, record where they agree and where they diverge, and identify the remaining unsettled questions about `A198683(12)`
- Created (UTC): 2026-05-21T14:49:21Z
- Repository HEAD: 418b69c1727af2b40e7f02fb8afc9c2d89c8ab55

## Summary

After three independent root-cause passes on the historical
`A198683(12) ∈ {2919, 2926}` conflict, the picture is consistent at the
factual level but unresolved at the certificate level. The Python
`mpmath` `2919` claim is invalidated; the Wolfram `2926` claim is the
strongest single-source local computation but is not a proof; and the
true value lies in a small set whose precise membership depends on
heuristic equality predicates that no wave-1 or wave-2 pipeline can
discriminate without a certified-arithmetic engine.

The state of the corpus after wave-2 is:

- **Recurrence and candidate generation**: settled. Both pipelines use
  the same OEIS principal-power semantics, the same dynamic-programming
  recurrence over distinct lower-level values, and the same `5139`
  candidate powers at `n = 12`.
- **Lower-term reproduction**: settled. Both pipelines reproduce
  `1, 1, 2, 3, 7, 15, 34, 77, 187, 462, 1152` for `n = 1..11`.
- **Locus of disagreement**: settled. The discrepancy lives entirely in
  the deduplication of the `5139` `n = 12` candidates; not in the
  recurrence, the candidate count, or the OEIS definition.
- **The `2919` claim**: invalidated by all three wave-2 reports as a
  finite-precision `mpmath.almosteq` artefact.
- **The `2926` claim**: standing as the strongest single-source local
  computation, but not a standalone proof — it depends on Wolfram's
  symbolic equality engine at the local WL version.
- **The true value of `a(12)`**: unsettled. The local heuristics span
  `2919`, `2920`, `2921`, `2922`, `2924`, `2925`, `2926`, `2927`,
  depending on which knob is turned. Wave-2 narrows the plausible
  range to a small set near `{2925, 2926, 2927}` but does not
  discriminate within it.
- **Path to certification**: planned. Wave-3 includes a feasibility
  study,
  [`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md),
  that maps a certified pipeline onto the in-repo `src/Numerics/python`
  package plus a small set of well-scoped extensions.

## 1. Wave-1: what was claimed

Wave-1 consists of two result reports, both at `reports/wave-1/`. Each
established a concrete numeric claim under a specific pipeline:

| Report | Pipeline | Claim |
|---|---|---:|
| [`wave-1/a198683-n12-python-mpmath-2919.md`](../wave-1/a198683-n12-python-mpmath-2919.md) | Python `mpmath`, scale-invariant numerical buckets, `almosteq`, special overflow bucket for one tiny candidate | `a(12) = 2919` |
| [`wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](../wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md) | Wolfram Language recurrence with `Union[..., SameTest -> Equal]` via the local Tungsten runner | `a(12) = 2926` |

Both reports agree on the lower terms through `n = 11` and on the
`5139` candidate powers at `n = 12`. The seven-class gap was the open
question wave-2 set out to explain.

## 2. Wave-2: three independent root-cause passes

Wave-2 consists of three reports, all at `reports/wave-2/`. Each was
prepared independently — different conversations, different prompts,
different methodologies — and they reached overlapping but
distinguishable conclusions.

| Report | Branch | Diagnostic style | Distinctive contribution |
|---|---|---|---|
| [`wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md`](../wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md) | `investigate-5.5` | Black-box precision sweep | Sweeps `--dps` from `180` to `3000`; observes `2919 → 2924` drift; bottom line: `2919` invalidated, `2926` is *the strongest recorded local value* |
| [`wave-2/a198683-n12-discrepancy-root-cause.md`](../wave-2/a198683-n12-discrepancy-root-cause.md) | `investigate-cc` | White-box tolerance-policy mechanism | Pinpoints `abs_eps = rel_eps` floor in `mp.almosteq`; identifies an 8-element near-zero cluster; setting `abs_eps = 0` raises count from `2919` to `2925`; identifies three structurally-degenerate clusters (near `0`, near `i^i`, near `1`); bottom line: strictly neutral |
| [`wave-2/a198683-n12-precision-sweep-extended.md`](../wave-2/a198683-n12-precision-sweep-extended.md) | `investigate-5.2` | Extended black-box precision sweep | Sweeps `--dps` from `260` to `8000`; finds Python stabilises at `2924` from `--dps 3000` upward; adds `sys.set_int_max_str_digits(0)` guard so diagnostic runs do not crash; bottom line: cautious — `2919` invalidated, `2926` not a proof either |

## 3. Where the three wave-2 reports agree

The three reports converge on the following substantive findings.
Treat them as established by wave-2; they are the input to any wave-3
or later work.

1. **The recurrence is shared.** Both implementations use the OEIS
   principal-power definition `z^w := Exp[w Log[z]]` and the
   dynamic-programming recurrence over distinct lower-level sets.
2. **The lower terms are reproduced.** Both implementations match the
   accepted `A198683(n)` for `n = 1..11`.
3. **The candidate count at `n = 12` is shared.** Both produce `5139`
   pairwise candidate powers.
4. **The disagreement is in deduplication.** It is not a branch
   choice, not a wrap-integer ambiguity, not a recurrence variant.
5. **The Python `2919` is a heuristic artefact.** All three reports
   independently show that `2919` is not stable: precision sweeps
   raise it monotonically, and an explicit tolerance-policy fix
   raises it directly.
6. **The Wolfram `2926` is not a proof.** All three reports agree
   that it is the result returned by Wolfram's symbolic equality
   engine at the local WL version's precision, not a standalone
   certificate.
7. **The remaining residue is structural.** It lives in a small set
   of near-collision clusters in the candidate space. More precision
   alone does not close it.
8. **The right tool is interval arithmetic with outward rounding.**
   This is the path called for by the wave-2 reports and detailed in
   [`exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md).

## 4. Where the three wave-2 reports diverge

The reports differ in **diagnostic depth** and in **bottom-line
stance**. None of the divergences is a factual contradiction; they
reflect different methodological choices.

### 4.1 Diagnostic depth

| Aspect | `5.5` (contradiction) | `cc` (discrepancy) | `5.2` (precision-sweep-extended) |
|---|---|---|---|
| Highest `--dps` probed | `3000` | `260` plus structural diagnostics | `8000` |
| Highest Python `a(12)` observed | `2924` (at `--dps 3000`) | `2925` (with `abs_eps = 0` at `n = 12`) | `2924` (stable from `--dps 3000` upward) |
| Mechanism named | "Finite-precision merge heuristic" (general) | Specific `abs_eps = rel_eps` floor in `mp.almosteq` | "Numerical equality heuristic" (general) |
| Structural cluster analysis | None | Near-`0` (8 candidates), near-`i^i = e^(-π/2)` (14 candidates), near-`1` (3 candidates) | None |
| Diagnostic scripts added | None | Six `diagnose_*.py` scripts under `computations/python/` | `compute_a198683.py` docstring + `int_max_str_digits` guard |
| Scope of explanation | The 7-class gap is "an artefact" | The 7-class gap is decomposed as 6 spurious merges near zero + 1 ambiguous residue elsewhere | The 7-class gap closes to a 2-class residue under maximal Python precision |

The `cc` report is the most mechanistic: it names the line of code at
fault, identifies the eight specific candidates that get collapsed,
and recovers six of the seven missing classes by a one-line edit.
The `5.5` and `5.2` reports are behavioural twins, distinguished only
by sweep depth.

### 4.2 Bottom-line stance on `2926`

| Report | Stance |
|---|---|
| `5.5` | `2919` is *invalidated*; `2926` should be *treated as the strongest recorded local value*. |
| `cc` | Strictly neutral. `2925`, `2926`, `2927` are *all* heuristics. Declines to declare any historical number authoritative. |
| `5.2` | Cautious. `2919` is invalidated; `2926` is not a proof either; the remaining work is proof-quality equality certification. |

`5.5` is the most willing to recommend a working answer; `cc` is the
most reluctant; `5.2` lands in the middle. None of these stances is
in factual contradiction with the others — they differ in how
aggressively to treat `2926` as a *result* pending an independent
certificate.

This corpus preserves all three stances. No wave-2 report supersedes
another. The corpus README presents them side by side.

## 5. The plausible-value table

Synthesising all evidence from wave-1 and wave-2, the local pipelines
have produced the following counts under their respective heuristics:

| Variant | `a(12)` | Source |
|---|---:|---|
| Python `compute_a198683.py`, default `abs_eps = rel_eps`, `--dps 260` | 2919 | wave-1 / wave-2 (`5.5`, `cc`, `5.2`) |
| Python `compute_a198683.py`, `--dps 600` | 2920 | wave-2 (`5.5`, `5.2`) |
| Python `compute_a198683.py`, `--dps 1000` | 2921 | wave-2 (`5.5`, `5.2`) |
| Python `compute_a198683.py`, `--dps 1200..2000` | 2922 | wave-2 (`5.5`, `5.2`) |
| Python `compute_a198683.py`, `--dps 3000..8000` | 2924 | wave-2 (`5.5`, `5.2`) |
| Python with `abs_eps = 0` at the `n = 12` dedup stage only | 2925 | wave-2 (`cc`) |
| Wolfram `Union[..., SameTest -> Equal]` recurrence | 2926 | wave-1 / wave-2 |
| Canonical-exponent dedup with relaxed tolerance (`diagnose_dedup.py`) | 2927 | wave-2 (`cc`) |

Eight observed counts; up to eight pairwise-distinct candidate
classes out of `5139` whose status depends on which heuristic decides
their equality. The wave-2 reports agree that all eight are
*heuristic* outputs and that the genuine count is among them but not
distinguished by them.

The structurally-degenerate clusters identified by `cc`:

- **Near-`0`** (8 candidates produced by `(I)^(huge n=11 value)`-style
  paths). Magnitudes far below `10^-130`; the `abs_eps` floor merges
  them. This cluster accounts for **6 of the 7** classes that
  separate `2919` from `2925`.
- **Near-`i^i = e^(-π/2)`** (14 candidates that evaluate, exactly or
  near-exactly, to `0.207879...` because various sub-trees reduce to
  positive-real intermediates per the OEIS "islands of associativity"
  comment). Magnitudes near `e^(-π/2) ≈ 0.208`; imaginary residuals
  of order `10^-261` to `10^-263`. The number of genuinely-distinct
  classes in this cluster is the principal unsettled question.
- **Near-`1`** (3 candidates with `Re(e)` and `Im(e)` both below
  `10^-1300`). The number of genuinely-distinct classes here is also
  unsettled.

A Schoenfield-style equivalence-class extension to `n = 12` derived from
running [`compute_a198683.py`](../../computations/python/compute_a198683.py)
and its instrumented siblings
[`dump_n12_candidates.py`](../../computations/python/dump_n12_candidates.py),
[`group_n12_candidates.py`](../../computations/python/group_n12_candidates.py),
and [`probe_tentative_classes.py`](../../computations/python/probe_tentative_classes.py)
at `--dps 260` (initial dump) and `--dps in {260, 500, 1000}` (probe) is
preserved at
[`../../data/a198683-n12-equivalence-classes.txt`](../../data/a198683-n12-equivalence-classes.txt).
It lists all 5139 candidates, grouped under a probe-refined partition
that starts from the strict-policy partition (2925 classes, the
abs_eps=0 fix from wave-2 `cc`) and refines each of the four tentative
classes using multi-precision algebraic probing:

| Strict tentative class | Members | Probe verdict at dps ∈ {260, 500, 1000} | Refined partition |
|---|---|---|---|
| `25` (near-`1`) | `{25, 1404, 4239}` | `diff_Re(e_25, e_1404) = 2.306566301e-1305` **stable** at all three dps (not numerical noise); `diff_Re(e_1404, e_4239) = 0` exact | **splits** into `{25}` ∪ `{1404, 4239}` (+1 class) |
| `561` (near-`i^i`) | 14 members | pairwise `diff_Re`, `diff_Im` shrink ~`10^-dps` with precision (noise) | conclusive merge: all 14 algebraically equal to `i^i = e^(-π/2)` |
| `2199` (near-`0`) | `{2207, 3777}` | pairwise differences at precision floor for every dps | conclusive merge: algebraically equal |
| `2924` (near-`0` overflow) | `{57}` | `|Im(e)| ~ 10^41232...` cannot be reduced mod `2π` at any finite precision | **tentative** — equality with any other candidate undecidable at finite precision |

The probe-refined partition gives exactly **2926 classes** — matching
Wolfram's `Union[..., SameTest -> Equal]` count. The `+1` over strict's
2925 is the cluster C split: `idx=25` separates from `{1404, 4239}`
because their level-12 exponents differ by `2.306566301e-1305`
algebraically (stable across all probed precisions; would shrink with
precision if it were numerical noise).

Of the 2926 refined classes, **2925 are conclusive** (1389 singletons
+ 1536 multi-member classes; multi-precision evidence consistent across
dps) and **1 is tentative** (the overflow singleton `{57}`, which
cannot be probed because its `|Im(e)|` is astronomical and beyond mod-2π
reduction at finite precision).

'Conclusive' here means *multi-precision heuristic evidence agrees across
dps ∈ {260, 500, 1000}*, not a formal proof. A certified pipeline (see
[`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md))
would still be needed to convert "all probed precisions agree" into
"proved", and to settle the one remaining tentative class.

## 6. Remaining unsettled questions

The following questions are explicitly open after wave-2. Each is the
input to some piece of wave-3 or later work.

### Q1. What is the true value of `A198683(12)`?

The eight-element band `{2919..2927}` is overdetermined by heuristics
but underdetermined by certificates. Specifically:

- `2919..2924` are excluded as Python-side artefacts at insufficient
  tolerance (precision-sweep evidence from `5.5` and `5.2`).
- `2925` is excluded as the Python-side result after one tolerance-policy
  fix at `n = 12`, but it is not a proof; the `cc` report explicitly
  declines to certify it.
- `2926` is the Wolfram side and the strongest local computation, but
  no audit-trail certificate independent of Wolfram's symbolic engine
  exists.
- `2927` arises from a strict canonical-exponent dedup with relaxed
  tolerance; it is a witness that strict structural comparison can
  over-split.

The most likely value, given the structural cluster analysis in `cc`,
is `2926`. None of the wave-2 reports certifies this, and none rules
out `2925` or `2927`.

### Q2. How many of the 14 "near-`i^i`" candidates are mathematically equal?

This cluster is the principal source of the `2925 / 2926 / 2927`
ambiguity. The relevant question is, for each pair `(p1, p2)` of the
14 parenthesisations:

- Does the algebraic tree structure force `p1 = i^i = e^(-π/2)`
  exactly, via the OEIS "islands of associativity" mechanism?
- Or does `p1` lie infinitesimally to one side of `e^(-π/2)`, with a
  tiny but nonzero imaginary residual?

No wave-1 or wave-2 heuristic can answer this without either:

- A proof-quality interval evaluator that returns
  `equal / not-equal / undecided`, with `undecided` driving adaptive
  precision, or
- A symbolic-algebraic argument that catalogues the sub-tree
  structures that genuinely reduce to `i^i` and shows which 14
  parenthesisations have such sub-trees.

### Q3. How many of the 3 "near-`1`" candidates are mathematically equal?

A smaller version of Q2. The `cc` report's canonical-form diagnostic
splits the 3-candidate Python class into `{25}` and `{1404, 4239}`,
but the diagnostic is itself heuristic. The candidate pair
`(1404, 4239)` shares `Re(e)` exactly at the working precision and
differs only in tiny imaginary noise; whether the difference is
genuine or a numerical artefact is the open question.

### Q4. Are there any structural collisions wave-2 has missed?

All three wave-2 reports look at the deduplicator's output; none
exhaustively enumerates the algebraic identities that could force
distinct parenthesisations to coincide. The OEIS comment by Sloane
(2015) records one such identity:

> `(i^i)^Y / (i^Y)^i = exp(-2π)` for `Y = ((i^i)^i)^i`.

This says that `(i^i)^Y` and `(i^Y)^i` are *not* equal but differ by
the transcendental factor `e^(-2π)`. The implication for `a(n)` is
that some apparent coincidences are spoiled by branch-cut shifts
that produce factors like `e^(-2π)` rather than `e^0`. Whether the
14-candidate "near-`i^i`" cluster contains any pair that differs by
such a factor (vs. genuinely equal pairs) is not addressed by wave-2.

### Q5. Is the Wolfram `2926` itself stable?

The wave-1 Wolfram report is the only single-source local
computation that reaches `2926` directly. Rerunning it under a
different Wolfram version, or under a different `Equal` tolerance,
could in principle return a different value. The corpus does not
currently have a Wolfram-side precision-sweep analogue to the
Python-side sweep in `5.5` and `5.2`.

### Q6. Can the certificate-grade pipeline actually be built?

This is the question the wave-3 feasibility study answers. The
short version, per
[`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md):
yes, via the `src/Numerics/python` package plus three engine
extensions (a `π` constant, `sin` / `cos` on bounded ground
intervals, a complex-interval wrapper) plus an application-layer
`i^Z`-form pipeline. The remaining question is whether the
work gets done.

## 7. What "settled" would look like

A wave-4 (or later) certificate would consist of:

1. An audit trail listing every one of the `5139` candidate powers at
   `n = 12` and, for every ordered pair, a verdict in
   `{Equal, NotEqual, Undecided-with-precision-cap}`.
2. Zero `Undecided` verdicts, or — failing that — a small explicit
   list of `Undecided` clusters with an algebraic-identity argument
   resolving each.
3. A reproducible engine binding (commit hash, working precision
   used, total wall-clock) so the certificate can be rerun.
4. A conditional statement of the form `a(12) = N` or
   `a(12) ∈ S` (with `|S| ≤ 3`) plus the explicit cluster
   descriptions.

The wave-3 feasibility study sketches the engine that would produce
(1)–(3). The cluster descriptions in (4) are already provided by the
`cc` report.

## 8. Reading order

For someone new to the corpus, the recommended path through wave-1 →
wave-2 → wave-3 is:

1. [`../README.md`](../README.md) — the corpus README (current-state
   map of the conflict).
2. [`../../README.md`](../../README.md) — the A198683 corpus root.
3. Either one of the two **wave-1 result reports** for context on
   what the two original claims were:
   - [`../wave-1/a198683-n12-python-mpmath-2919.md`](../wave-1/a198683-n12-python-mpmath-2919.md)
   - [`../wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md`](../wave-1/a198683-n12-wolfram-2926__2026-05-20__20-31-16-000000.md)
4. **Any one of the three wave-2 root-cause reports** for a working
   understanding of the discrepancy. The mechanistic
   [`../wave-2/a198683-n12-discrepancy-root-cause.md`](../wave-2/a198683-n12-discrepancy-root-cause.md)
   is the deepest; the precision-sweep diagnostics in the other two
   are independent corroboration:
   - [`../wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md`](../wave-2/a198683-n12-contradiction-root-cause__9e7681d48134.md)
   - [`../wave-2/a198683-n12-discrepancy-root-cause.md`](../wave-2/a198683-n12-discrepancy-root-cause.md)
   - [`../wave-2/a198683-n12-precision-sweep-extended.md`](../wave-2/a198683-n12-precision-sweep-extended.md)
5. **This synthesis** for the cross-cuts and the unsettled-questions
   inventory.
6. [`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md)
   for the proposed certified pipeline.
7. [`../exploratory/A198683-report-2.md`](../exploratory/A198683-report-2.md)
   for the original strategy document the feasibility study
   operationalises.

## 9. References

Primary local references:

- Wave-1 result reports listed in §1.
- Wave-2 root-cause reports listed in §2.
- Wave-3 feasibility study:
  [`a198683-numerics-interval-feasibility.md`](a198683-numerics-interval-feasibility.md).
- Corpus README: [`../../README.md`](../../README.md).
- Reports index: [`../README.md`](../README.md).

Supporting infrastructure:

- Python recurrence:
  [`../../computations/python/compute_a198683.py`](../../computations/python/compute_a198683.py)
- Python diagnostics (added by wave-2 `cc`): `diagnose_dedup.py`,
  `diagnose_pairs.py`, `diagnose_tol.py`, `diagnose_naive.py`,
  `diagnose_levels.py`, `diagnose_tol_simple.py` (all under
  [`../../computations/python/`](../../computations/python/)).
- Wolfram recurrence:
  [`../../computations/wolfram/a198683-n12-check__2026-05-20.wl`](../../computations/wolfram/a198683-n12-check__2026-05-20.wl).

OEIS / external:

- OEIS entry: <https://oeis.org/A198683>.
- Local OEIS snapshot:
  [`../../sources/oeis-entry__2025-11-05.txt`](../../sources/oeis-entry__2025-11-05.txt).
- Schoenfield table for `n = 1..11`:
  [`../../sources/schoenfield-a198683.txt`](../../sources/schoenfield-a198683.txt).
