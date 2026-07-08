# `src/Lean/` Lean↔Coq parity port and deep-fix pass

- Created (UTC): 2026-07-08T15:15:00Z
- Repository HEAD: c19b998bc0f148d11277790c1a448bfd8a39113a (branch `claude/lean-coq-proofs-review-6d6444`)

The follow-up to [`proof-simplification-review-2026-07.md`](proof-simplification-review-2026-07.md)
(same goal statement, next session): where that pass simplified and reorganized,
this pass closes the **content gaps between the Lean originals and their
Rocq/Coq ports** and lands the deeper build-speed fixes that needed new
machinery rather than deletion.

## The PAHF porting backlog

The bi-interpretability program in `SetTheory/lean/SetTheory/PAHF/` kept moving
after the last Coq sync (`0993b68ca`, 2026-07-07): a declaration-level diff of
the Lean tree against that snapshot showed **380 new declarations**
(~14.3k Lean lines) with no Coq counterpart — the PA-provability layer for
Gödel-beta halving traces, term-parametric HF-membership formulas, and the
distinguisher/extensionality program, plus supporting Ackermann-HF semantics.

Port method: one foundational block (new formula macros, trace certificates,
substitution bookkeeping) was ported first so that the term-parametric macros
could be *defined with iterated `Term.rename S`*, which makes the Lean side's
big-`simp` substitution lemmas hold in Coq by plain `reflexivity`. The
remaining ~334 lemmas were then ported in ten dependency-ordered blocks by
parallel agents, each self-verified against the compiled `PAHF.vo` with
`Axiom` stubs for cross-block dependencies; blocks were integrated in order
(stubs stripped, full `coqc` recompile at each step), so no axiom ever
entered the committed file.

Status: **complete — 380/380 declarations ported**; `PAHF.v` grew from
21,517 to 36,500 lines and compiles in ~47 s (Audit.v re-checked at every
integration step).

| Block | Content | Decls | Status |
|-------|---------|-------|--------|
| A | macros, traces, subst bookkeeping, HF semantics | 46 | committed `04449ba2d` |
| B1 | PA arithmetic `_all`/`_terms` closures | 33 | committed `c80d0ab88` |
| B2 | object-level order (`leAt`/`ltAt`/`leTermAt`/`ltTermAt`) | 35 | committed `c80d0ab88` |
| B3 | divisibility and halving steps (`dvdAt`/`div2StepAt`) | 12 | committed `c80d0ab88` |
| B4 | Euclidean-remainder uniqueness chain (`remAt`/`remTermAt`) | 38 | committed `811f88657` |
| B5 | beta-modulus and opened-body `betaAt`/`betaTermAt` | 34 | committed `811f88657` |
| B6 | indexed beta wrappers (`betaAtConstIdx`/`betaTermAtTermIdx`) | 29 | committed `811f88657` |
| B7 | beta-div2 witness/steps/bit lemmas | 24 | committed `811f88657` |
| B8 | HF-membership opened-body eliminations (`hfMemAt`) | 44 | committed `3e928ef56` |
| B9 | extensionality + distinguisher macros and semantics | 40 | committed `c80d0ab88` |
| B10 | distinguisher packaging + translated HF axioms | 36 | committed `3e928ef56` |

## Other parity gaps closed

- `CoqProofs/FloorSqrtSum.v`: the Nat-level closed form
  `sum_floor_sqrt_eq` (truncated `-` and `/`), via the subtraction-free key
  identity `6·Σ + s(s+1)(2s+1) = 6·s·(n+1)`; divisibility by 6 falls out as
  `six_divides_sqrt_term`.
- `CoqProofs/A198683N12Magnitude.v`: the three magnitude flag lists are again
  three *independent literal transcriptions* of the Lean TSV columns (they had
  been collapsed to a single generated `oneHot` term, which made the
  "independent columns agree" theorems vacuous); the generated form survives
  as a `vm_compute` cross-check per list.
- `SetTheory/BusyBeaverMathlib.v`: the `EncodedInputBudget` record bundled as
  assumptions four statements the Lean side proves; they are now real Coq
  theorems (`linear_mul_le_two_pow_pred_of_large`,
  `nat_size_linear_le_self_of_large` via a `nat_size` analogue of `Nat.size`,
  and the two `init_wrapper_state_count` bounds) and the record is gone.
  `Audit.v` prints their assumptions (closed) and separates the remaining
  assumption interfaces under an explicit "NOT theorems" banner. A new
  root-workspace `SetTheory/lean/SetTheory/AuditMathlib.lean` prints the
  axioms of the two unconditional busy-beaver capstones
  (`[propext, Classical.choice, Quot.sound]`), closing the
  bit-rot gap flagged by the previous report.
- `CoqProofs/WolframBoolean.v`: the two Lean capstones (every short
  Sheffer-characterizing equation has a finite non-Wolfram countermodel;
  Wolfram's six operations are minimal for single equational axioms) are now
  proved in Coq about the original eager check, axiom-free, in 4.6 s — the
  blocker was Stdlib's non-short-circuiting `forallb`/`existsb` under
  `vm_compute`, solved by lazy match-based combinators with bridge
  equalities plus an `Eval`-hoisted countermodel pool. The stroke/classical
  machinery of `Nicod.v` and `WolframBoolean.v` is deduplicated into the
  shared `Sheffer.v` (~235 LOC), restoring the Lean architecture; Nicod's
  Metamath label comments are ported.
- `CoqProofs/PowTower.v`: the lexical-vs-recursive value-set equivalence
  (`In_evalList_iff_recursiveValueList`) is now proved for **all** `n` and an
  arbitrary evaluation type, mirroring Lean's `valueSet_eq_recursiveValueSet`
  (previously only an `n ≤ 3` instance check). Its corollary
  `valueCount_eq_recursiveValueList_length` (the recursive list is `NoDup`)
  lets the OEIS certificates A199812/A002845/A000081 count "distinct values
  of all parenthesizations" rather than "recurrence output".
- `CoqProofs/TinyExponentTower.v`: the three analytic hypotheses are
  discharged with coq-interval, making the floor identities unconditional.
- new `CoqProofs/A198683N12Bounds.v`: the disputed `a(12)` endgame boxes
  (`rho_bounds`, `theta_box`, the `nearOne1404`/`nearOne25` norm separation)
  proved directly with `interval`, replacing ~1900 lines of Lean rational-box
  propagation. Both interval files carry the standard coq-interval
  PrimInt63/PrimFloat evaluator axioms (plus classical reals) — the accepted
  footprint for machine-arithmetic certificates, not admits.
- `CoqProofs/FermatFour.v`: **Fermat's Last Theorem for exponent 4 is proved
  unconditionally** — the classical descent (Pythagorean-triple
  parametrization → double descent → well-founded induction on `|c|`) is
  constructed from scratch over Stdlib `Znumtheory`, discharging the descent
  step the file previously took as a section hypothesis
  (`fermat_four_no_positive_nat_solutions_unconditional` and the square-RHS
  form; axiom-free).

## Build-speed fixes

- `CoqProofs/A199812.v`: **242 s → 2.4 s** (~100×). The cost was the
  quadratic `dedupBy` over structurally-shared CNF trees, not the
  `vm_compute` evaluations: a fueled bottom-up mergesort-dedup over
  `onoteCompare` (with `onoteCompare_eq_iff` soundness) plus a single
  `Eval vm_compute` value table changes the complexity class — and made the
  n = 13 value (20287, Lean parity) free.
- `CoqProofs/A002845.v`: 39 s → 18.3 s while extending the certified values
  from n = 14 to n = 17. Same sort-based dedup, but tail-recursive with an
  `N`-valued count table: reading a >~120k unary `nat` out of the Coq VM
  overflows the OCaml stack, so lengths are computed in binary. The old
  quadratic path survives as a cross-check through n = 11.

## Simplifications

- `CoqProofs/FermatFour.v`: before the unconditional descent construction, the
  three descent-granularity sections were made to share one pair of generic
  public wrappers (the 15-line nat→Z transport is written once).
- `CoqProofs/ArctanSquareIdentity.v`: dead `atan_add_rational` `Ltac` removed
  (chaining its two sentences into one tactic stack-overflows on some goals;
  the sequential call-site pattern is the working form and stays).
- `CoqProofs/RationalFloorOrbit.v`: five section banners mirroring the Lean
  chapter structure.

## Verification record

Every commit lists its `coqc`/`lake` verification line. Baselines
(2026-07-08, this machine): all 27 `CoqProofs` modules, all 12 `SetTheory`
Coq modules, the root `LeanProofs` workspace (2358 jobs), and the standalone
`SetTheory/lean` workspace all build cleanly at the starting commit.

A final full `coqc` sweep after the port confirms **all 25 non-interval
`CoqProofs` modules and all 12 `SetTheory` Coq modules green** (37/37, zero
failures); `TinyExponentTower.v`, `A198683N12Bounds.v`, and `FermatFour.v`
build separately (the last is a heavy from-scratch descent). `PAHF.v` is now
36,500 lines (from 21,517) and re-checks in ~47 s solo; `Audit.v` re-checks
the whole audited surface. The two Lean workspaces are unchanged in structure
and build clean (`lake build` root: 2358 jobs; `lake build SetTheory` +
`SetTheory.AuditMathlib`).

## Net effect

The Coq side now mirrors the Lean development declaration-for-declaration in
the PAHF bi-interpretability program (the last real parity gap), and several
theorems that were *weaker* in Coq than in Lean are now equal or stronger:
FLT-4 is unconditional in both; the Wolfram-minimality capstones and the
BusyBeaver budget lemmas are real Coq theorems; the A198683 `a(12)` analytic
endgame is interval-certified in Coq where Lean used a hand-built box cascade;
and A199812/A002845 reach further (n=13 / n=17) and count provably-distinct
values. Two compute-heavy certificates dropped from minutes to seconds
(A199812 ~100×). No theorem statement or public certificate surface was
weakened anywhere.
