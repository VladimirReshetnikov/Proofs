# `src/Lean/` proof-simplification review

- Created (UTC): 2026-07-08T06:54:00Z
- Repository HEAD: 088cceb8f (branch `claude/lean-coq-proofs-review-71f4e2`)

A review of every Lean and Rocq/Coq proof under `src/Lean/` with the goal of
making them **simpler, shorter, faster to build, and easier to navigate**,
without changing any proved theorem statement or public certificate surface.

## Scope

| Tree | Files | Lines | Role |
|------|-------|-------|------|
| `CoqProofs/` | 27 `.v` | ~11.7k | Rocq/Coq ports of the Lean modules |
| `LeanProofs/` | 26 `.lean` | ~22.2k | the original Lean proofs |
| `SetTheory/` (Coq) | 12 `.v` (+`PAHF.v` 21k) | ~28k | Closure≡ZF + PA/HF + Busy Beaver |
| `SetTheory/lean/` | 12 `.lean` (+`PAHF.lean` 25k) | ~35.5k | Lean port of the above |

`BusyLean/` holds only docs (no proof sources) and `Oeis/A198683/` holds only
Python/Wolfram research data, so both are out of scope for proof review.

## Method

Seven read-only survey agents analyzed the clusters in parallel (Coq
non-A198683, Coq A198683, Lean non-A198683, Lean A198683, SetTheory core both
languages, PAHF/BusyBeaver Coq, PAHF/BusyBeaver Lean), while full build
baselines were taken for both languages. Every applied change was re-verified by
recompilation (`coqc` per module for Coq; `lake build` for Lean).

## Build baselines (this machine, 2026-07-08)

Rocq 9.0.1 has **`native_compute` disabled at configure time** (it silently
falls back to `vm_compute`), so `vm_compute` is the ceiling for Coq computation
here — the compute-heavy certificates cannot be sped up by switching engines.

Coq build hot spots (full clean `CoqProofs` build ≈ 675 s baseline):

| Module | Baseline | Note |
|--------|----------|------|
| `A199812.v` | 275 s | ordinal-note enumeration, `vm_compute` to n=12 |
| `A198683N12Probe.v` | 98 s | 5139-row partition certificate |
| `A198683SchoenfieldRows.v` | 84 s | 16796-row trie reconstruction |
| `WolframBooleanCertificates.v` | 71 s | ~1330-item generated certificate |
| `A198683Schoenfield.v` | 50 s | class-count certificate |
| `A002845.v` | 47 s | sparse-log table to n=14 |
| `SetTheory/PAHF.v` | 35 s | 21k-line bi-interpretability certificate |

Lean: after `lake exe cache get` (a one-time ~13 min mathlib decompress in a
fresh worktree), the `LeanProofs` library builds in ~9 min; the standalone
`SetTheory/lean` library builds in ~45 s (`PAHF.lean` 29 s, everything else
1–3 s, all mathlib-free). `defaultTargets = ["LeanProofs"]` means a bare
`lake build` in `src/Lean` does **not** build the `SetTheory` lib — build it
with `lake build SetTheory` or from `SetTheory/lean`.

## Changes applied and verified

### Coq (committed)

- **~855 lines of duplicated certificate data removed** in
  `A198683Schoenfield.v`, `A198683SchoenfieldRows.v`, `A198683N12Probe.v`.
  The `labelsSeven..Ten` / `rowsSeven..Ten` tables are exact Catalan-numbered
  prefixes of the level-11 tables, and `n12ProbeRefinedClassWitnesses` is
  `n12StrictClassWitnesses ++ [1404]`. Each equality was proved against the
  compiled `.vo` before the literals were deleted; every `schoenfield_*` /
  `rows_*_reconstruct` certificate still re-checks it via `vm_compute`.
- **`A199812.v`**: `a199812_values_through_eleven` is now derived from the
  individual value lemmas by rewriting instead of a second `vm_compute` of the
  whole n=1..11 enumeration (~40 s off the module build; the n=12 `vm_compute`
  is the irreducible remaining cost).
- **Dead code**: dropped the superseded unprimed `checkStep` in
  `EquationalLogic.v` and the never-invoked `Ltac` cluster
  (`contradict_{wolfram,meredith}_table` etc.) in `WolframBoolean.v` (~78 lines).
- **Dedup / golfing**: `Sheffer.v`/`Nicod.v` `eval_toNand`/`eval_toNor` collapsed
  to the compact tactic already used in `WolframBoolean.v`; `TinyExponentTower.v`
  `towerBaseInt_cast` alias removed; `RationalFloorOrbit.v` even/odd `div2` split
  factored into `even_double`/`odd_double`.
- **`SetTheory/Fol.v` + `Calculus.v`**: the renaming-past-instantiation identity
  proved inline four times in `Prov_rename` is now `Fol.rename_inst_push`.
- **Build config**: `_CoqProject` (CoqProofs) lists all 27 modules;
  `SetTheory/_CoqProject` now includes the BusyBeaver trio and the `Audit`
  capstone, so `make` builds the full audited development.

Net: ~1050 Coq lines deleted / ~170 added; full clean `CoqProofs` rebuild
675 s → 580 s; the SetTheory Coq chain (incl. PAHF and Audit) still builds.

### Lean

- **`A198683N12Symbolic.lean`**: the ten `nearOne25_ne_nearOne4239_of_*`
  theorems mirror the `nearOne1404` chain statement-for-statement, and
  `nearOne1404 = nearOne4239` is already proved. Deleted the nine intermediate
  4239 twins and re-proved the terminal `..._of_endpoint_bounds` as a one-line
  bridge (`rw [← nearOne1404_eq_nearOne4239]`) — the named final result is
  preserved, ~375 lines removed. This module is a leaf (only the root imports
  it) and the whole 4239 chain was internal scaffolding, so nothing downstream
  is affected.
- **`A000081.lean`**: removed the dead trivial `eval_eq_sharedEval` bridge.
- **`PowTower.lean`**: `parenthesizations_one` now reuses `parenthesizations_one_eq`
  instead of a redundant `native_decide`.
- **`RationalFloorOrbit.lean`**: added four `/-! ## -/` section dividers over the
  four phases (Stern–Brocot generator / inverse index / `Rat` bridge /
  enumeration) of a previously marker-free 420-line file.
- **`SetTheory/lean/Fol.lean` + `Calculus.lean`**: mirrored the Coq
  `rename_inst_push` dedup to keep the two ports in sync.

### Lean, phase 2 (navigability — committed)

- **Split `SetTheory/lean/PAHF.lean` (25,665 lines) into three modules** at its
  verified namespace boundaries: `PAHF/AckermannHFCore.lean` (Block A, semantic
  core), `PAHF/PASyntax.lean` (Block B, PA syntax + `BProv`), and
  `PAHF/Interpretation.lean` (Block C, interpretation + certificates), with
  `PAHF.lean` a thin re-export so `SetTheory.PAHF` and every qualified name are
  unchanged. Pure relocation. Three perspective-diverse adversarial audits
  (reference-direction, scoping/attributes, declaration-integrity) confirmed no
  backward references, no scope/attribute/universe state crossing a boundary,
  and clean cut points; verified with `lake build` (16 jobs). Editing one block
  now re-elaborates ~9–17 s instead of the whole file.
- **Section dividers added to the five marker-free giant files**:
  `A198683.lean` (11), `A198683Tower.lean` (11), `A198683N12Symbolic.lean` (8),
  `A198683SchoenfieldRows.lean` (6), and Coq `SetTheory/PAHF.v` (12), carving
  each into named phases without touching a proof. (`RationalFloorOrbit.lean`
  got its four dividers in phase 1.)

## Recommended, not yet done (prioritized)

1. **`PAHF` deductive scaffolding is 74% of the file and builds toward an
   *uninhabited* target** (`DeductiveBiInterpretationCertificate`). It is not
   dead — `Audit.{v,lean}` type-checks most of it — but it is a scope decision
   for Vladimir: finish it (inhabit the certificate), keep growing it, or, if the
   semantic certificate is the real deliverable, treat it as optional weight. ~78
   genuinely-dead (unreferenced *and* un-audited) decls in Coq `PAHF.v` (~1062
   lines) could be dropped after an intent check.
2. **Lean Schoenfield/Rows data dedup was deliberately NOT applied.** Unlike
   Coq's lazy `firstn`, a Lean `native_decide` over `labelsEleven.take k`
   compiles the full 16796-element `labelsEleven` into every small check, which
   would likely make the build *slower* — a poor trade against "faster to build."
   Revisit only if measurement shows no regression.
3. Smaller Coq/Lean items surfaced by the survey but left alone as low-value or
   surface-touching: `A198683N12Magnitude` triplicated one-hot flag families
   (evidentiary "independent columns agree"), `RationalFloorOrbit.v` unused
   `Qeq`-level mirror theorems, the `WolframBoolean*Certificates` encoding
   (shrinkable only by regenerating from the Lean-side generator).

## Guardrails (looks removable, is not)

- The `A198683.lean` "bound ladder" of weaker `a198683 7` corollaries is
  **README-documented intentional exposition**, not dead code — keep it.
- `Fol.seal_valid` / `Fol.Sat_fIff` look unused in the SetTheory core but are
  required by `PAHF`.
- `Forward.{v,lean}` / `Reverse.{v,lean}` are superseded *for the `T_iff_ZF`
  theorem* but are audited and pedagogically distinct (shallow embedding, the
  Hosting refinement) — keep.
- `Audit.{v,lean}` and `BusyBeaverMathlib.{v,lean}` are live but outside the
  default build closure; they silently bit-rot. Consider a build/CI target.
- The many `a002845_eq_*` / `a199812_eq_*` bridge theorems are intentional,
  README-documented equivalences mirrored across Coq and Lean — keep.
