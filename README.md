# Proofs

**Machine-checked mathematics in Lean 4 and Rocq/Coq.**

`Proofs` is [Vladimir Reshetnikov's](https://github.com/VladimirReshetnikov)
public collection of formal mathematics and auditable computational
certificates. It ranges from classical number theory and exact analytic
identities to OEIS power-tower sequences, propositional and equational logic,
alternative foundations of set theory, and Busy Beaver results.

Lean 4 with mathlib is the primary environment. Rocq (formerly Coq)
developments provide independent or complementary checks. Supporting Python
and Wolfram Language programs are retained when they generate, reconstruct, or
audit certificate data; they are proof support, not substitutes for kernel
checking. The repository distinguishes semantic theorems, conditional
theorems, checked facts about retained data, and heuristic evidence.

**Toolchains:** Lean `4.31.0` · mathlib `v4.31.0` · Rocq `≥ 9.0`
(developed against `9.0.1`) · [MIT-0](LICENSE)

## Highlights

| Area | Machine-checked result | Entry point |
| --- | --- | --- |
| Classical mathematics | Fermat's Last Theorem for `n = 4`, an exact floor-square-root sum, a bijective rational orbit, and exact trigonometric, arctangent, and power-tower identities | [`LeanProofs/`](LeanProofs/) |
| OEIS and power towers | Formal semantics and exact finite certificates for A000081, A002845, A158415, A198683, and A199812 | [OEIS and power towers](#oeis-and-power-towers) |
| Logic | Nicod's single NAND axiom, Wolfram's single Sheffer-stroke equation, Meredith's basis, and checked equational certificates | [`LeanProofs/WolframBoolean.lean`](LeanProofs/WolframBoolean.lean) |
| Set theory | Full deductive equivalence of Vladimir's Closure axiomatization and ZF, checked independently in Rocq and Lean | [`SetTheory/`](SetTheory/README.md) |
| Computability | Busy Beaver domination results; exact score proofs `Σ(2) = 4` and `Σ(3) = 6` in Lean and Rocq; exact Rocq proofs of `Σ(4) = 13` and times `BB(2) = 6`, `BB(3) = 21`, `BB(4) = 107` | [`SetTheory/`](SetTheory/README.md), [`CoqBB2/`](CoqBB2/README.md), [`CoqBB3/`](CoqBB3/README.md), [`CoqBB4/`](CoqBB4/README.md) |
| Reproducible research | Source snapshots, exact generators, retained data, investigation reports, and proof-status ledgers for difficult certificate projects | [`Oeis/`](Oeis/) |

## Repository map

| Path | Purpose |
| --- | --- |
| [`LeanProofs/`](LeanProofs/) | Root Lean 4/mathlib library and generated certificate modules. [`LeanProofs.lean`](LeanProofs.lean) is its import surface. |
| [`CoqProofs/`](CoqProofs/README.md) | Rocq ports of the root Lean developments, with their parity limits documented explicitly. |
| [`SetTheory/`](SetTheory/README.md) | Closure ↔ ZF, first-order logic and completeness, PA/HF work, Busy Beaver formalizations, and the accompanying article. |
| [`CoqBB2/`](CoqBB2/README.md) | Vendored upstream Rocq proof of the two-state Busy Beaver time bound, with repository-local hardening. |
| [`CoqBB3/`](CoqBB3/README.md) | Vendored upstream Rocq proof of the three-state Busy Beaver time bound, with the same kernel hardening. |
| [`CoqBB4/`](CoqBB4/README.md) | Vendored upstream Rocq proof of the four-state Busy Beaver time bound, likewise hardened and bridged to the local machine model. |
| [`Oeis/A158415/`](Oeis/A158415/) | Exact Wolfram generator and research notes behind the A158415 radical certificates. |
| [`Oeis/A198683/`](Oeis/A198683/README.md) | Wave-organized source, data, computation, and report corpus for the disputed value of A198683(12). |
| [`docs/reports/`](docs/reports/) | Repository-wide comparison and status reports. |

There is no `src/` prefix in this repository: all paths above are relative to
the repository root.

## Formalizations

### Exact identities and enumerations

| Lean module | Result |
| --- | --- |
| [`FermatFour.lean`](LeanProofs/FermatFour.lean) | The positive-natural-number `n = 4` case of Fermat's Last Theorem, via the stronger classical descent statement. |
| [`FloorSqrtSum.lean`](LeanProofs/FloorSqrtSum.lean) | A closed form for `∑ k ∈ [1,n], ⌊√k⌋` as an exact natural-number identity. |
| [`RationalFloorOrbit.lean`](LeanProofs/RationalFloorOrbit.lean) | The orbit of `q ↦ 1 / (1 - q + 2⌊q⌋)` from `0` visits every nonnegative rational exactly once. |
| [`TinyExponentTower.lean`](LeanProofs/TinyExponentTower.lean) | The exact floor offset `2811012357389` for a five-level tiny-exponent tower. |
| [`TrigGoldenRatio.lean`](LeanProofs/TrigGoldenRatio.lean) | `sin 9° + sin 21° + sin 39° = φ / √2`. |
| [`ArctanSquareIdentity.lean`](LeanProofs/ArctanSquareIdentity.lean) | An exact eleven-term quadratic identity among `arctan` values. |

A representative public theorem is:

```lean
theorem fermat_four_no_positive_nat_solutions
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 + b ^ 4 ≠ c ^ 4
```

### OEIS and power towers

[`LeanProofs/PowTower.lean`](LeanProofs/PowTower.lean) supplies the shared
lexical syntax for binary parenthesizations and proves the equivalence between
the canonical semantic value set and the recursive, finite, memoized, and
hash-set presentations used by certificate code.
[`LeanProofs/SparseBinary.lean`](LeanProofs/SparseBinary.lean) provides the
verified sparse arithmetic used by the natural-power certificates.

| Sequence | Formalized interpretation | Unconditional Lean result |
| --- | --- | --- |
| [A000081](https://oeis.org/A000081) | Distinct positive-real functions represented by parenthesizations of `x^x^...^x` | Values through `n = 5`, ending in `9` |
| [A002845](https://oeis.org/A002845) | Distinct natural values of parenthesizations of `2^2^...^2` | Values through `n = 18`, ending in `125608` |
| [A158415](https://oeis.org/A158415) | Distinct real values of expressions over `1`, unary `√`, and binary `+`, counted by symbol size | Values through `n = 15`, ending in `791` |
| [A198683](https://oeis.org/A198683) | Distinct principal-complex-power values of parenthesizations of `i^i^...^i` | Exact values through `n = 7`; `16 ≤ a(8) ≤ 127` |
| [A199812](https://oeis.org/A199812) | Distinct ordinal values of parenthesizations of `ω^ω^...^ω` | Values through `n = 13`, ending in `20287` |

The main modules are
[`A000081.lean`](LeanProofs/A000081.lean),
[`A002845.lean`](LeanProofs/A002845.lean),
[`A158415.lean`](LeanProofs/A158415.lean),
[`A158415Fifteen.lean`](LeanProofs/A158415Fifteen.lean),
[`A198683.lean`](LeanProofs/A198683.lean),
[`A198683EightBounds.lean`](LeanProofs/A198683EightBounds.lean), and
[`A199812.lean`](LeanProofs/A199812.lean).

#### The A198683(12) checkpoint

A198683(12) is deliberately presented as an open formalization checkpoint,
not as a proved value. The retained recurrence produces `5139` candidates,
and the probe-refined data partition has `2926` classes, but checking those
facts about retained data does not by itself prove the semantic cardinality.

The current Lean endgame provides:

- an explicit conditional decision tree in
  [`A198683N12Certificate.lean`](LeanProofs/A198683N12Certificate.lean);
- an unconditional proof of the extremely close near-`1` separation in
  [`A198683N12Endpoints.lean`](LeanProofs/A198683N12Endpoints.lean);
- a certified lower bound on the overflow witness in
  [`A198683N12OverflowBound.lean`](LeanProofs/A198683N12OverflowBound.lean);
- checked retained-data and exact symbolic subcertificates in the other
  `A198683N12*.lean` modules.

An exact theorem for `a(12)` still requires the wide semantic partition
witness and resolution of the overflow candidate's isolation. The
[wave-5 status ledger](Oeis/A198683/reports/wave-5/a198683-formalization-status-and-remaining-work.md)
is the authoritative proved/conditional/data-certified/heuristic inventory.

### Propositional and equational logic

- [`Sheffer.lean`](LeanProofs/Sheffer.lean) defines NAND and NOR, a
  one-stroke formula language, and truth-preserving translations from ordinary
  propositional formulas.
- [`Nicod.lean`](LeanProofs/Nicod.lean) formalizes Nicod's one-axiom,
  one-rule NAND calculus, proves soundness, and derives the standard
  Łukasiewicz Hilbert basis.
- [`EquationalLogic.lean`](LeanProofs/EquationalLogic.lean) implements a small
  first-order equational proof checker and proves its soundness.
- [`WolframBoolean.lean`](LeanProofs/WolframBoolean.lean) uses checked
  certificates to connect Wolfram's single equation, Meredith's two-axiom
  system, the Sheffer axioms, and Huntington's Boolean-algebra basis. It also
  proves the six-operation equation minimal against every canonical candidate
  with at most five operation occurrences by a finite countermodel
  certificate.

### Foundations and computability

[`SetTheory/`](SetTheory/README.md) proves that the following alternative
axiomatization is deductively equivalent to ordinary ZF:

- retain Extensionality, Regularity, Separation, and Powerset;
- replace Pairing, Union, Infinity, and Replacement with a single Closure
  schema asserting set-sized transitive closures for set-like relations.

The result is checked in a canonical Rocq development and in an independent,
mathlib-free Lean 4 port under [`SetTheory/lean/`](SetTheory/lean/README.md).
The development includes its own first-order syntax, proof calculus,
soundness, Gödel completeness, model theory, and both directions of the
axiom trade. The mathematical exposition is available as
[`closure-axiomatization.pdf`](SetTheory/article/closure-axiomatization.pdf)
with [LaTeX source](SetTheory/article/closure-axiomatization.tex).

The same project contains adjacent foundational and computability work:

- Ackermann-coded hereditary finite sets and PA/HF interpretation
  infrastructure;
- a first-order PA sentence expressing the Mertens/Littlewood arithmetic
  criterion associated with the Riemann Hypothesis—the repository formalizes
  the statement, not a proof of RH or yet its analytic equivalence;
- Busy Beaver champion witnesses and eventual-domination theorems;
- an exhaustive Lean classification of all `12^4 = 20,736` two-state tables,
  proving the marked-symbol score `Σ(2) = 4`;
- a bridge to the vendored Rocq proof that the maximum halting time for the
  corresponding two-state model is `BB(2) = 6`;
- an [independent Lean proof](SetTheory/lean/SetTheory/BusyBeaverBB3.lean) of
  `Σ(3) = 6`, using a kernel-checked lazy partial-table search whose active
  leaves carry declaratively verified n-gram CPS nonhalting certificates;
- a [separate Rocq proof](SetTheory/BusyBeaverBB3Bridge.v) of `Σ(3) = 6`,
  combining its kernel-checked lazy score search with the vendored
  `BB(3) = 21` time certificate;
- a [Rocq bridge](SetTheory/BusyBeaverBB4Bridge.v) from the vendored
  `BB(4) = 107` certificate to the local machine model, proving the exact
  local time statement `ExactBusyBeaverTime 4 107`;
- a separate score-aware Rocq replay of the four-state TNF enumeration in
  [`BusyBeaverBB4Score.v`](SetTheory/BusyBeaverBB4Score.v) and its companion
  modules, bounding the tape immediately before the final action by twelve
  marks and the executed final write by one more, proving `Σ(4) = 13`;
- a sound, mathlib-free Lean four-state TNF reduction with state-renaming and
  reflection proofs; its exact upper bound remains conditional on the still
  unsharded equality `TNF.checkRoot BB4.leaf = true`.

The score theorems `Σ(2) = 4`, `Σ(3) = 6`, `Σ(4) = 13` and time theorems
`BB(2) = 6`, `BB(3) = 21`, `BB(4) = 107` use different Busy Beaver measures;
the differing numbers are intentional. The four-state score theorem is a
separate certificate, not a consequence of the 107-step time theorem.

### Rocq/Coq coverage

[`CoqProofs/`](CoqProofs/README.md) contains idiomatic Rocq ports of the root
Lean modules. Some ports reproduce the full mathematical statement; others
check the finite certificate surface while an analytic or semantic bridge
remains Lean-only. The directory README records those boundaries module by
module rather than claiming blanket parity.

[`CoqBB2/`](CoqBB2/README.md) is a vendored copy of the upstream `BB2/` proof
from `ccz181078/Coq-BB5`. The local version replaces an upstream unchecked
native-cache cast with a kernel-checked `vm_compute`/`reflexivity` proof and
retains the upstream provenance and license.

[`CoqBB3/`](CoqBB3/README.md) similarly vendors the upstream `BB3/` proof of
the 21-step bound and applies the same hardening. The local
[`BusyBeaverBB3Bridge.v`](SetTheory/BusyBeaverBB3Bridge.v) transports that time
bound into the repository's Rado model and combines it with a proved lazy
partial-table score checker to obtain the exact score `Σ(3) = 6`.

[`CoqBB4/`](CoqBB4/README.md) vendors the modular upstream `BB4/` proof of the
107-step bound and replaces its unchecked native-cache cast by the same
kernel-checked `vm_compute`/`reflexivity` path. The local
[`BusyBeaverBB4Bridge.v`](SetTheory/BusyBeaverBB4Bridge.v) proves that its
undefined-transition convention corresponds to the final-action convention
of the local model, checks that the standard four-state champion attains 107
local steps, and exports `ExactBusyBeaverTime 4 107`.

The distinct [`BusyBeaverBB4Score.v`](SetTheory/BusyBeaverBB4Score.v) checker
augments the same TNF queue with a proved score invariant. Its cached q200
computation shows that every undefined-transition halt has at most twelve
marks; [`BusyBeaverBB4ScoreBridge.v`](SetTheory/BusyBeaverBB4ScoreBridge.v)
proves exact synchronization with the local list tape and accounts for the
executed final write, exporting `sigma_four_eq_thirteen`.

## Research artifacts

Proof discovery is part of the repository when it is needed to reproduce or
audit a certificate:

- [`Oeis/A158415/computations/wolfram/generate-a158415-data.wl`](Oeis/A158415/computations/wolfram/generate-a158415-data.wl)
  generates and audits the exact radical tables and Lean certificate
  fragments for A158415.
- [`Oeis/A198683/`](Oeis/A198683/README.md) preserves source snapshots,
  Python and Wolfram computations, generated tables, discrepancy analyses,
  and five waves of formalization reports.
- [`docs/reports/riemann-hypothesis-pa-statement-2026-07-09.md`](docs/reports/riemann-hypothesis-pa-statement-2026-07-09.md)
  compares the formal PA statement with the intended analytic criterion.

Generated tables and scripts remain outside the trusted theorem boundary
unless a proof-assistant checker connects them to the mathematical semantics.

## Building and checking

### Lean/mathlib workspace

The root workspace is pinned by [`lean-toolchain`](lean-toolchain) and
[`lake-manifest.json`](lake-manifest.json). With Git and
[elan](https://github.com/leanprover/elan) installed:

```powershell
git clone https://github.com/VladimirReshetnikov/Proofs.git
cd Proofs
lake exe cache get
lake build
```

The broad build includes large exact certificates and can be expensive. For
focused work, build the affected module and its dependencies:

```powershell
lake build +LeanProofs.FermatFour
lake build +LeanProofs.A198683EightBounds
lake build +SetTheory.BusyBeaverBB2
lake build +SetTheory.BusyBeaverBB3
lake build +SetTheory.BusyBeaverMathlib
lake build +SetTheory.AuditMathlib
```

The Closure ↔ ZF Lean port also has a standalone, mathlib-free workspace:

```powershell
cd SetTheory/lean
lake build
lake env lean SetTheory/Audit.lean
```

### Rocq/Coq developments

The root [`_CoqProject`](_CoqProject) lists the `CoqProofs` modules in
dependency order. On PowerShell, compile them with:

```powershell
cd C:\path\to\Proofs
Get-Content _CoqProject |
  Where-Object { $_ -match '^CoqProofs/.+\.v$' } |
  ForEach-Object {
    & coqc -Q CoqProofs LeanProofsCoq $_
    if ($LASTEXITCODE -ne 0) { throw "coqc failed: $_" }
  }
```

The SetTheory manifest includes its vendored CoqBB2, CoqBB3, and CoqBB4
dependencies in the required order:

```powershell
cd C:\path\to\Proofs\SetTheory
Get-Content _CoqProject |
  Where-Object { $_ -match '\.v$' } |
  ForEach-Object {
    & coqc -Q . SetTheory -Q ../CoqBB2 CoqBB2 -Q ../CoqBB3 CoqBB3 `
        -Q ../CoqBB4 CoqBB4 $_
    if ($LASTEXITCODE -ne 0) { throw "coqc failed: $_" }
  }
```

For individual files, use the same logical-path flags. See
[`CoqProofs/README.md`](CoqProofs/README.md),
[`SetTheory/README.md`](SetTheory/README.md),
[`CoqBB2/README.md`](CoqBB2/README.md),
[`CoqBB3/README.md`](CoqBB3/README.md), and
[`CoqBB4/README.md`](CoqBB4/README.md) for project-specific details.

## Trust and status

- Lean theorem statements are checked by Lean's kernel. Some finite
  certificates use `native_decide`; those sites deliberately extend the
  trusted boundary to Lean's native compiler and runtime and are visible in
  source. The exhaustive `Σ(2)=4` and `Σ(3)=6` Busy Beaver shards use ordinary
  kernel `decide`, not `native_decide`.
- Rocq certificates use kernel checking and, where documented, `vm_compute`.
  The vendored CoqBB2, CoqBB3, and CoqBB4 proofs use functional
  extensionality; their READMEs record the exact assumption. Their locally
  hardened enumeration cache equations do not use `native_cast_no_check`.
  The four-state score equality uses `vm_cast_no_check`: despite its historical
  name, the [Rocq 9.0 manual](https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/tactics.html#performance-oriented-tactic-variants)
  specifies that it skips only the tactic-side precheck and asks the kernel to
  perform VM conversion at `Qed`. The equality is closed under the global
  context and does not use native OCaml compilation.
- Generated equational traces, interval tables, and candidate partitions are
  accepted only through proved checkers or explicit hypotheses. Numerical
  agreement alone is never presented as a theorem.
- Conditional theorems remain useful: their hypotheses identify the exact
  mathematical or certificate obligations still open. They are labeled as
  conditional in module documentation and status reports.
- Assumption audits live in [`SetTheory/Audit.v`](SetTheory/Audit.v),
  [`SetTheory/lean/SetTheory/Audit.lean`](SetTheory/lean/SetTheory/Audit.lean),
  and
  [`SetTheory/lean/SetTheory/AuditMathlib.lean`](SetTheory/lean/SetTheory/AuditMathlib.lean).

## Provenance

This repository was extracted from
[`VladimirReshetnikov/Smithereens`](https://github.com/VladimirReshetnikov/Smithereens)
on 2026-07-09 from source snapshot
[`6955227fc5bf55d368b4c40644767b3749234425`](https://github.com/VladimirReshetnikov/Smithereens/commit/6955227fc5bf55d368b4c40644767b3749234425).
The filtered history lifts the former proof-owned paths to the repository root
while retaining their relevant ancestry, authorship, timestamps, messages,
and contents; commit identifiers necessarily changed during filtering. The
filtered repository's ordinary `git log` and `git blame` expose that rewritten
history; consult Smithereens for the original path names.

BusyLean was intentionally excluded from this repository and remains in
[Smithereens at `src/BusyLean`](https://github.com/VladimirReshetnikov/Smithereens/tree/main/src/BusyLean).

The vendored [`CoqBB2/`](CoqBB2/), [`CoqBB3/`](CoqBB3/), and
[`CoqBB4/`](CoqBB4/) source snapshots come from
[`ccz181078/Coq-BB5` commit `9142e219...`](https://github.com/ccz181078/Coq-BB5/commit/9142e219229baf2245d3f70851947230ea28a318).
Their directory READMEs identify the selected upstream proof and each
repository-local kernel-hardening change.

## License

Unless a nested license says otherwise, this repository is available under
the [MIT No Attribution License (MIT-0)](LICENSE). The vendored
[`CoqBB2/`](CoqBB2/), [`CoqBB3/`](CoqBB3/), and [`CoqBB4/`](CoqBB4/)
subtrees retain their upstream MIT licenses ([BB2](CoqBB2/LICENSE),
[BB3](CoqBB3/LICENSE), [BB4](CoqBB4/LICENSE)) and provenance.
