# SetTheory — Lean 4 port

- Created (UTC): 2026-07-02T02:12:50Z
- Repository HEAD: 50a14cc6ba5c0dfca20cafd0a24df7b224a5e817

A complete Lean 4 port of the core Rocq/Coq Closure/ZF development in [`../`](../) —
Vladimir Reshetnikov's **"Closure" axiomatization of set theory and its
machine-checked equivalence with ZF**, up to and including the headline
syntactic theorem

```lean
theorem T_iff_ZF (phi : Form) (hphi : Sentence phi) :
    BProv Tax_s [] phi ↔ BProv ZFax_s [] phi
```

— *T and ZF prove exactly the same sentences* — plus the Gödel-completeness
library it stands on. The core statements have Lean counterparts with the same
logical content; parity and deliberate side-module differences are recorded in
the table below. There is no `sorry` and no project-specific Lean axiom.

## Module map

| Lean module | Coq file | contents |
| --- | --- | --- |
| [`SetTheory/Fol.lean`](SetTheory/Fol.lean) | `Fol.v` | formulas over {∈, =} with De Bruijn variables, renaming, free variables, sentences, sealing, a surjective enumeration (self-contained Cantor pairing), Tarski satisfaction `Sat`, `relOf` |
| [`SetTheory/Calculus.lean`](SetTheory/Calculus.lean) | `Calculus.v` | the ND calculus `Prov`, weakening/deduction/cut, the equality kit, renaming admissibility, Henkin-witness cores, **soundness** |
| [`SetTheory/Completeness.lean`](SetTheory/Completeness.lean) | `Completeness.v` | the quotient term model + truth lemma (`model_exists`), the sentence-base Lindenbaum/Henkin chain (`model_of_BCon`; finite-context completeness is its `B = ∅` instance), **Gödel completeness** (`prov_iff_valid`), infinite completeness (`completeness_inf`), **`theory_equiv`** |
| [`SetTheory/Zf.lean`](SetTheory/Zf.lean) | `Zf.v` | the ZF axioms as formulas, `ZFax_s`, extraction bridges, and the internal mathematics of a FO model of {Ext, Sep, Pair, Union, Inf, Repl}: Kuratowski pairs, internal ω with `omega_ind`, the formula-macro library, the finite recursion theorem, **`ClosureFO_of_ZF`** |
| [`SetTheory/Equivalence.lean`](SetTheory/Equivalence.lean) | `Equivalence.v` | the deep forward trade, `Closure_form` + bridges, `Tax_s`, `Tmodel_sat_ZF` / `ZFmodel_sat_T`, `ZF_implies_T`, `T_implies_ZF`, **`T_iff_ZF`** |
| [`SetTheory/Forward.lean`](SetTheory/Forward.lean) | `Forward.v` | the shallow (second-order) forward trade, self-contained, dependency-audited |
| [`SetTheory/Reverse.lean`](SetTheory/Reverse.lean) | `Reverse.v` | the shallow reverse direction (ZF ⊢ Closure), self-contained, Foundation-free numerals |
| [`SetTheory/PAHF.lean`](SetTheory/PAHF.lean) — a facade over [`SetTheory/PAHF/`](SetTheory/PAHF/)`{PASyntax, AckermannHFCore, RiemannHypothesis, Interpretation}.lean` | `PAHF.v` | PA/HF formalization work: Ackermann-coded HF on `Nat`, finite von Neumann ordinals, shallow PA/HF round-trip isomorphisms, first-order HF axiom schemas in the one-relation language, a separate first-order PA syntax with sealed PA axiom semantics, and a PA sentence form of the Mertens/Littlewood RH criterion |
| [`SetTheory/BusyBeaver.lean`](SetTheory/BusyBeaver.lean) | `BusyBeaver.v` | Rado-style two-symbol blank-tape machines, attainable halting scores, the maximum-property interface `IsSigma`, and the theorem that any such busy-beaver score function eventually dominates every total recursive function whose recursiveness predicate has the standard linear-overhead blank-tape compiler |
| [`SetTheory/BusyBeaverKnownValues.lean`](SetTheory/BusyBeaverKnownValues.lean) | `BusyBeaverKnownValues.v` | standard 1-, 2-, 3-, and 4-state busy-beaver score champion tables, checked halting-score witnesses for `1, 4, 6, 13`, a direct proof that `Σ(1)=1`, and a certificate interface proving the exact A028444 prefix from the remaining explicit upper-bound proofs; the Rocq file additionally hosts its local bounded three-state score checker |
| [`SetTheory/BusyBeaverBB2.lean`](SetTheory/BusyBeaverBB2.lean) | `BusyBeaverBB2Bridge.v` + vendored CoqBB2 | an independent Lean proof of `Σ(2)=4`, using kernel-checked halting/nonhalting certificates for the left-moving half of the 20,736 tables and a proved reflection simulation for the right-moving half |
| [`SetTheory/BusyBeaverBB3.lean`](SetTheory/BusyBeaverBB3.lean) — a facade over [`SetTheory/BusyBeaverBB3/`](SetTheory/BusyBeaverBB3/) | `BusyBeaverBB3Bridge.v` + vendored CoqBB3 | independent Lean proof of `Σ(3)=6` by a sound lazy partial-table search and declaratively checked n-gram CPS nonhalting certificates; the separate Rocq proof combines its lazy score checker with the certified 21-step time bound |
| [`SetTheory/BusyBeaverBB4/`](SetTheory/BusyBeaverBB4/) | `BusyBeaverBB4Bridge.v`, `BusyBeaverBB4Score*.v` + vendored CoqBB4 | Lean proves a sound partial-table search, nonhalting leaves, and arbitrary-machine TNF/state-renaming/reflection reductions, with exact coverage still conditional; Rocq proves both `ExactBusyBeaverTime 4 107` and the exact score `Σ(4)=13` |
| [`SetTheory/BusyBeaverMathlib.lean`](SetTheory/BusyBeaverMathlib.lean) | `BusyBeaverMathlib.v` (explicit assumption-record counterpart) | mathlib's `Computable` predicate as the total-recursive predicate for `Nat -> Nat`, sequential `ToPartrec.Code` extraction, the proved finite-support `PartrecToTM2` evaluator bridge, and the unconditional busy-beaver domination theorem for `Computable` functions |
| [`SetTheory/Audit.lean`](SetTheory/Audit.lean) | `Audit.v` | type-checks the headline results and prints their axioms |
| [`SetTheory/AuditMathlib.lean`](SetTheory/AuditMathlib.lean) | — (root workspace only) | assumption audit for the explicit Busy Beaver certificate targets and mathlib-backed bridge theorems |

## Building

Lean 4.31.0 via elan/lake; **no external dependencies** (no Mathlib, no
Batteries — Lean core only) for the standalone SetTheory workspace:

```sh
cd SetTheory/lean
lake build                            # builds every mathlib-free module
lake env lean SetTheory/Audit.lean    # re-runs the assumption audit
lake build +SetTheory.BusyBeaverBB4.TNFAudit
```

The expensive Busy Beaver certificate modules
`SetTheory/BusyBeaverBB2.lean` and `SetTheory/BusyBeaverBB3.lean`, the
mathlib-backed `SetTheory/BusyBeaverMathlib.lean` bridge, and their combined
`SetTheory/AuditMathlib.lean` audit are built explicitly from the
repository-root workspace, which is pinned to mathlib `v4.31.0`:

```sh
cd "$(git rev-parse --show-toplevel)"
lake exe cache get Mathlib.Computability.TuringMachine.ToPartrec
lake build +SetTheory.BusyBeaverBB2
lake build +SetTheory.BusyBeaverBB3
lake build +SetTheory.BusyBeaverMathlib
lake build +SetTheory.AuditMathlib    # replays the bridge assumption audit
```

## The assumption audit

`SetTheory/Audit.lean` is the Lean analogue of the Coq files' trailing
`Print Assumptions` commands. Its output certifies:

```text
'SetTheory.T_iff_ZF' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— only Lean's three standard axioms, which together provide exactly the
classical-mathematics package the Coq development drew from
`ClassicalEpsilon` + `FunctionalExtensionality` + `PropExtensionality` +
`ProofIrrelevance` (in Lean, functional extensionality is a theorem of
`Quot.sound`, and proof irrelevance is definitional). No `axiom`
declarations, no `sorry` anywhere in the port.

The **free dependency audit** of the Coq development survives — in a
stronger, statement-level form. Where Coq's `Section` mechanism made the
audit visible only in the post-hoc `Check` output, the Lean port names each
axiom schema as a `def` (`ExtAx`, `SepAx`, `HostAx`, `ClosureAx`, …) and
each theorem takes **exactly the hypotheses it uses** as explicit
parameters. So the signatures themselves certify, e.g.:

- `Forward.Union (hSep) (hClo)` — Union needs only Separation + Closure;
- `Forward.Replacement (hSep) (hHost) (hClo)` — no Powerset, no Extensionality;
- `Forward.Pairing (witness) (hSep) (hHost) (hClo)` — plus a nonempty domain,
  and not even Extensionality;
- `Forward.Infinity (witness) (hExt) (hSep) (hHost) (hClo)`;
- `Reverse.Closure_holds (witness) (hExt) (hSep) (hPair) (hUnion) (hInf) (hRepl)`
  — **neither Powerset nor Regularity**, i.e. *ZF − Powerset − Regularity ⊢
  Closure*;
- `ZFAxioms` (the model-side bundle behind `ClosureFO_of_ZF`) contains
  exactly {Ext, Sep, Pair, Union, Inf, Repl} — the deep reverse likewise
  needs neither Powerset nor Regularity.

The PA/HF work in `PAHF.lean` is also included in the audit. Its current
checked surface is deliberately explicit:

```lean
theorem AckermannHF.PA_biinterpretable_with_HF_standard :
    Nonempty (PA.Iso PA.natModel AckermannHF.ordinalPAModel) ∧
      Nonempty (AckermannHF.AdjunctionIso
        AckermannHF.standardModel AckermannHF.ordinalHFModel)

theorem AckermannHF.sat_HF_model
    (M : AckermannHF.AdjunctionModel α) (v : Nat → α) :
    ∀ g, AckermannHF.HFAx_s g → Sat M.mem v g

theorem PA.Formula.sat_axiom_s
    (M : PA.Model α) (e : Nat → α) :
    ∀ f, PA.Formula.Ax_s f → PA.Formula.Sat M e f
```

The PA syntax layer also contains
[`SetTheory/PAHF/RiemannHypothesis.lean`](SetTheory/PAHF/RiemannHypothesis.lean),
which defines `PA.Formula.RiemannHypothesis.mertensRiemannHypothesisSentence`:
the sealed first-order PA sentence corresponding to the Mertens/Littlewood
growth criterion `forall q > 0, exists C, forall n,
|M(n)|^(2*q) <= C*n^(q+1)`.  The companion report
[`../../docs/reports/riemann-hypothesis-pa-statement-2026-07-09.md`](../../docs/reports/riemann-hypothesis-pa-statement-2026-07-09.md)
explains why this was chosen over the Lagarias/Robin/Farey alternatives.

This is a semantic and syntax-preparation checkpoint, not yet the final
deductive bi-interpretability theorem. The remaining syntactic bridge is the
interpretation layer itself: PA terms/formulas must be translated to
membership-language formulas over the finite ordinals, and HF membership must
be translated back to PA by a definable bit predicate rather than by treating
`Nat.testBit` as primitive.

`BusyBeaver.lean` adds a small, independent computability-theory interface.  It
does not attempt to formalize a universal-machine compiler inside this file;
instead it names the exact compiler property needed for the classical argument:

```lean
theorem BusyBeaver.eventuallyDominates_of_hasLinearOverheadBlankCompiler
    {Sigma : Nat -> Nat} (hSigma : BusyBeaver.IsSigma Sigma)
    {TotalRecursive : (Nat -> Nat) -> Prop}
    (hCompiler : BusyBeaver.HasLinearOverheadBlankCompiler TotalRecursive)
    {f : Nat -> Nat} (hf : TotalRecursive f) :
    BusyBeaver.EventuallyDominates Sigma f
```

The same theorem is also exported under the request-shaped name
`BusyBeaver.sigma_eventually_dominates_every_total_recursive`.  The companion
theorem `BusyBeaver.eventuallyDominates_totalRecursiveInRadoModel` and its alias
`BusyBeaver.sigma_eventually_dominates_every_totalRecursiveInRadoModel` package
the same result for the model-relative predicate
`BusyBeaver.TotalRecursiveInRadoModel`.  `SetTheory/Audit.lean` checks and
prints the axioms of the request-shaped aliases.

The same module also proves the state-padding facts needed for later compiler
accounting: `BusyBeaver.sigma_mono_of_pos` pads positive-state machines with
unreachable states, and `BusyBeaver.score_le_sigma_of_atMost` lets any score
attainable with at most `n` states be compared directly with `Σ(n)`.
Using those lemmas, it also exposes
`BusyBeaver.eventuallyDominates_of_hasEventuallyAtMostBlankCompiler`, a version
of the domination theorem whose compiler target is simply: for all sufficiently
large `n`, produce a blank-tape machine using at most `n` states and scoring
`f n`.

`BusyBeaverMathlib.lean` connects that interface to mathlib's recursion theory
without introducing an unproved recursive-function/Turing-machine bridge:

```lean
theorem BusyBeaver.totalRecursiveMathlib_eval_by_supported_tm2
    {f : Nat -> Nat} :
    BusyBeaver.TotalRecursiveMathlib f ->
      ∃ c : Turing.ToPartrec.Code,
        (∀ n,
          StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
            (Turing.PartrecToTM2.init c [n]) =
              Part.some (Turing.PartrecToTM2.halt [f n])) ∧
        Turing.TM2.Supports Turing.PartrecToTM2.tr
          (Turing.PartrecToTM2.codeSupp c Turing.PartrecToTM2.Cont'.halt)
```

The companion theorem `BusyBeaver.totalRecursiveMathlib_tm2_eval_main`
packages the same computation in mathlib's ordinary `TM2.eval` interface:
the evaluator started with `trList [n]` on the main stack halts with
`trList [f n]` there.  For the score-counting direction, the bridge proves
a unary-output variant: `BusyBeaver.totalRecursiveMathlib_bool_tm0_eval_unary`
threads a composed `ToPartrec.Code` through `TM2 -> TM1`, `TM1 -> TM1 Bool`,
and `TM1 -> TM0` so that the decoded main stack contains
`trList (List.replicate (f n) 0)`, a list with exactly `f n` zero entries,
and the support-preserving lowering
`BusyBeaver.partrecToTM2_descends_to_supported_bool_tm0_with_encoding`
carries the finite-support `PartrecToTM2` evaluator through mathlib's proved
reductions to a finite-support Bool `TM0` machine.  The chain then closes
**unconditionally**: the supported Bool `TM0` machine is wrapped by a local
blank-tape initializer (`InitThenTM0State`), its state count is budgeted
against the binary size of the input
(`linear_mul_le_two_pow_pred_of_large`, `nat_size_linear_le_self_of_large`,
`init_wrapper_state_count_le_linear`,
`init_wrapper_state_count_le_linear_size`), and the file proves

```lean
theorem BusyBeaver.totalRecursiveMathlib_hasEventuallyAtMostLowerBoundCompiler :
    HasEventuallyAtMostLowerBoundCompiler TotalRecursiveMathlib

theorem BusyBeaver.sigma_eventually_dominates_every_totalRecursiveMathlib
    {Sigma : Nat -> Nat} (hSigma : IsSigma Sigma)
    {f : Nat -> Nat} (hf : TotalRecursiveMathlib f) :
    EventuallyDominates Sigma f
```

— any busy-beaver score function eventually dominates every function
accepted by mathlib's `Computable` predicate.
[`SetTheory/AuditMathlib.lean`](SetTheory/AuditMathlib.lean) replays the
`#print axioms` audit for both theorems from the root workspace: only
`propext`, `Classical.choice`, and `Quot.sound`.

`BusyBeaverBB2.lean` proves the exact second score value without importing the
Coq theorem. It enumerates the 12 possible actions in each table entry,
kernel-checks the `6 * 12^3 = 10,368` tables whose first move is left, and
covers the right-moving half by a proved tape-reflection simulation. Thus all
`12^4 = 20,736` machines are covered. A table that has halted by step six is
checked to have at most four marked cells. Every other table must carry a sound
nonhalting certificate: an exact or translated loop, a one-way blank escape, a
closed three-cell local abstraction, or one of seven proved frontier-growth
invariants (plus their reflected forms). In particular, a machine that prints
an unbounded trail is handled by a blank-escape or frontier invariant, not by
an invalid repeated-configuration assumption. The expensive Boolean checks
are split into 144-table modules under `SetTheory/BusyBeaverBB2/` and proved by
kernel `decide`; the proof does not use `native_decide`. The exported results
are:

```lean
theorem BusyBeaver.BB2.upperBound_two :
    BusyBeaver.AttainableScore 2 score -> score <= 4

theorem BusyBeaver.BB2.sigma_two_eq_four
    (hSigma : BusyBeaver.IsSigma Sigma) : Sigma 2 = 4
```

`BusyBeaverBB3.lean` independently proves the exact three-state value. Its lazy
partial table stores only continuing transitions. Whenever execution first
reaches an unassigned entry, the search checks both possible final writes and
recurses through all twelve continuing actions; after 21 transitions, every
still-active branch must supply a sound nonhalting certificate. The leaf
pipeline first recognizes a table with all six continuing entries assigned,
then tries Boolean n-gram CPS certificates of widths one, two, and three, and
finally width two over symbols carrying a depth-two per-cell write history.

The fixed-point builder is only a certificate generator: its output is accepted
solely after the proved declarative `NGramCPS.Valid` checker has rechecked every
seed, length, transition, and closure obligation. The exhaustive computation is
split first by the twelve possible initial continuing actions under
`SetTheory/BusyBeaverBB3/Certificates/`, then subdivided further at later
freshly encountered table entries as needed. Every computational shard is
proved with ordinary kernel `decide`; none uses `native_decide`. The public
results are:

```lean
theorem BusyBeaver.BB3.upperBound_three :
    BusyBeaver.AttainableScore 3 score -> score <= 6

theorem BusyBeaver.BB3.sigma_three_eq_six
    (hSigma : BusyBeaver.IsSigma Sigma) : Sigma 3 = 6
```

This Lean proof does not import the Coq development. Independently,
`BusyBeaverBB3Bridge.v` imports the vendored Rocq `BB(3)=21` certificate and
combines it with the Rocq lazy score checker to prove the same `Sigma 3 = 6`
statement through a different upper-bound route.

For four states, Lean now proves the semantic search and symmetry layer under
`BusyBeaverBB4/`. `TNF.checkFrom_sound` applies a whole-machine state
permutation whenever execution first reaches a noncanonical fresh state;
`TNF.upperBound_of_checkRoot` additionally proves first-transition target
canonicalization and left/right tape reflection. These are arbitrary-machine
theorems, not assumptions that the input was already normalized, and their
axiom footprint is only `propext` and `Quot.sound`.

The strongest Lean result is deliberately still conditional:

```lean
theorem BusyBeaver.BB4.TNF.upperBound_of_checkRoot
    (hLeaf : LeafSound leaf) (hCheck : checkRoot leaf = true) :
    AttainableScore 4 score -> score <= 13
```

The remaining obligation is the kernel-checked exhaustive equality
`TNF.checkRoot BB4.leaf = true`; direct evaluation is too large and needs the
same kind of sharding used for the three-state proof. A 100,000-node coverage
probe reached 1,053 leaves, all accepted by the existing sound leaf pipeline;
a separate million-node structural probe reached 10,691 leaves and no unsafe
halt. These bounded probes are evidence about the search shape rather than the
missing exhaustive theorem.

Independently, Rocq imports the vendored `BB(4)=107` certificate through
`BusyBeaverBB4Bridge.v`, proving `ExactBusyBeaverTime 4 107` in the local
model. The `BusyBeaverBB4Score*.v` chain propagates a score invariant through
the TNF enumeration, bounds the tape before the undefined transition by twelve
marks, and proves that the local final action adds at most one, yielding the
unconditional exact score theorem `Σ(4)=13`.

## Translation notes (Coq → Lean)

Statements are 1:1; proofs are re-idiomatized. The deliberate deviations,
all mechanical:

- **`seal` → `sealF`.** `seal` is a reserved keyword in Lean 4.
- **`omega` → `omegaV`.** The internal ω is renamed to avoid the `omega`
  tactic.
- **Cantor pairing is self-contained.** Coq used `Stdlib.Cantor`; the port
  builds the pairing in `SetTheory/Fol.lean` from recursively-defined
  triangular numbers (`tri`), avoiding division arithmetic entirely.
- **De Bruijn offset convention.** Where the Coq file writes an offset
  lookup `off + k`, the port writes `k + off` (and `S i` becomes `i + 1`):
  Lean's `Nat.add` recurses on its *second* argument, so this keeps the
  environment lookups reducing definitionally, exactly as Coq's `plus`
  (which recurses on the first) did there.
- **Hypothesis packaging.** Coq `Section` hypotheses become either explicit
  named parameters (`Forward`, `Reverse`, the DeepForward section of
  `Equivalence` — preserving the dependency audit) or `Prop`-valued
  structure bundles where the Coq development always used the whole set:
  `MCHT` (the five maximal-consistent-Henkin-theory properties in
  `Completeness`) and `ZFAxioms` (the six model-side ZF axioms in `Zf`).
- **Classical description.** `constructive_indefinite_description` ↦
  `Exists.choose`/`Exists.choose_spec`; `epsilon` (with an inhabited
  default, used for the canonical `ceq`-representatives) is defined locally
  in `Completeness.lean`; `excluded_middle_informative` ↦ a classical
  `if … then … else`.
- **The quotient term model** uses `Subtype` (`D T = {n : Nat // rep T n = n}`)
  with `Subtype.ext` where Coq needed `proof_irrelevance`.
- **`Local Opaque` macros** need no counterpart: Lean's `simp only [Sat]`
  reduces satisfaction through connectives while leaving the formula-macro
  `def`s (`fEmptyF`, `fKPairF`, `fApproxF`, …) folded, which is exactly the
  discipline the Coq proofs enforced by hand.

## Relation to the Coq development

The Coq sources in [`../`](../) remain the canonical development; this port
is a faithful second machine-checking of the same mathematics in an
independent proof assistant (different kernel, different axiom base,
different standard library). The article
[`../article/closure-axiomatization.tex`](../article/closure-axiomatization.tex)
describes the mathematics and the Coq formalization; everything it says
about the structure of the proofs applies verbatim to the Lean port via the
module map above.
