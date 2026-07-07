# SetTheory — Lean 4 port

- Created (UTC): 2026-07-02T02:12:50Z
- Repository HEAD: 50a14cc6ba5c0dfca20cafd0a24df7b224a5e817

A complete Lean 4 port of the Rocq/Coq development in [`../`](../) —
Vladimir Reshetnikov's **"Closure" axiomatization of set theory and its
machine-checked equivalence with ZF**, up to and including the headline
syntactic theorem

```lean
theorem T_iff_ZF (phi : Form) (hphi : Sentence phi) :
    BProv Tax_s [] phi ↔ BProv ZFax_s [] phi
```

— *T and ZF prove exactly the same sentences* — plus the Gödel-completeness
library it stands on. Every Coq statement has a Lean counterpart with the
same logical content; no `sorry`, no extra axioms.

## Module map

| Lean module | Coq file | contents |
|---|---|---|
| [`SetTheory/Fol.lean`](SetTheory/Fol.lean) | `Fol.v` | formulas over {∈, =} with De Bruijn variables, renaming, free variables, sentences, sealing, a surjective enumeration (self-contained Cantor pairing), Tarski satisfaction `Sat`, `relOf` |
| [`SetTheory/Calculus.lean`](SetTheory/Calculus.lean) | `Calculus.v` | the ND calculus `Prov`, weakening/deduction/cut, the equality kit, renaming admissibility, Henkin-witness cores, **soundness** |
| [`SetTheory/Completeness.lean`](SetTheory/Completeness.lean) | `Completeness.v` | the quotient term model + truth lemma (`model_exists`), the sentence-base Lindenbaum/Henkin chain (`model_of_BCon`; finite-context completeness is its `B = ∅` instance), **Gödel completeness** (`prov_iff_valid`), infinite completeness (`completeness_inf`), **`theory_equiv`** |
| [`SetTheory/Zf.lean`](SetTheory/Zf.lean) | `Zf.v` | the ZF axioms as formulas, `ZFax_s`, extraction bridges, and the internal mathematics of a FO model of {Ext, Sep, Pair, Union, Inf, Repl}: Kuratowski pairs, internal ω with `omega_ind`, the formula-macro library, the finite recursion theorem, **`ClosureFO_of_ZF`** |
| [`SetTheory/Equivalence.lean`](SetTheory/Equivalence.lean) | `Equivalence.v` | the deep forward trade, `Closure_form` + bridges, `Tax_s`, `Tmodel_sat_ZF` / `ZFmodel_sat_T`, `ZF_implies_T`, `T_implies_ZF`, **`T_iff_ZF`** |
| [`SetTheory/Forward.lean`](SetTheory/Forward.lean) | `Forward.v` | the shallow (second-order) forward trade, self-contained, dependency-audited |
| [`SetTheory/Reverse.lean`](SetTheory/Reverse.lean) | `Reverse.v` | the shallow reverse direction (ZF ⊢ Closure), self-contained, Foundation-free numerals |
| [`SetTheory/PAHF.lean`](SetTheory/PAHF.lean) | new Lean-first module | PA/HF formalization work: Ackermann-coded HF on `Nat`, finite von Neumann ordinals, shallow PA/HF round-trip isomorphisms, first-order HF axiom schemas in the one-relation language, and a separate first-order PA syntax with sealed PA axiom semantics |
| [`SetTheory/BusyBeaver.lean`](SetTheory/BusyBeaver.lean) | new Lean-first module | Rado-style two-symbol blank-tape machines, attainable halting scores, the maximum-property interface `IsSigma`, and the theorem that any such busy-beaver score function eventually dominates every total recursive function whose recursiveness predicate has the standard linear-overhead blank-tape compiler |
| [`SetTheory/BusyBeaverMathlib.lean`](SetTheory/BusyBeaverMathlib.lean) | mathlib-backed bridge module | mathlib's `Computable` predicate as the total-recursive predicate for `Nat -> Nat`, sequential `ToPartrec.Code` extraction, and the proved finite-support `PartrecToTM2` evaluator bridge |
| [`SetTheory/Audit.lean`](SetTheory/Audit.lean) | trailing `Check` / `Print Assumptions` commands | type-checks the headline results and prints their axioms |

## Building

Lean 4.31.0 via elan/lake; **no external dependencies** (no Mathlib, no
Batteries — Lean core only) for the standalone SetTheory workspace:

```sh
cd src/Lean/SetTheory/lean
lake build                            # builds all seven modules
lake env lean SetTheory/Audit.lean    # re-runs the assumption audit
```

The mathlib-backed bridge `SetTheory/BusyBeaverMathlib.lean` is built from the
root `src/Lean` workspace, which is pinned to mathlib `v4.31.0`:

```sh
cd src/Lean
lake exe cache get Mathlib.Computability.TuringMachine.ToPartrec
lake build +SetTheory.BusyBeaverMathlib
```

## The assumption audit

`SetTheory/Audit.lean` is the Lean analogue of the Coq files' trailing
`Print Assumptions` commands. Its output certifies:

```
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
`trList [f n]` there.  For the score-counting direction, the bridge also proves
a unary-output variant: `BusyBeaver.totalRecursiveMathlib_bool_tm0_eval_unary`
threads a composed `ToPartrec.Code` through `TM2 -> TM1`, `TM1 -> TM1 Bool`,
and `TM1 -> TM0` so that the decoded main stack contains
`trList (List.replicate (f n) 0)`, a list with exactly `f n` zero entries.
It also proves the support-only lowering
`BusyBeaver.partrecToTM2_descends_to_supported_bool_tm0`: the finite-support
`PartrecToTM2` evaluator descends through mathlib's proved reductions to a
finite-support Bool `TM0` machine.  The remaining bridge for the full
busy-beaver theorem is the exact output/tape normalization from that Bool
`TM0` computation into a blank-tape two-symbol Rado machine, including the
state-count accounting needed by `Σ(n)`.

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
