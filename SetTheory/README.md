# SetTheory — machine-verified equivalence of the "Closure" axiomatization with ZF

- Created (UTC): 2026-06-30T04:48:30Z
- Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9

A Rocq/Coq formalization of Vladimir Reshetnikov's alternative axiomatization of
set theory and its equivalence with ordinary ZF — plus a complete, independent
**Lean 4 port** of the whole development under [`lean/`](lean/README.md).

## The axiomatization

Keep **Extensionality, Regularity, Separation, Powerset**. Drop
**Pairing, Union, Infinity, Replacement**. Add one schema:

> **Closure.** For every *set-like* class relation `≺`, the transitive closure of
> any set `s` under `≺` is a set.

with the readings

- `≺` is **set-like**: `∀x ∃y ∀z (z ≺ x ⇒ z ∈ y)` — every node's `≺`-predecessors
  are bounded by a set;
- `w` is a **superset of the transitive closure of `s` under `≺`**:
  `s ⊆ w ∧ ∀u ∀v (u ≺ v ∈ w ⇒ u ∈ w)` — `w` contains `s` and is closed under
  taking `≺`-predecessors.

Formally, the schema (one instance per definable binary relation `≺`, parameters
allowed) is

```
( ∀x ∃y ∀z (z ≺ x ⇒ z ∈ y) )  ⇒  ∀s ∃w ( s ⊆ w ∧ ∀u ∀v (u ≺ v ∈ w ⇒ u ∈ w) ).
```

**A note on Choice.** We work in ZF, not ZFC. The Axiom of Choice plays no part in
the trade between the four generative axioms and the Closure schema (neither
direction uses it), so it is omitted from both theories here; the Coq sources
declare no Choice hypothesis in either `T` or `ZF`. Adding it back is symmetric:
since `T` and `ZF` prove the same theorems, `T ∪ {C}` and `ZFC` coincide. (The
metatheoretic description operator the formalization uses — Hilbert's ε — is choice
in the *ambient logic*, not the set-theoretic axiom; see *Faithfulness* below.)

## The result

The system is **exactly ZF**:

| direction | statement | status | file |
|-----------|-----------|--------|------|
| forward   | `{Ext, Sep, Pow, Closure}` ⊢ Pairing, Union, Replacement, Infinity | **machine-checked** | [`Forward.v`](Forward.v) |
| reverse   | ZF ⊢ Closure (every set-like relation admits a transitive closure) | **machine-checked** | [`Reverse.v`](Reverse.v) |
| forward, first-order | same trade with the schemas as genuine syntactic formulas | **machine-checked** | [`Equivalence.v`](Equivalence.v) |
| proof calculus | ND calculus + soundness, and `ZF ⊢ φ ⟹ T ⊨ φ` | **machine-checked** | [`Calculus.v`](Calculus.v), [`Equivalence.v`](Equivalence.v) |
| model existence | every maximal-consistent Henkin theory is satisfiable (truth lemma) | **machine-checked** | [`Completeness.v`](Completeness.v) |
| completeness | `Γ ⊢ φ ⟺ Γ ⊨ φ` (soundness + Gödel completeness) | **machine-checked** | [`Completeness.v`](Completeness.v) |
| infinite completeness | `B ⊨ φ ⟹ B ⊢ φ` for sentence theories (compactness lift) | **machine-checked** | [`Completeness.v`](Completeness.v) |
| deductive equivalence | same-model sentence theories prove the same sentences | **machine-checked** | [`Completeness.v`](Completeness.v) |
| `ZF ⊢ φ ⟹ T ⊢ φ` | the forward syntactic direction, ZF/T as sentence theories | **machine-checked** | [`Equivalence.v`](Equivalence.v) |
| deep reverse | every first-order ZF model satisfies `Closure_form` (the internal recursion theorem) | **machine-checked** | [`Zf.v`](Zf.v), [`Equivalence.v`](Equivalence.v) |
| `T ⊢ φ ⟹ ZF ⊢ φ` | the converse syntactic direction | **machine-checked** | [`Equivalence.v`](Equivalence.v) |
| **`T ⊢ φ ⟺ ZF ⊢ φ`** | **full deductive equivalence** (`T_iff_ZF`) | **machine-checked** | [`Equivalence.v`](Equivalence.v) |

The Lean port also contains two Lean-first side modules that support nearby
foundational/computability work:

- [`lean/SetTheory/PAHF.lean`](lean/SetTheory/PAHF.lean) develops Ackermann-coded
  hereditary finite sets and first-order PA/HF interpretation infrastructure.
- [`lean/SetTheory/BusyBeaver.lean`](lean/SetTheory/BusyBeaver.lean) formalizes a
  Rado-style two-symbol blank-tape machine model and proves that any busy-beaver
  score function satisfying the maximum property eventually dominates every
  total recursive function whose recursiveness predicate has the standard
  linear-overhead blank-tape compiler.
- [`lean/SetTheory/BusyBeaverMathlib.lean`](lean/SetTheory/BusyBeaverMathlib.lean)
  is the mathlib-backed bridge showing that mathlib-total-recursive
  `Nat -> Nat` functions have sequential `ToPartrec.Code`s evaluated by
  mathlib's finite-support `PartrecToTM2` Turing machine.  It is built from the
  root `src/Lean` Lake workspace because the standalone SetTheory Lean project
  deliberately remains dependency-free.

## Module structure — the reusable core vs. the T-specific shell

The development is organized as a small library. Three modules are **generic
first-order logic** (nothing in them mentions ZF, let alone the Closure
axiomatization), one is **generic first-order ZF**, and only one file is about
the axiomatization T itself:

```text
Fol.v ──► Calculus.v ──► Completeness.v      generic FOL over the language {∈, =}
  │             │
  └──► Zf.v ◄───┘                            first-order ZF (no Powerset/Regularity needed)
                │
Forward.v   Reverse.v   Equivalence.v        the Closure axiomatization T, and T ⟺ ZF
(shallow, self-contained)   (imports all of the above)
```

- [`Fol.v`](Fol.v) — a deep embedding of first-order logic over one binary
  relation symbol and equality (De Bruijn variables): syntax, renaming and its
  equational theory, free variables, sentences, universal closure (`seal`), a
  surjective formula enumeration, Tarski satisfaction `Sat` over an arbitrary
  structure `(V, mem)`, and formula-definable relations (`relOf`). **Reusable for
  any theory whose signature is one binary relation** — set theories, graph
  theories, order theories.
- [`Calculus.v`](Calculus.v) — classical natural deduction `Prov` over those
  formulas, its admissible rules (weakening, cut, renaming admissibility, the
  equality kit), the Henkin-witness core lemmas, and
  **soundness** w.r.t. `Sat`. Theory-independent.
- [`Completeness.v`](Completeness.v) — **Gödel completeness** (`Prov G φ ⟺ G ⊨ φ`,
  via a quotient term model and a Lindenbaum/Henkin chain), the compactness-style
  lift to infinite **sentence theories** (`completeness_inf`), and
  **`theory_equiv`** — *two sentence theories with the same models prove the same
  sentences* — the abstract engine for proving any two axiomatizations
  deductively equivalent. Theory-independent.
- [`Zf.v`](Zf.v) — **first-order ZF**, with no reference to T: the ZF axioms as
  formulas and as a sentence theory (`ZFax_s`), extraction bridges from
  satisfaction to abstract semantic axioms, and the **internal mathematics of an
  arbitrary FO model of {Ext, Sep, Pair, Union, Inf, Repl}**: internal set
  algebra, Kuratowski pairs with injectivity, an internal ω with the
  definable-induction schema `omega_ind`, and the **finite recursion theorem**,
  culminating in `ClosureFO_of_ZF` (every definable set-like relation admits a
  closure superset, inside every such model). Reusable for any future "does
  first-order ZF prove schema S?" question.
- [`Equivalence.v`](Equivalence.v) — everything specific to the Closure
  axiomatization: the deep forward trade, `Closure_form`, `Tax_s`, the mutual
  model inclusions, and the syntactic equivalence `T_iff_ZF`.
- [`Forward.v`](Forward.v) / [`Reverse.v`](Reverse.v) — the original shallow
  (second-order) equivalence, kept self-contained with no inter-file imports.

The honest genericity boundary: the language is hard-wired to a *single binary
relation symbol plus equality* (with equality interpreted as genuine equality —
"normal" models), and the compactness lift applies to *sentence* theories.
Within that boundary, `Fol.v`/`Calculus.v`/`Completeness.v` are a self-contained,
axioms-clean Gödel-completeness library.

Regularity is **shared verbatim** between the two theories, so the
equivalence reduces to trading the four generative axioms `{Pairing, Union,
Infinity, Replacement}` for the single schema `Closure` over the common base
`{Ext, Sep, Pow}` (with Regularity and Choice as shared passengers, used by neither
direction). The forward file proves the interesting half; the reverse file proves
the standard half.

## Why it works — the linchpin

`Forward.v` isolates the one fact that makes the whole collapse happen — **hosting:
every set is a member of some set**:

```coq
Hypothesis Hosting : forall a, exists y, a ∈ y.
Definition host (a : V) : V := proj1_sig (constructive_indefinite_description _ (Hosting a)).
Lemma host_spec : forall a, a ∈ host a.
```

Consequently every singleton-valued (more generally, suitably bounded) class
relation is automatically set-like — its predecessor-class `{G(x)}` at each node `x`
is bounded by `host (G(x))`. That turns `Closure` into a fully general *collection*
principle, and the four lost axioms become four instances of one idea:

- **Union** = closure under `∈` (one step), then Separation;
- **Pairing** = closure of the seed `{∅,{∅}}` under the two-branch relation
  `(x=∅ ∧ z=a) ∨ (x={∅} ∧ z=b)` — `a` and `b` ride *different* seed nodes so each
  predecessor-class stays a singleton, hostable (putting both on one node would
  require bounding `{a,b}`, i.e. Pairing itself);
- **Replacement** = closure along a function graph `z = F(x)`, then Separation;
- **Infinity** = closure of `{∅}` under the successor relation `z = x ∪ {x}`.

**Powerset is more than this needs.** The trade never opens a powerset up; it uses
only hosting (`a ∈ 𝒫(a)` is one way to get it — `powerset_gives_hosting`). Hosting is
far weaker than Powerset (it holds in `H(ℵ₁)`, which has no `𝒫(ω)`). And *Powerset
restricted to finite sets is **not** enough*: the predecessors we must host (`a`,
`b`, `F x`, `x ∪ {x}`) are arbitrary, possibly infinite sets, which finite Powerset
cannot host. The genuine forward engine is `{Ext, Sep, Closure}` + hosting.

## Free dependency audit

Because the development is a Coq `Section` with the axioms as hypotheses, closing
the section generalizes each theorem over *exactly* the hypotheses it used. The
trailing `Check` commands in `Forward.v` print these, certifying:

- **Union** needs only **Separation + Closure** (not hosting, not Powerset, not
  Extensionality, not the nonempty-domain assumption);
- **Replacement** needs **Separation + Hosting + Closure** (no Powerset, no
  Extensionality, no nonemptiness);
- **Pairing** needs **Separation + Hosting + Closure** and a **nonempty domain** (to
  build `∅`) — and, now that the seed is built by Closure rather than a powerset, not
  even Extensionality;
- **Infinity** additionally needs **Extensionality** (inductive-set uniqueness);
- **Powerset** is used by **none** of the four (only by the side lemma
  `powerset_gives_hosting`); **Regularity** by none either — both, with Choice, are
  genuine passengers.

The same audit on the reverse direction (`Check Closure_holds` in `Reverse.v`)
shows `Closure_holds` depends on a nonempty domain, **Extensionality, Separation,
Pairing, Union, Infinity, Replacement** — but **neither Powerset nor Regularity**.
So the machine certifies the sharper statement *ZF − Powerset − Regularity ⊢
Closure*. The upshot for the two structural axioms:

- **Powerset** is the one *asymmetric* axiom, but even forward it is used only
  through its hosting shadow `∀a ∃y a∈y` (never as a powerset), and is idle in
  reverse;
- **Regularity** is idle in **both** directions — a passenger of the trade alongside
  Choice. The reverse direction needs only that the finite numerals `onat n` are
  distinct, which is a theorem of ZF *without* Foundation (each `onat n` is a
  transitive set with irreflexive membership — `onat_trans`, `onat_no_self`), so the
  global "no set is self-membered" fact (and hence Regularity) is never invoked.

## How the reverse direction works

`Reverse.v` builds the transitive closure of `s` under a set-like `R` the textbook
way, with the iteration carried on the *meta-level* `nat`:

1. for each node the predecessors are bounded (set-likeness), so the one-step
   predecessor set `predsf t = { u : ∃ v ∈ t, R u v }` is a genuine set — in ZF by
   Collection (a choice-free theorem) + Union + Separation. (The Coq code realizes
   this with a metatheoretic bounding function `boundf` via classical description:
   a convenience, not an object-level use of Choice.)
2. `gstep t = t ∪ predsf t`, and `Wₙ = iterate gstep s n` (Coq `Fixpoint` on `nat`);
3. to collect `{Wₙ : n}` into one object set we feed the object numerals
   `onat n ∈ Inf` (from Infinity) through Replacement via a map `Ffun` with
   `Ffun (onat n) = Wₙ` — well-defined because `onat` is injective (`onat_inj`),
   which in turn follows from the numerals being non-self-membered (`onat_no_self`,
   proved Foundation-free from `onat_trans` — *not* from Regularity);
4. `w = ⋃ (image)` then contains `s = W₀` and is closed under `R`-predecessors
   (`u R v`, `v ∈ Wₙ ⟹ u ∈ predsf Wₙ ⊆ W₍ₙ₊₁₎ ⊆ w`).

## Faithfulness (deep vs. shallow embedding)

This is a **shallow embedding**: the structure `(V, ∈)` is an abstract Coq type
with a relation, and the schemas (Separation, Closure, and the derived
Replacement) are rendered with the metatheory's predicates (`V -> Prop`,
`V -> V -> Prop`). The artifact therefore proves the **second-order** statement
"every structure satisfying these axioms satisfies those," which is the standard,
accepted way to mechanize equivalence of axiomatizations.

It stays faithful to the genuine first-order claim because **every derivation
instantiates a schema at one concrete, definable relation** (the two-branch
relation, a function graph, `∈`, successor) — exactly the instances a first-order
proof would use. What a shallow embedding does *not* deliver is a syntactic
`Provable(T, φ) ↔ Provable(ZF, φ)` theorem; that requires a deep embedding of
first-order logic and its proof calculus — which the rest of the library then
went on to build (`Fol.v` … `Equivalence.v`), culminating in exactly that
theorem, `T_iff_ZF`.

Classical logic enters only through `ClassicalEpsilon` (used to package the
existential axioms `Separation`/`Powerset` as the operators `sep`/`power`, and, in
`Reverse.v`, to extract a bounding function from set-likeness and to index the
iteration). This is *metatheoretic* choice — Hilbert's ε in the ambient logic, used
only to name objects the theory already asserts to exist — and is distinct from the
set-theoretic Axiom of Choice, which appears in neither theory (see *A note on
Choice* above). In `Reverse.v` the bounding function is a convenience: the
underlying ZF argument needs only the choice-free Collection schema, so no
object-level Choice is incurred.

## Closing the first-order gap (`Fol.v` + `Equivalence.v`)

The deep embedding removes the second-order rendering for the forward direction.
[`Fol.v`](Fol.v) supplies the language — a `form` datatype for the first-order
language of set theory (`=`, `∈`, with De Bruijn variables) and a Tarski
satisfaction relation `Sat : (nat→V) → form → Prop` — and
[`Equivalence.v`](Equivalence.v)'s `DeepForward` section states T's schemas
`SeparationFO` and `ClosureFO` over genuine **formulas** `phi`, `psi`
(interpreted by `Sat`/`relOf`), not over arbitrary `V→Prop`.

[`Equivalence.v`](Equivalence.v) (section `DeepForward`) then re-derives Pairing,
Union, **first-order Replacement**, and Infinity from
those first-order schemas, *exhibiting the relation each step uses as a concrete
formula* and verifying its `Sat`-meaning (`Hrel_pair`, `Hrel_mem`, `Hrel_succ`, and
for Replacement the renamed graph via `Sat_rename`/`chi_spec`). This certifies
formally — not as a meta-remark — that the schema-trade uses only **first-order
definable** instances. `Fol.v` supplies everything the trade needs: `form`, `Sat`, the
environment-extensionality lemma `Sat_ext`, and a De Bruijn renaming lemma
`Sat_rename` (the one piece Replacement needs, to express "∃x∈a, ψ(y,x)" as a
formula).

**Why the reverse direction is harder to deepen.** The forward trade ports cleanly
because every relation it uses (`pairing`, `∈`, `successor`, a function graph) is a
short first-order formula. The reverse direction does **not** port cheaply: its use
of Replacement is essential, and the collected map `n ↦ Wₙ` is first-order
definable only through the *syntactic recursion theorem*. `Reverse.v` deliberately
sidesteps that with a meta-level `nat` iteration; rendering it first-order means
formalizing the recursion theorem's defining formula — the genuinely heavy
object-level construction. That construction is now done: [`Zf.v`](Zf.v)
builds the defining formula for real (see below), so the first-order content of the
reverse direction — the recursion theorem — is machine-checked too.

## A proof calculus, soundness, and a cross-theory corollary (`Calculus.v` + `Equivalence.v`)

[`Calculus.v`](Calculus.v) carries the genuine **syntactic** layer:

- `Prov : list form → form → Prop`, a natural-deduction calculus over `form`
  (assumption, `→`/`∧`/`∨`/`∀`/`∃` intro+elim, ex falso, excluded middle,
  equality reflexivity and the Leibniz rule `P_eqElim` — `i=j` and `a[0:=i]`
  give `a[0:=j]`, which makes equality genuinely symmetric/transitive/congruent).
  Because the signature is purely relational, terms are just variables, so
  quantifier instantiation is a *renaming* — handled by the existing
  `rename`/`Sat_rename`, with no separate substitution operation.
- `soundness : Prov G a → ∀ e, (e ⊨ G) → Sat e a` — the calculus is sound for Tarski
  semantics (one case per rule; the quantifier/equality cases use `Sat_rename` and
  `Sat_ext`).

Encoding the ZF axioms as closed `form`s (`Ext_form … Reg_form`, plus the `Sep_form`
and `Repl_form` schemas) and proving this T-model satisfies each (via the derived
`Pairing`/`Union`/`ReplacementFO`/`Infinity` and the T-hypotheses) yields the
**cross-theory corollary**

```
ZF_provable_holds_in_T :
  (T-model) → ∀ φ, ZFprov φ → ∀ e, Sat e φ
```

i.e. **everything ZF proves holds in every model of the Closure axiomatization T**
(`ZF ⊢ φ ⟹ T ⊨ φ`), where `ZFprov` is provability in the ND calculus from the deep
ZF axiom set (all eight axioms; Separation and Replacement as schemas over `form`).
This combines the syntactic `soundness` with the forward semantic equivalence.

The symmetric corollary needs "every ZF-model satisfies `ClosureFO`", i.e. the
*deep reverse* direction — the recursion theorem as a first-order formula, proved
in [`Zf.v`](Zf.v) and applied in [`Equivalence.v`](Equivalence.v)
(`ZFmodel_sat_Closure`).

## Completeness (`Completeness.v`)

[`Completeness.v`](Completeness.v) builds **Gödel completeness** for the
`Calculus.v` calculus from scratch — a fully generic module: nothing in it
mentions any particular theory. The headline results:

```coq
completeness   : (forall Dom m v, (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi)
                 -> Prov G phi.
prov_iff_valid : Prov G phi <-> (forall Dom m v, (... |= G) -> Sat Dom m v phi).
```

i.e. **a formula is provable in the calculus iff it is valid in every model** —
soundness (`Calculus.v`) and completeness together. The development:

1. **Proof-theory infrastructure** (in `Calculus.v`) — weakening,
   proof-by-contradiction, double-negation, consistency (`Con`), the equality kit
   (symmetry/transitivity/congruence — derivable only after the calculus's
   equality rule was corrected to the Leibniz `P_eqElim`),
   renaming-admissibility `Prov_rename`, and cut `Prov_cut`.
2. **Model existence** `model_exists` (abstract maximal-consistent Henkin theory):
   a quotient term model (domain = canonical `ceq`-representatives via Hilbert ε,
   `D = {n | rep n = n}`) and the **truth lemma** by structural induction on the
   formula with the substitution generalized (the De Bruijn quantifier cases
   recurse on the body at a consed substitution, via `rename_inst_up`).
3. **Lindenbaum/Henkin** — a Cantor-pairing formula enumeration (`Enum`,
   surjective, from `Fol.v`), the eigenvariable lemma and the Henkin witness core
   lemmas (`henkin_ex_core`, `henkin_all_core`, from `Prov_rename` + freshness,
   in `Calculus.v`), and — built once, relative to a **sentence** base theory `B`
   plus a finite context (`BProv`) — the chain `chainB B L0 n` whose limit theory
   `Tinf` is shown maximal-consistent and Henkin (all five `model_exists`
   hypotheses). The Henkin-freshness obstacle for an infinite theory is overcome
   by the sentence restriction: a witness fresh for the finite added list is
   automatically fresh w.r.t. `B` (sentences have no free variables).
   `model_of_BCon`: a consistent sentence theory (plus finite context) has a
   model.
4. **Completeness** — finite-context completeness is the empty-base instance
   `B = ∅`: `BProv_empty` identifies `BProv (fun _ => False)` with plain `Prov`,
   so `model_of_BCon` specializes to `model_of_con` (a consistent set has a
   model); the contrapositive gives `completeness`, and with soundness,
   `prov_iff_valid`.
5. **Infinite completeness (compactness)** — the same machinery at an infinite
   sentence theory `B`:
   `completeness_inf : Sentences B → Sentence φ → (B ⊨ φ) → B ⊢ φ`, and
   `theory_equiv` — **two sentence theories with the same models prove the same
   sentences.**

The syntactic endgame **`ZF ⊢ φ ⟹ T ⊢ φ`** is then played out downstream: `ZF`
and `T` are encoded as sentence theories (`ZFax_s` in `Zf.v`, `Tax_s` in
`Equivalence.v`), every axiom universally closed by `seal` (the Closure schema as
the closed formula `Closure_form`). `Tmodel_sat_ZF` (in `Equivalence.v`) proves
*every T-model is a ZF-model* (extract the abstract axioms from a T-model through
the `bridge_*` lemmas, then reapply the derived `sat_*` of the forward trade), and
then soundness + `completeness_inf` give `ZF_implies_T`.

`Print Assumptions` lists only the standard classical-mathematics axioms (`classic`,
`constructive_indefinite_description`, and `functional_extensionality` /
`propositional_extensionality` / `proof_irrelevance`) — no `Admitted` anywhere.

## The deep reverse: the recursion theorem as a first-order formula (`Zf.v` + `Equivalence.v`)

[`Zf.v`](Zf.v) and [`Equivalence.v`](Equivalence.v) close the last gap: **every first-order model of
ZF satisfies every instance of `Closure_form`** (`ZFmodel_sat_Closure`), hence
**`T ⊢ φ ⟹ ZF ⊢ φ`** (`T_implies_ZF`) and the full deductive equivalence

```coq
T_iff_ZF : forall phi, Sentence phi ->
           (BProv Tax_s nil phi <-> BProv ZFax_s nil phi).
```

`Reverse.v` proves Closure from *second-order* Replacement, iterating the one-step
operator `g` on the metatheory's `nat` and collecting the stages with a
metatheoretic map — which a first-order model need not supply (a nonstandard model
has stages at nonstandard levels the meta-`nat` never reaches). `Zf.v`
instead runs the iteration **inside** an arbitrary first-order ZF model — the
finite recursion theorem rendered with genuine syntactic formulas:

1. **Internal set algebra** — pairs, unions, successors, and Kuratowski ordered
   pairs `kpair` with machine-checked injectivity (`kpair_inj`), all canonical by
   Extensionality.
2. **An internal ω** — carved out of the Infinity witness by the *formula* "x
   belongs to every inductive set", yielding the **definable-induction schema**
   `omega_ind`: induction over the internal naturals for any property given by a
   formula `phi` with parameters in the environment. This is the engine that
   replaces the meta-level `nat`. Internal arithmetic (`nat_transitive`,
   `nat_no_self`, `succ_inj_nat`, …) is proved by that schema, Foundation-free.
3. **A formula-macro library with satisfaction specs** — `fEmptyF`, `fSingF`,
   `fUPairF`, `fKPairF`, `fPairMemF`, `fSuccF`, `fInd`, and, relative to the
   closure relation `psi`, `fRF` (the renamed relation), `fStepF`
   ("y = g(t)"), `fApproxF`, `fThetaF`. Each macro is a genuine de Bruijn `form`
   whose satisfaction provably means the intended semantic statement; macros are
   made locally opaque after their spec so `cbn` composes them cleanly.
4. **The approximation predicate** `Approx f m` — "f is (the graph of) a function
   on `{0,…,m}` recording the stages `s, g(s), g(g(s)), …`", five clauses
   (functionality, domain bound, base pair `⟨0,s⟩`, domain coverage, recurrence
   `f(k+1) = g(f(k))`) — with **existence** (`Approx_exists`) and **agreement**
   (`Approx_agree`) both proved by internal induction. Agreement makes the stage
   relation `Theta y m := m ∈ ω ∧ ∃f (Approx f m ∧ ⟨m,y⟩ ∈ f)` **functional**
   (`theta_functional`) — exactly what first-order Replacement demands.
5. **Collection** — FO Replacement applied to `Theta` over ω collects the stages;
   their union is the closure set (`ClosureFO_of_ZF`).

Two structural points worth noting:

- **The one-step operator is canonical.** `Reverse.v` fed a *choice* of
  predecessor-bounds (Hilbert ε on set-likeness) through second-order Replacement.
  First-order Replacement cannot swallow a choice function, so `Zf.v`
  uses the canonical predecessor set `predSet v = { z : z ≺ v }` (carved by
  Separation inside an ε-chosen bound, but unique by Extensionality) and the
  definable graph formula "y = predSet(x)" (`psiPS`) — the ε leaks nothing into
  the object level.
- **Neither Powerset nor Regularity is used.** The model-side hypothesis list is
  `{Ext, Sep, Pair, Union, Inf, Repl}`, so the deep reverse inherits the
  sharpening *ZF − Powerset − Regularity ⊢ Closure* at the first-order level
  (visible in the `Check ClosureFO_of_ZF` output).

With `ZFmodel_sat_T` (every ZF-model is a T-model) and the converse
`Tmodel_sat_ZF` (both in `Equivalence.v`), the two theories have **exactly the same models**
(`T_ZF_same_models`); `T_iff_ZF` also falls out of the general `theory_equiv` as a
cross-check (`T_iff_ZF_via_theory_equiv`). `Print Assumptions T_iff_ZF` lists only
the same five classical axioms — no `Admitted` anywhere.

## What is proven

Machine-checked, no admits — the table is closed everywhere:

- The equivalence **semantically**, both directions: `Forward.v` (T ⟹ ZF axioms)
  and `Reverse.v` (ZF ⟹ Closure).
- The forward direction with **genuine first-order schemas**: `Fol.v` +
  `Equivalence.v`.
- A **sound** proof calculus and the bridge `ZF ⊢ φ ⟹ T ⊨ φ`: `Calculus.v` +
  `Equivalence.v`.
- **Soundness + completeness** for the calculus, `Prov G φ ⟺ G ⊨ φ`; **infinite
  completeness** (compactness) for sentence theories; and the **deductive
  equivalence of same-model sentence theories**: `Completeness.v`.
- The forward syntactic direction **`ZF ⊢ φ ⟹ T ⊢ φ`** (`ZF_implies_T`):
  `Equivalence.v`, on `Completeness.v`'s machinery.
- The **deep reverse** (every FO ZF model satisfies `Closure_form`; the internal
  recursion theorem), the converse **`T ⊢ φ ⟹ ZF ⊢ φ`**, and the headline
  **`T ⊢ φ ⟺ ZF ⊢ φ`** (`T_iff_ZF`): `Zf.v` + `Equivalence.v`.

## A written account

[`article/closure-axiomatization.tex`](article/closure-axiomatization.tex)
(rendered to [`article/closure-axiomatization.pdf`](article/closure-axiomatization.pdf))
is a detailed, tutorial-style article covering both the mathematics and this
formalization: the equivalence theorem, the four derivations as one
schema-instance family, the "how much Powerset?" analysis (the forward trade needs
only hosting — not full, nor even finite, Powerset — and Regularity and Choice are
passengers used in neither direction), the reverse transitive-closure recursion,
and then a section-by-section walkthrough of the whole Coq library (the shallow
embedding and the free dependency audit, the deep embedding closing the first-order
gap, the proof calculus and soundness, the from-scratch Gödel completeness /
compactness / `ZF ⊢ φ ⟹ T ⊢ φ` layer, and the deep reverse — the recursion theorem
as a first-order formula, closing `T ⊢ φ ⟺ ZF ⊢ φ`), including the module map. Build it with
`lualatex closure-axiomatization.tex` (run twice for the table of contents and
cross-references).

## Building

Rocq/Coq ≥ 9.0 (developed against Rocq 9.0.1):

```sh
# the shallow layer is self-contained:
coqc Forward.v
coqc Reverse.v
# the library builds in dependency order under the SetTheory namespace:
coqc -Q . SetTheory Fol.v
coqc -Q . SetTheory Calculus.v
coqc -Q . SetTheory Completeness.v
coqc -Q . SetTheory Zf.v
coqc -Q . SetTheory Equivalence.v
```

`Forward.v` and `Reverse.v` are independent (no inter-file `Require`) and need only
the standard library. The library files import along the DAG shown above
(`Fol` ← `Calculus` ← `Completeness`; `Fol`, `Calculus` ← `Zf`; everything ←
`Equivalence`). `Completeness.v` additionally uses the standard
classical/extensionality axiom modules (`ClassicalEpsilon`,
`FunctionalExtensionality`, `PropExtensionality`, `ProofIrrelevance`) for the
quotient term model — all consistent with the classical setting already in use.

## The Lean 4 port (`lean/`)

The entire Closure/ZF development is also machine-checked a **second time, in
Lean 4** (4.31.0, core only — no Mathlib), under [`lean/`](lean/): seven modules
mirror the seven Coq files one-to-one (`Fol.lean` … `Equivalence.lean`,
`Forward.lean`, `Reverse.lean`), every statement with the same logical content,
through the same headline theorem `T_iff_ZF`. The Lean workspace also contains
[`lean/SetTheory/PAHF.lean`](lean/SetTheory/PAHF.lean), a Lean-first
formalization toward the bi-interpretability of Peano arithmetic and hereditary
finite sets. Its current checked surface includes Ackermann-coded HF on `Nat`,
finite von Neumann ordinals, shallow PA/HF round-trip isomorphisms, first-order
HF axiom schemas in the membership language, and a separate first-order PA syntax
with sealed PA axiom semantics; the remaining syntactic bridge is the explicit
formula translation between PA and HF. `lean/SetTheory/Audit.lean` replays the
`Print Assumptions` audit: the Lean proof depends only on `propext`,
`Classical.choice`, and `Quot.sound` — Lean's standard classical axioms — with no
`sorry` anywhere.
Because Lean generalizes hypotheses as explicit named parameters rather than
via Coq's `Section` mechanism, the free dependency audit is *visible in each
theorem's signature* there (e.g. `Reverse.Closure_holds` literally takes no
Powerset and no Regularity argument). Build with `cd lean && lake build`;
see [`lean/README.md`](lean/README.md) for the module map and the full list
of (mechanical) translation deviations.
