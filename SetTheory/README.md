# SetTheory — machine-verified equivalence of the "Closure" axiomatization with ZF

- Created (UTC): 2026-06-30T04:48:30Z
- Repository HEAD: adeba87107a01ad82de9c28edd492a3d7d816ef9

A Rocq/Coq formalization of Vladimir Reshetnikov's alternative axiomatization of
set theory and its equivalence with ordinary ZF(C).

## The axiomatization

Keep **Extensionality, Regularity, Separation, Powerset, Choice**. Drop
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

## The result

The system is **exactly ZF** (and with the shared Choice axiom, exactly ZFC):

| direction | statement | status | file |
|-----------|-----------|--------|------|
| forward   | `{Ext, Sep, Pow, Closure}` ⊢ Pairing, Union, Replacement, Infinity | **machine-checked** | [`Forward.v`](Forward.v) |
| reverse   | ZF ⊢ Closure (every set-like relation admits a transitive closure) | **machine-checked** | [`Reverse.v`](Reverse.v) |
| forward, first-order | same trade with the schemas as genuine syntactic formulas | **machine-checked** | [`Deep.v`](Deep.v) |
| proof calculus | ND calculus + soundness, and `ZF ⊢ φ ⟹ T ⊨ φ` | **machine-checked** | [`Deep.v`](Deep.v) |
| model existence | every maximal-consistent Henkin theory is satisfiable (truth lemma) | **machine-checked** | [`Completeness.v`](Completeness.v) |
| completeness | `Γ ⊢ φ ⟺ Γ ⊨ φ` (soundness + Gödel completeness) | **machine-checked** | [`Completeness.v`](Completeness.v) |

Regularity and Choice are **shared verbatim** between the two theories, so the
equivalence reduces to trading the four generative axioms `{Pairing, Union,
Infinity, Replacement}` for the single schema `Closure` over the common base
`{Ext, Sep, Pow}` (+ Regularity, + Choice). The forward file proves the
interesting half; the reverse file proves the standard half.

## Why it works — the linchpin

`Forward.v` isolates the one fact that makes the whole collapse happen:

```coq
Lemma self_in_power : forall a, a ∈ power a.   (* a ⊆ a, so a ∈ 𝒫(a) *)
```

**Powerset gives every set a host.** Consequently every singleton-valued (more
generally, suitably bounded) class relation is automatically set-like — its
predecessor-class `{G(x)}` at each node `x` is bounded by `𝒫(G(x))`. That turns
`Closure` into a fully general *collection* principle, and the four lost axioms
become four instances of one idea:

- **Union** = closure under `∈` (one step), then Separation;
- **Pairing** = closure of the seed `{∅,{∅}}` under the two-branch relation
  `(x=∅ ∧ z=a) ∨ (x={∅} ∧ z=b)` — `a` and `b` ride *different* seed nodes so each
  predecessor-class stays a singleton, hostable by a powerset (putting both on one
  node would require bounding `{a,b}`, i.e. Pairing itself);
- **Replacement** = closure along a function graph `z = F(x)`, then Separation;
- **Infinity** = closure of `{∅}` under the successor relation `z = x ∪ {x}`.

## Free dependency audit

Because the development is a Coq `Section` with the axioms as hypotheses, closing
the section generalizes each theorem over *exactly* the hypotheses it used. The
trailing `Check` commands in `Forward.v` print these, certifying:

- **Union** needs only **Separation + Closure** (not Powerset, not Extensionality,
  not the nonempty-domain assumption);
- **Replacement** needs **Separation + Powerset + Closure** (no Extensionality, no
  nonemptiness);
- **Pairing** and **Infinity** additionally need **Extensionality** and a
  **nonempty domain** (to build `∅` and tell `∅ ≠ {∅}` apart);
- **Regularity** is used by **none** of the four — it is a genuine passenger.

The `Powerset` hypothesis appears in Pairing/Replacement/Infinity precisely in its
host-providing role.

The same audit on the reverse direction (`Check Closure_holds` in `Reverse.v`)
shows `Closure_holds` depends on a nonempty domain, **Extensionality, Separation,
Pairing, Union, Infinity, Replacement, Regularity** — but **not Powerset**. So the
machine certifies the sharper statement *ZF − Powerset ⊢ Closure*. Note the
pleasant mirror image:

- **Powerset** is load-bearing forward (it hosts every set) and idle in reverse;
- **Regularity** is idle forward and load-bearing in reverse (it powers
  `no_self_mem`, hence injectivity of the numerals `onat`, which is what pins the
  Replacement index when collecting `{Wₙ}`).

## How the reverse direction works

`Reverse.v` builds the transitive closure of `s` under a set-like `R` the textbook
way, with the iteration carried on the *meta-level* `nat`:

1. set-likeness yields a bounding function `boundf` (one bound per node, via
   classical description), so the one-step predecessor set
   `predsf t = { u : ∃ v ∈ t, R u v }` is a genuine set
   (`⋃` of the `boundf`-image of `t`, then Separation);
2. `gstep t = t ∪ predsf t`, and `Wₙ = iterate gstep s n` (Coq `Fixpoint` on `nat`);
3. to collect `{Wₙ : n}` into one object set we feed the object numerals
   `onat n ∈ Inf` (from Infinity) through Replacement via a map `Ffun` with
   `Ffun (onat n) = Wₙ` — well-defined because `onat` is injective
   (`onat_inj`, from `no_self_mem`);
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
`Provable(T, φ) ↔ Provable(ZF, φ)` theorem; that would require a deep embedding of
first-order logic and its proof calculus, a much larger project with little
additional mathematical insight.

Classical logic enters only through `ClassicalEpsilon` (used to package the
existential axioms `Separation`/`Powerset` as the operators `sep`/`power`, and, in
`Reverse.v`, to extract a bounding function from set-likeness and to index the
iteration). Set theory is classical anyway, and Choice rides along.

## Closing the first-order gap (`Deep.v`)

`Deep.v` removes the second-order rendering for the forward direction. It defines

- a `form` datatype for the first-order language of set theory (`=`, `∈`, with De
  Bruijn variables) and a Tarski satisfaction relation `Sat : (nat→V) → form → Prop`;
- the schemas `SeparationFO` and `ClosureFO` quantifying over genuine **formulas**
  `phi`, `psi` (interpreted by `Sat`/`relOf`), not over arbitrary `V→Prop`.

It then re-derives Pairing, Union, **first-order Replacement**, and Infinity from
those first-order schemas, *exhibiting the relation each step uses as a concrete
formula* and verifying its `Sat`-meaning (`Hrel_pair`, `Hrel_mem`, `Hrel_succ`, and
for Replacement the renamed graph via `Sat_rename`/`chi_spec`). This certifies
formally — not as a meta-remark — that the schema-trade uses only **first-order
definable** instances. The development is self-contained: `form`, `Sat`, the
environment-extensionality lemma `Sat_ext`, and a De Bruijn renaming lemma
`Sat_rename` (the one piece Replacement needs, to express "∃x∈a, ψ(y,x)" as a
formula).

**Why only the forward direction is deepened.** The forward trade ports cleanly
because every relation it uses (`pairing`, `∈`, `successor`, a function graph) is a
short first-order formula. The reverse direction does **not** port cheaply: its use
of Replacement is essential, and the collected map `n ↦ Wₙ` is first-order
definable only through the *syntactic recursion theorem*. `Reverse.v` deliberately
sidesteps that with a meta-level `nat` iteration; rendering it first-order would
mean formalizing the recursion theorem's defining formula — the genuinely heavy
object-level construction. So the first-order content of the reverse direction *is*
the recursion theorem, which is left at the (already verified) shallow level.

## A proof calculus, soundness, and a cross-theory corollary (`Deep.v`)

`Deep.v` also carries a genuine **syntactic** layer:

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

The symmetric corollary `T ⊢ φ ⟹ ZF ⊨ φ` needs "every ZF-model satisfies
`ClosureFO`", i.e. the *deep reverse* direction — blocked at the same point as
above (the recursion theorem as a first-order formula).

## Completeness (`Completeness.v`)

[`Completeness.v`](Completeness.v) builds **Gödel completeness** for the `Deep.v`
calculus from scratch (requires the `SetTheory` namespace:
`coqc -Q . SetTheory Deep.v` then `coqc -Q . SetTheory Completeness.v`). The
headline results:

```coq
completeness   : (forall Dom m v, (forall g, In g G -> Sat Dom m v g) -> Sat Dom m v phi)
                 -> Prov G phi.
prov_iff_valid : Prov G phi <-> (forall Dom m v, (... |= G) -> Sat Dom m v phi).
```

i.e. **a formula is provable in the calculus iff it is valid in every model** —
soundness (`Deep.v`) and completeness together. The development:

1. **Proof-theory infrastructure** — weakening, deduction theorem,
   proof-by-contradiction, double-negation, consistency (`Con`), the Lindenbaum step
   `Con_cons_or`, the equality kit (symmetry/transitivity/congruence — derivable
   only after `Deep.v`'s equality rule was corrected to the Leibniz `P_eqElim`),
   renaming-admissibility `Prov_rename`, and cut `Prov_cut`.
2. **Model existence** `model_exists` (abstract maximal-consistent Henkin theory):
   a quotient term model (domain = canonical `ceq`-representatives via Hilbert ε,
   `D = {n | rep n = n}`) and the **truth lemma** by strong induction on formula
   size (renaming preserves size, so the De Bruijn quantifier cases recurse).
3. **Lindenbaum/Henkin** — a Cantor-pairing formula enumeration (`Enum`,
   surjective), the eigenvariable lemma and Henkin witness lemmas (`henkin_ex`,
   `henkin_all`, from `Prov_rename` + freshness), and the chain `chain G0 n` whose
   limit theory `TL` is shown maximal-consistent and Henkin (all five
   `model_exists` hypotheses).
4. **Completeness** — `model_of_con` (a consistent set has a model), then the
   contrapositive gives `completeness`, and with soundness, `prov_iff_valid`.

`Print Assumptions completeness` lists only the standard classical-mathematics
axioms (`classic`, `constructive_indefinite_description`, and
`functional_extensionality` / `propositional_extensionality` /
`proof_irrelevance`) — no `Admitted`.

## What is proven

- The equivalence **semantically**, both directions: `Forward.v` (T ⟹ ZF axioms)
  and `Reverse.v` (ZF ⟹ Closure).
- The forward direction with **genuine first-order schemas**: `Deep.v`.
- A **sound** proof calculus and the bridge `ZF ⊢ φ ⟹ T ⊨ φ`: `Deep.v`.
- **Soundness + completeness** for the calculus, `Prov G φ ⟺ G ⊨ φ`: `Completeness.v`.

The one piece beyond this for a literal syntactic `ZF ⊢ φ ⟺ T ⊢ φ` is lifting
completeness from finite contexts to **infinite theories** (compactness): `ZF` and
`T` are infinite axiom sets, so `ZF ⊢ φ` means provability from a finite subset.
With infinite-theory completeness, soundness + the `Deep.v` forward equivalence give
`ZF ⊢ φ ⟹ T ⊢ φ` outright (the reverse syntactic direction still also needs the
deep reverse, i.e. the recursion theorem as a formula). The general
`Prov G φ ⟺ G ⊨ φ` proven here is the substance; the lift is routine.

## Building

Rocq/Coq ≥ 9.0 (developed against Rocq 9.0.1):

```sh
coqc Forward.v
coqc Reverse.v
coqc Deep.v
# Completeness.v builds on Deep via the SetTheory namespace:
coqc -Q . SetTheory Deep.v
coqc -Q . SetTheory Completeness.v
```

`Forward.v`, `Reverse.v`, `Deep.v` are independent (no inter-file `Require`) and need
only the standard library. `Completeness.v` `Require`s `Deep` (hence the `-Q`
namespace) and additionally uses the standard classical/extensionality axiom modules
(`ClassicalEpsilon`, `FunctionalExtensionality`, `PropExtensionality`,
`ProofIrrelevance`) for the quotient term model — all consistent with the classical
setting already in use.
