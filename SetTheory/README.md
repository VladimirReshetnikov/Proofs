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

## Building

Rocq/Coq ≥ 9.0 (developed against Rocq 9.0.1):

```sh
coqc Forward.v
coqc Reverse.v
```

No external libraries beyond the standard library (`Stdlib.Logic.ClassicalEpsilon`).
