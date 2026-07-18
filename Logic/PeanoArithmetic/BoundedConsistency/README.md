# Bounded-complexity consistency for Peano arithmetic

This project studies the following **numeralwise consistency scheme** for
first-order Peano arithmetic (PA): for every natural number `n` chosen in the
metatheory, PA proves that no PA derivation in which every formula occurrence
has at most `n` quantifier groups derives falsity.

The phrase “every formula occurrence” and the metatheoretic status of `n` are
essential.  They are part of the formal specification, not presentational
details.

> **Current status.**  The Lean and Rocq/Coq phase-one developments
> machine-check a metatheoretic restricted-proof construction and its semantic
> consistency consequences for the repository's PA/HF natural-deduction
> calculus.  They compute mutually recursive syntactic `Sigma` and `Pi`
> polarity ranks in the host logic and use faithful, data-carrying proof-tree
> mirrors to inspect every occurrence.  They
> do **not** yet arithmetize that hierarchy test or proof predicate, construct
> partial truth inside PA, or prove an object sentence in the PA calculus.  In
> particular, the requested theorem `PA ⊢ Con_n(PA)` for each external `n` is
> **not yet implemented**.

## The intended theorem

Fix a Gödel coding of PA formulae and derivations.  Let `AHBound(n, p)` mean
that `p` codes a formula in `Sigma_n` or `Pi_n` of the arithmetical hierarchy,
with bounded quantifiers ignored in the usual way.  Define

```text
RestrictedProof_n(d, p) :=
  d is a PA derivation of p, and
  every formula occurrence at every node of d satisfies AHBound(n, -).

Con_n(PA) := not exists d, RestrictedProof_n(d, code(false)).
```

For a one-sided sequent calculus, “every formula occurrence” includes every
formula in every sequent, every principal formula, every premise formula, and
every cut formula.  It also includes the formula used by an axiom instance.
Equivalent bookkeeping is required for natural deduction or a Hilbert
calculus.  Restricting only axioms, only cut formulae, or only the concluding
sentence is not the statement of this project.

The target is an externally indexed family of formal derivations:

```text
for each metatheoretic n : nat, construct a derivation PA |- Con_n(PA).
```

In Lean or Coq this may be exposed as a theorem with a host-language argument
`n : Nat`/`n : nat`, returning an object-level PA derivation.  The parameter is
specialized by the proof assistant before the resulting PA proof is read.  It
must not be silently strengthened to the single object-level assertion

```text
PA |- forall n, Con_n(PA).
```

## Why the bound covers the entire proof

Falsity is quantifier-free.  Therefore, if the restriction were imposed only
on the final statement, then for every `n` the alleged theorem would simply
say that PA has no proof of falsity at all: it would be the ordinary
consistency statement `Con(PA)`.  Under the usual consistency and
representability hypotheses, Gödel's second incompleteness theorem prevents
PA from proving that statement.

The all-occurrences restriction changes the claim.  A fixed complexity bound
allows a fixed partial truth definition.  That partial truth predicate can be
proved compositional for every formula appearing in the restricted
derivation, so PA can verify the soundness of that restricted derivation
without defining truth for arbitrary arithmetic formulae.

This restriction also has to be visible in the arithmetized proof predicate.
It is not enough to observe externally that each standard proof is finite and
therefore has a maximum formula complexity.  An internal PA theorem quantifies
over nonstandard proof codes in nonstandard PA models as well.

## Phase-one hierarchy measure and the representation gap

The phase-one ports compute two polarity-sensitive syntactic ranks
simultaneously, one `Sigma`-oriented and one `Pi`-oriented.  Atoms have level
zero.  Boolean connectives combine the corresponding ranks componentwise;
negation and the antecedent of implication exchange the two polarities.
Universal and existential quantifiers preserve an already matching outer
block and add a level when the polarity switches.  Consequently, Boolean
branches with different leading polarities are aligned at the correct higher
level rather than being underestimated by a raw maximum over syntax-tree
branches.

For example, the two branches of

```text
(exists x, P(x)) and (forall y, Q(y))
```

have opposite polarities.  The mutually computed ranks place their conjunction
at the next level; they do not incorrectly call the whole formula a one-group
formula merely because each individual branch has one group.

This is the intended **external, metatheoretic** hierarchy measurement for the
phase-one syntax.  The remaining gap is representational: its recursive host
function is not yet a predicate on Gödel numbers expressed by a formula of PA.
Nor has its correspondence with the concrete coded syntax used by PA's proof
predicate yet been established.

The Lean foundation library supplies the closely related typed predicate
`LO.FirstOrder.Arithmetic.Hierarchy`.  Its constructors preserve level across
genuinely bounded quantifiers, preserve a block of matching polarity, and
increase the level when polarity alternates.  The intended final domain
predicate on Gödel codes corresponds to

```text
Hierarchy Sigma n phi or Hierarchy Pi n phi.
```

Because the restricted-proof predicate must itself live inside arithmetic,
the project still needs code-level `IsSigma n` and `IsPi n` recognizers and
proofs that they agree both with the phase-one rank computation and with this
typed hierarchy on standard quoted formulae.  Bounded quantifiers must be
ignored at this final correspondence boundary even if the small phase-one
syntax represents only primitive unbounded quantifiers.

## What phase one checks

Both phase-one developments separate four notions which are easy to conflate:

1. the ordinary proof relation;
2. a data-carrying proof tree whose numeric rank bounds every formula
   occurrence by a fixed polarity-sensitive hierarchy level;
3. the resulting restricted-provability relation; and
4. semantic soundness or consistency of that restricted relation under the
   corresponding semantic hypotheses.

The repository's original proof relation lives in `Prop`, so proof
irrelevance prevents either kernel from computing a numeric rank by inspecting
an ordinary proof witness.  Both ports therefore mirror the 17 inference rules
in a `Type`-valued `ProvTree`.  Erasure maps a tree to an ordinary proof, while
ordinary derivability propositionally supplies a tree.  Thus the mirror is a
faithful data presentation of the same calculus, not an added proof system.

Erasing the ranked tree recovers an ordinary proof.  Consequently,
restricted provability implies ordinary provability.  Both ports then combine
erasure with the existing soundness theorem and validity of the PA axioms in
the standard natural-number model to rule out a restricted derivation of
falsity for every external bound, without assuming PA's consistency.  This
phase-one theorem is not a new internal soundness proof by partial truth.

These are genuine kernel-checked metatheorems about the phase-one datatypes.
They do not assert that PA represents those datatypes or proves their
soundness.

### Lean theorem surface

The module `BoundedPAConsistency.Basic`, in namespace
`LeanProofs.BoundedPAConsistency`, provides:

- `sigmaRank`, `piRank`, `quantifierGroups`, and `QuantifierBounded`;
- `hierarchyRanks_rename` and `hierarchyRanks_subst`, together with the
  corresponding one-rank and boundedness corollaries;
- `contextRank`, `nodeRank`, the `Type`-valued `ProvTree`, and numeric
  `proofOccurrenceRank`; the rank includes each node's conclusion, its entire
  displayed context, every formula-valued rule parameter, and all recursive
  premises;
- `eraseProvTree` and `provTree_complete`, proving the two directions of the
  faithful relationship with `PA.Formula.Prov`;
- `ProofAllBounded`, `RestrictedProv`, and theory-relative `RestrictedBProv`;
- monotonicity in the bound and metatheoretic cofinality of the restricted
  relations among all finite ordinary derivations;
- `restrictedProv_erase` and `restrictedBProv_erase`;
- `conclusionRestrictedProv_bot_iff` and
  `conclusionRestrictedBProv_bot_iff`, which formally expose the
  conclusion-only error; and
- the external theorem
  ```lean
  theorem restrictedPA_consistent_standard (n : Nat) :
      ¬ RestrictedBProv n PA.Formula.Ax_s [] PA.Formula.bot
  ```

### Rocq/Coq theorem surface

The module `BoundedPAConsistency.BoundedConsistency`, inside
`PABoundedConsistency`, provides the parallel definitions `sigmaRank`,
`piRank`, `quantifierGroups`, `QuantifierBounded`, `contextRank`,
`ProvTree`, `proofOccurrenceRank`, `ProofAllBounded`, `RestrictedProv`, and
`RestrictedBProv`.  Its tree erasure/completeness, preservation,
monotonicity, cofinality, and conclusion-only-collapse lemmas parallel the Lean
surface.  Its headline phase-one result is:

```coq
Theorem restrictedPA_consistent_standard : forall n,
  ~ RestrictedBProv n Formula.Ax_s [] pBot.
```

Both occurrence ranks explicitly cover each formula-valued inference-rule
parameter.  Term parameters cannot change formula rank.

### Lean coded-induction bridge

`BoundedPAConsistency.Internal` reuses Foundation's nonstandard-model coding
of syntax and least-fixed-point derivations.  Its `inductionAtHierarchy`
generalizes the library's coded fixed-point induction from a hard-coded
level-one invariant to an invariant at any externally fixed positive
arithmetical-hierarchy level, assuming the matching induction fragment.
`inductionInPeanoModel` discharges that fragment in an arbitrary model of full
PA.  This is infrastructure for pushing a future partial-truth invariant
through coded derivations; it is neither a partial truth predicate nor a
reflection theorem.

The current Rocq/Coq foundation has no corresponding arithmetized syntax and
fixed-point derivation library, so this bridge presently has no Rocq analogue.

## The standard partial-truth argument

For each fixed external `n`, the full proof should implement the classical
partial-truth argument as follows.

1. **Code the hierarchy.**  Define delta-zero/primitive-recursive predicates
   `IsSigma(n, p)` and `IsPi(n, p)` on formula codes.  Prove constructor,
   inversion, negation, substitution, shift, and monotonicity lemmas, as well
   as correctness on quotations of standard formulae.
2. **Restrict derivations structurally.**  Arithmetize a derivation predicate
   whose recursive clauses require the hierarchy bound at every node.  This
   must include formulae introduced only in premises or as cut formulae.
3. **Evaluate coded terms.**  Define the value of a coded arithmetic term under
   coded bound- and free-variable environments.  Prove totality,
   functionality, and compatibility with weakening and substitution in PA.
4. **Construct partial satisfaction.**  For the fixed `n`, define dual
   satisfaction predicates for `Sigma_n` and `Pi_n` codes.  Establish the
   Tarski clauses for atoms, Boolean connectives, bounded quantifiers, and each
   permitted unbounded quantifier block.  Prove that the two predicates are
   complementary under coded negation.
5. **Verify the logical rules.**  Induct internally on the restricted
   derivation code and prove that every derived sequent contains a partially
   true formula.  The induction predicate has a fixed finite hierarchy level,
   so full PA supplies the required induction for each external `n`.
6. **Verify PA axioms.**  The finitely many non-induction axioms are immediate.
   An induction axiom is true because PA induction applies to the formula
   saying that its coded body is partially satisfied.  This step must also
   handle nonstandard pseudo-formulae accepted by PA's delta-one axiom
   recognizer in a nonstandard model; correctness merely for standard quoted
   axioms is insufficient.
7. **Exclude the false sequent.**  The compositional falsity clause shows that
   a restricted derivation whose final sequent is the singleton containing
   falsity cannot exist.  Package this statement as the arithmetic sentence
   `Con_n(PA)` and construct its PA proof.

One viable Lean endpoint is model-theoretic: prove `Con_n(PA)` in every model
of PA, including nonstandard models, and apply the foundation library's
first-order completeness theorem.  A direct syntactic PA derivation is equally
acceptable but does not remove the need to reason about arbitrary coded
derivations inside PA.

## Gödel-II boundary

The target does not contradict Gödel's second incompleteness theorem.

- Each standard `n` is fixed outside PA, and its partial truth predicate is a
  separate finite construction.
- No one of the sentences `Con_n(PA)` rules out PA proofs using formulae of
  greater complexity.
- There is no claim that PA proves the universal closure over all `n`.

With the intended coding, PA can verify that any alleged proof code has some
formula-complexity bound.  Therefore a single PA proof of
`forall n, Con_n(PA)` would yield ordinary `Con(PA)`.  Likewise, a purported
uniform truth predicate covering all levels would cross Tarski's
undefinability boundary.  The numeralwise family avoids both uniformizations.

## Roadmap to the requested theorem

The following work remains; items are intentionally phrased as proof
obligations rather than implementation guesses.

- [x] Instantiate the existing Lean and Coq PA/HF formula and proof datatypes
  with independent restricted-proof wrappers.
- [x] Define mutually recursive syntactic `Sigma`/`Pi` polarity ranks in the
  phase-one host syntax.
- [x] Require the phase-one bound at every formula occurrence.
- [x] Add faithful `Type`-valued proof trees, erasure/completeness,
  monotonicity, and metatheoretic cofinality in both ports.
- [x] Prove conclusion-only collapse and external standard-model consistency
  of the restricted PA calculus without a separate consistency hypothesis.
- [ ] Prove and audit the exact relationship between the phase-one rank pair
  and the foundation library's typed `Sigma_n`/`Pi_n` hierarchy, including the
  treatment of bounded quantifiers.
- [ ] Define code-level hierarchy recognizers in Lean and Coq and prove their
  correspondence with the typed/meta-level hierarchy.
- [ ] Prove closure of the code-level bound under every syntactic operation
  used by the proof calculus: negation, shift, bound-variable opening,
  substitution, universal closure, and formation/inversion of principal
  formulae.
- [ ] Define the all-occurrences restricted derivation predicate over the
  repository's actual Gödel coding, and prove it delta-one (with restricted
  provability sigma-one and restricted consistency pi-one).
- [ ] Formalize coded environments and term evaluation, including totality and
  substitution lemmas in PA.
- [ ] Construct fixed-level partial satisfaction and prove all Tarski clauses
  in PA.
- [x] In Lean, generalize arithmetized fixed-point induction from level-one
  invariants to every externally fixed positive hierarchy level and specialize
  it to models of full PA.
- [ ] Build or port the corresponding coded-derivation induction machinery in
  Rocq/Coq.
- [ ] Prove soundness of every logical inference for partial satisfaction.
- [ ] Prove partial truth of all PA-minus axioms.
- [ ] Prove partial truth of every internally recognized induction axiom,
  including nonstandard instances in nonstandard PA models.
- [ ] Define the object sentence `Con_n(PA)` and prove its representation
  theorem in both ports.
- [ ] Construct, for each external `n`, a checked object-level derivation
  `PA |- Con_n(PA)` in Lean and Coq.
- [ ] Add audits that print/check the assumptions of the final theorem and
  reject admissions, project-local axioms, or semantic soundness hypotheses at
  the headline boundary.
- [ ] Record parity explicitly: theorem statements and mathematical coding
  contracts must coincide even when the concrete Gödel encodings differ.

## Building phase one

From the repository root, the Lean library is registered as
`BoundedPAConsistency`:

```bash
lake build BoundedPAConsistency.Basic BoundedPAConsistency.Internal \
  BoundedPAConsistency.Audit \
  BoundedPAConsistency
```

The Rocq/Coq logical path is `BoundedPAConsistency`.  The root `_CoqProject`
registers both the implementation and audit.  They can be checked directly
against the already-built dependencies with:

```bash
opam exec --switch=proofs-rocq92 -- rocq compile \
  -Q Logic/FirstOrder/Coq FirstOrder \
  -Q Logic/Interpretability/PAHF/Coq PAHF \
  -Q Logic/PeanoArithmetic/BoundedConsistency/Coq BoundedPAConsistency \
  Logic/PeanoArithmetic/BoundedConsistency/Coq/BoundedConsistency.v

opam exec --switch=proofs-rocq92 -- rocq compile \
  -Q Logic/FirstOrder/Coq FirstOrder \
  -Q Logic/Interpretability/PAHF/Coq PAHF \
  -Q Logic/PeanoArithmetic/BoundedConsistency/Coq BoundedPAConsistency \
  Logic/PeanoArithmetic/BoundedConsistency/Coq/Audit.v
```

The audit modules, rather than this README, are the authority for the exact
kernel assumptions and public theorem surface.
