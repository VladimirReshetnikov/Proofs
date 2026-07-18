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
> calculus.  Rocq additionally has canonical natural-number codes, total
> decoders, and an executable checker for those restricted proof trees, with
> exact quotation and soundness theorems.  Lean now goes beyond standard
> codes: in every possibly nonstandard model of `I Sigma 1` it represents the
> coded polarity rank, all-occurrences restricted derivation predicate, and
> fixed-external-bound consistency sentence.  It also has represented coded
> term evaluation, nonstandard-code shift/substitution transport, and a
> rank-zero formula truth predicate with structural and Boolean Tarski
> clauses and semantic transport under negation, shift, and substitution.
> Lean also proves every rank-zero logical inference sound for arbitrary
> nonstandard restricted-derivation codes, discharges the full internal PA
> axiom recognizer at rank zero, and obtains the actual object theorem
> `PA ⊢ Con_0(PA)`.  It now also defines externally indexed Sigma/Pi partial
> truth predicates over nonstandard codes, proves their fixed-level
> definability, and establishes oriented Boolean/quantifier Tarski clauses,
> including both polarity switches.  Rocq now has both the earlier
> standard-model representing formula and a transparent canonical arithmetic
> formula describing accepting traces of the concrete compiled checker.  The
> compiler theorem proves that the canonical machine accepts exactly when the
> executable restricted-proof checker returns true on standard naturals, and
> the trace certificate shell has been unfolded in arbitrary raw PA models.
> Rocq also has a generic route from arbitrary raw-model validity to an
> object-level PA proof, and the canonical fixed-bound consistency sentence
> is now proved equivalent to rejection of accepting canonical traces in
> every raw PA model.  The finite transition formula and every internally
> indexed adjacent pair in its beta-coded trace are now reflected exactly to
> raw-carrier steps of the concrete Minsky program.  Beta functionality now
> makes those local descriptions agree on every live counter, while the
> canonical initial state, accepting output, and final program-counter
> boundary are decoded exactly from one graph witness.  A PA
> zero-or-successor argument further identifies them with one genuine full
> state at the possibly nonstandard final index.  Nonstandard trace
> rejection itself remains open.
> Lean now has full fixed-level polarity coherence, shift/substitution
> transport, a unified bounded truth interface, and soundness of every coded
> logical inference conditional only on truth of the recognized PA axiom.
> Its quotation-adequacy theorem now discharges every code recognized by the
> finite `PeanoMinus` branch at arbitrary positive levels.  The nonstandard
> induction-axiom branch remains incomplete.  Consequently the full requested
> scheme `PA ⊢ Con_n(PA)` for
> every external `n` is **not yet implemented** in either kernel; Lean's
> externally indexed family is complete at `n = 0`.

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

## Phase-one hierarchy measure and the coded bridge

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

This remains the **external, metatheoretic** hierarchy measurement for the
phase-one PA/HF syntax.  Lean's `CodedHierarchy` module independently performs
the corresponding recursion on Foundation's actual Gödel codes in arbitrary
models and proves agreement on every standard quotation.  Rocq's
`CodedSyntax` proves the analogous agreement for its canonical natural-number
codes, but that computation has not yet been internalized for arbitrary
nonstandard PA models.

The Lean foundation library supplies the closely related typed predicate
`LO.FirstOrder.Arithmetic.Hierarchy`.  Its constructors preserve level across
genuinely bounded quantifiers, preserve a block of matching polarity, and
increase the level when polarity alternates.  The intended final domain
predicate on Gödel codes corresponds to

```text
Hierarchy Sigma n phi or Hierarchy Pi n phi.
```

Bounded quantifiers must still be addressed at the final correspondence
boundary: the small phase-one syntax represents only primitive unbounded
quantifiers, while Foundation's typed hierarchy treats genuine bounded
quantifiers as level-preserving abbreviations.  No theorem currently equates
the PA/HF host rank with Foundation's implication-free NNF rank across that
change of syntax.

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

`BoundedPAConsistency.ModelFormulaInduction` specializes the same bridge to
Foundation's formula-code fixed point and exposes all eight syntax cases.  It
allows fixed higher-level invariants to be proved for every internally
well-formed formula code, including nonstandard codes, without host-language
decoding.

The current Rocq/Coq foundation has no corresponding arithmetized syntax and
fixed-point derivation library, so this bridge presently has no Rocq analogue.

### Lean coded-term evaluation

`BoundedPAConsistency.TermEvaluation` evaluates Foundation codes of
arithmetic terms under HFS-coded bound- and free-variable environments.  It
uses Foundation's term recursor, so its value and vector-value graphs are
Sigma-one represented functions in every model of `I Sigma 1`, including on
nonstandard term codes.  The checked equations cover de Bruijn and free
variables, binder extension, argument vectors, and the arithmetic constants,
addition, and multiplication.  This is the term-semantic input to partial
truth; it does not yet evaluate formula codes.

`BoundedPAConsistency.TermEvaluationTransport` proves, by internal structural
induction rather than decoding, that evaluation commutes with coded
free-variable shift and simultaneous bound-variable substitution.  It also
constructs genuine HFS fresh-head and reversed de Bruijn substitution
environments.  The results therefore apply to nonstandard term codes in every
model of `I Sigma 1`.

### Lean coded hierarchy and restricted proof sentence

`BoundedPAConsistency.CodedHierarchy` uses Foundation's formula fixed-point
recursor to compute the pair of `Sigma`- and `Pi`-oriented ranks on actual
formula codes.  Its graph is Sigma-one represented and its
`QuantifierBoundedCode` predicate has a dual Sigma/Pi Delta-one presentation.
The constructor equations, negation swap, and invariance under shift and term
substitution are proved by internal structural induction, so they cover
nonstandard codes in arbitrary models of `I Sigma 1`.  The module also proves
exact agreement with its external rank on standard quoted NNF formulae.

`BoundedPAConsistency.OrientedHierarchy` resolves the minimum-based bound
into separate internal `IsSigmaCode` and `IsPiCode` domains.  It proves the
Boolean and quantifier constructor inversions, polarity exchange under coded
negation, monotonicity, and shift/substitution/free-opening transport needed
by an externally recursive partial-truth family.  These results also range
over arbitrary nonstandard codes and model bounds.

`BoundedPAConsistency.RestrictedDerivation` conjoins that bound with every
node of Foundation's coded derivation fixed point.  Its erasure theorem is an
internal induction over the fixed point, not a decoder argument on standard
naturals.  `BoundedPAConsistency.RestrictedConsistency` packages the result as
a Delta-one restricted-proof predicate, Sigma-one restricted provability,
and a Pi-one sentence `paRestrictedConsistencySentence n` for each external
Lean natural number `n`.  Evaluation of that sentence in every arithmetic
model is proved equivalent to absence of all model-internal restricted proof
codes.  The rank-zero instance of this exact target is now proved in PA;
arbitrary positive external levels remain open.

### Lean rank-zero partial truth

`BoundedPAConsistency.QuantifierFreeTruth` is the base case of partial
satisfaction.  It evaluates nonstandard coded arithmetic atoms and Boolean
combinations using a represented finite HFS certificate, supplies exact
positive and negative equality/order clauses, conjunction/disjunction
clauses, Boolean-valuedness, and complementary truth/falsity predicates on
the Delta-one level-zero domain.  Quantifier constructors are deliberately
totalized to zero and carry no semantic claim.

`BoundedPAConsistency.QuantifierFreeTarski` proves internally that level zero
forces *both* polarity ranks to vanish, a fact not immediate from the
minimum-based definition on nonstandard codes.  It derives exact domain
inversion at conjunction/disjunction, exclusion of quantifier constructors,
and positive/negative Tarski clauses for arithmetic atoms and Boolean
connectives.  `BoundedPAConsistency.QuantifierFreeTransport` proves formula
evaluation invariant under coded free-variable shift and simultaneous term
substitution, and complementary under coded negation, for arbitrary model
elements satisfying the internal syntax predicates.

`BoundedPAConsistency.QuantifierFreeSoundness` then performs internal
fixed-point induction over arbitrary rank-zero restricted derivations.  It
checks the initial, Boolean, weakening, shift, cut, and axiom rules; the
quantifier rules are excluded by the rank-zero domain theorem.  The result is
parameterized by one deliberately explicit theory premise saying that every
internally recognized rank-zero axiom is rank-zero true.  Thus the logical
soundness layer is complete at level zero.

`BoundedPAConsistency.QuantifierFreePAAxioms` discharges that final premise
for the repository's actual Delta-one PA recognizer.  Its finite PA-minus
branch is shown to contain only standard quoted axioms, whose surviving
rank-zero cases evaluate true.  The possibly nonstandard induction branch is
excluded structurally because every recognized induction formula contains a
genuine universal quantifier.  Completeness then turns arbitrary-model
rank-zero consistency into the audited object theorem

```lean
theorem pa_proves_restrictedConsistency_zero :
    Peano ⊢ (paRestrictedConsistencySentence 0 : ArithmeticSentence)
```

### Lean fixed-level partial truth

`BoundedPAConsistency.FixedLevelTruth` defines an externally indexed family
`SigmaTrue n`/`PiTrue n` over arbitrary model elements.  Positive-level truth
uses internally finite HFS certificates rather than host-language recursion
on a formula code, so nonstandard codes are included.  Certificate records
traverse both children of conjunctions, choose one disjunct, store existential
witnesses, and stop at quantifier-free or lower opposite-polarity leaves.

`FixedLevelTruthCertificate` proves certificate enlargement and the positive
conjunction, disjunction, and existential Tarski clauses.
`FixedLevelTruthDefinability` represents `SigmaTrue n` by a `Sigma_(n+1)`
formula and `PiTrue n` by a `Pi_(n+1)` formula.
`FixedLevelTruthTarski` supplies the uniform Sigma clauses, their Pi Boolean
duals, Pi universal truth over every model element, and the two level-changing
universal/existential polarity clauses.  `OrientedHierarchy.rankCode_balanced`
proves internally that the two ranks differ by at most one, so every formula
with minimum rank at most `n` lies in either chosen polarity at level `n+1`.
`FixedLevelTruthCoherence` proves conservativity between adjacent levels and
agreement of Sigma/Pi truth wherever both oriented domains apply, using
model-internal structural induction for nonstandard codes.
`FixedLevelTruthSubstitution` proves free-variable shift and simultaneous
bound-variable substitution transport under nonstandard environments.
`FixedLevelTruthLaws` combines these results into ordinary complement,
Boolean, quantifier, opening, and substitution clauses for the unified
predicate `SigmaTrue (n+1)` on codes bounded by `n`.  Together with
`AbstractSoundness` and `FixedLevelSequentDefinability`, this proves the whole
logical calculus sound at every fixed external level once the recognized PA
axioms are shown true.  `FixedLevelPAMinusAxioms` proves term-quotation and
formula-quotation adequacy for every standard arithmetic formula within the
fixed coded bound, then uses standardness of the finite `PeanoMinus`
recognizer to show that all of its accepted axioms are `SigmaTrue (n+1)`.
Only the recognizer's genuinely nonstandard induction-axiom branch remains
before the final fixed-level Lean consistency theorem can be assembled.

### Rocq natural codes and executable checker

`CodedSyntax.v` gives canonical natural-number codes for the phase-one PA
terms and formulae, total fuelled decoders, round trips and injectivity, coded
renaming and instantiation, and exact agreement of the coded hierarchy rank
with the typed rank.  `CodedProof.v` gives an unindexed mirror of all 17 proof
rules, an executable endpoint checker, canonical proof codes and total
decoding, and exact preservation of `proofOccurrenceRank` when a typed
`ProvTree` is quoted.

The PA wrapper records explicit witnesses for the six fixed axiom schemes and
for induction instances.  Every phase-one restricted PA derivation has an
accepted code, and every accepted code erases to an ordinary PA derivation.
This is still a computation performed by Rocq on standard `nat` values.  The
checker has an extracted computability witness and a representing PA formula
whose correctness theorem is exact in the standard `nat` model.  It has not
been proved correct for nonstandard codes in arbitrary PA models; that
distinction is exactly the remaining internalization boundary.

There is an additional reason this particular representing formula is only a
checkpoint: the generic computability bridge selects, by classical choice,
an arbitrary formula with the right `natModel` extension.  That contract does
not determine its behavior in nonstandard models or provide a PA-provable
graph theorem.

`CanonicalCheckerTrace.v` removes that opacity.  It constructively extracts
the checker to a closed lambda term, compiles that term to a fixed nine-counter
Minsky program, and builds a fully transparent PA formula asserting the
existence of beta-coded initial, transition, final-state, and output traces.
Its arbitrary-raw-model theorem unfolds the outer certificate into the exact
finite list of trace conditions.  `CanonicalCheckerStandardAgreement.v`
uses deterministic machine semantics to prove, on ordinary naturals, that
the concrete machine accepts exactly when `checkRestrictedPAProofCode`
returns true.  The audits show that the compiler and standard-agreement
theorems are closed; only the generic environment extensionality lemma used
by the raw certificate shell assumes functional extensionality.  The missing
step is now mathematical rather than representational: prove in every raw PA
model that an accepting nonstandard trace would yield a sound bounded proof,
and hence cannot end in falsity.

`RawModelCompleteness.v` supplies the other endpoint: a sentence valid under
every valuation in every raw model of the PA axioms has an object-level
`Formula.BProv Formula.Ax_s []` proof.  This theorem is intentionally
conditional on arbitrary-model validity.  Combining it with the standard
checker-formula correctness theorem would be unsound; the missing fixed-level
partial-truth argument is precisely what must establish that validity for
nonstandard model elements.

`CanonicalCheckerRawReduction.v` fixes the hierarchy bound in the transparent
canonical trace formula, universally closes the candidate-certificate input,
and proves exact satisfaction in every raw arithmetic structure.  Combining
that semantics with raw-model completeness and soundness yields an iff: PA
proves this canonical fixed-bound sentence exactly when every raw PA model
rejects every (including nonstandard) accepting trace.  This is a reduction,
not a proof of rejection; its statement deliberately exposes the remaining
nonstandard soundness obligation.

`CanonicalCheckerRawTraceReflection.v` unfolds the finite transition
disjunction into an explicit raw-carrier Minsky step relation.  It proves
exact semantics for increment, decrement, program-counter, and unchanged
register conditions, and beta-decodes a related current/next state at every
model-internal index below the trace length.  Thus every complete canonical
graph witness contains an internally stepwise trace, even when its length is
nonstandard.

`CanonicalCheckerRawTraceCoherence.v` uses beta functionality in a raw PA
model to prove that all descriptions of one trace position agree on the
program counter and every one of the nine live registers.  Consecutive local
steps therefore share the same finite middle state.  From a single complete
graph witness it also reflects the exact initial checker state (including the
fixed bound and certificate inputs), the accepting output entry, and the
final program counter lying outside the compiled program.  PA's
zero-or-successor theorem obtains either the initial state at a zero-length
trace or the endpoint of the single preceding reflected step; beta
functionality then joins the output and program-counter entries into that one
genuine full final state.  This closes the local coherence and boundary
bookkeeping, but deliberately does not perform an external induction across a
possibly nonstandard trace length.  An object-definable invariant and PA
induction are still needed to exclude the accepting endpoint.

`CodedCheckerRawReduction.v` makes this boundary exact.  It proves the chosen
checker assertion is a sentence, unfolds its semantics in every raw PA model,
and shows that its object-level PA provability is equivalent to rejection of
the graph formula at every (including nonstandard) model element.  It does not
assert that rejection; the opaque formula's standard-model specification is
insufficient to prove it.

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
- [x] In Lean, define a Delta-one code-level hierarchy bound over Foundation
  codes and prove exact quotation correctness for its NNF syntax.
- [ ] Internalize the Rocq code-level hierarchy computation in arbitrary PA
  models and complete the cross-syntax/typed-hierarchy correspondence.
- [ ] Prove closure of the code-level bound under every syntactic operation
  used by the proof calculus: negation, shift, bound-variable opening,
  substitution, universal closure, and formation/inversion of principal
  formulae.
- [x] In Lean, prove nonstandard-code negation, shift, substitution, and
  free-variable-opening preservation for the coded hierarchy rank.
- [x] In Lean, split the minimum-based bound into nonstandard-code Sigma- and
  Pi-oriented domains with exact constructor and polarity-switching laws.
- [x] In Lean, define the all-occurrences restricted derivation predicate over
  Foundation's actual Gödel coding and prove it Delta-one, with Sigma-one
  restricted provability and Pi-one restricted consistency.
- [ ] Build the corresponding arbitrary-model restricted derivation predicate
  in Rocq/Coq.
- [ ] Formalize coded environments and term evaluation, including totality and
  substitution lemmas in PA.
- [x] In Lean, construct represented coded term evaluation and the rank-zero
  partial-truth evaluator with atomic and Boolean clauses.
- [x] In Lean, prove internal term shift/substitution transport and the
  structural/Boolean rank-zero Tarski interface on nonstandard codes.
- [x] In Lean, construct externally indexed fixed-level Sigma/Pi satisfaction
  predicates over nonstandard codes and prove hierarchy definability,
  oriented Boolean/quantifier clauses, and polarity changes at quantifier
  heads.
- [x] Complete polarity coherence, negation, and semantic transport for Lean
  fixed-level truth, including nonstandard shift and simultaneous
  substitution environments.
- [x] In Lean, generalize arithmetized fixed-point induction from level-one
  invariants to every externally fixed positive hierarchy level and specialize
  it to models of full PA.
- [ ] Build or port the corresponding coded-derivation induction machinery in
  Rocq/Coq.
- [x] In Rocq/Coq, construct a transparent canonical Minsky-trace formula for
  the executable checker and prove exact standard-natural compiler agreement.
- [ ] Prove the canonical trace checker's bounded-proof soundness in every raw
  PA model, including nonstandard trace lengths and formula/proof codes.
- [x] In Lean, prove soundness of every rank-zero logical inference for
  arbitrary nonstandard restricted-derivation codes, conditional on the exact
  theory-axiom truth premise.
- [x] Extend logical-inference soundness to every fixed external level,
  conditional on the exact internally recognized theory-axiom truth premise.
- [x] In Lean at rank zero, prove truth of all internally recognized PA-minus
  axioms and structurally exclude every induction-axiom code.
- [ ] Generalize PA-minus and internally recognized induction-axiom truth to
  every fixed positive level, including nonstandard instances.
- [x] In Lean, define the fixed-external-`n` object sentence `Con_n(PA)` and
  prove its arbitrary-model representation theorem.
- [x] Define and represent the matching canonical object sentence in
  Rocq/Coq, with exact arbitrary-raw-model semantics and a conditional
  completeness reduction.
- [x] In Lean, construct and audit the checked rank-zero object derivation
  `PA |- Con_0(PA)`.
- [ ] Construct, for each positive external `n`, a checked object-level
  derivation `PA |- Con_n(PA)` in Lean and Coq.
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
  BoundedPAConsistency.CodedHierarchyAudit \
  BoundedPAConsistency.OrientedHierarchyAudit \
  BoundedPAConsistency.QuantifierFreeTruthAudit \
  BoundedPAConsistency.QuantifierFreeTarskiAudit \
  BoundedPAConsistency.QuantifierFreeTransportAudit \
  BoundedPAConsistency.QuantifierFreeSoundnessAudit \
  BoundedPAConsistency.TermEvaluationTransportAudit \
  BoundedPAConsistency.RestrictedDerivationAudit \
  BoundedPAConsistency.RestrictedConsistencyAudit \
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
