# Coding finite lists in Peano arithmetic

This project gives independent Lean 4 and Rocq/Coq proofs that finite lists of
natural numbers can be coded by single natural numbers and that twenty-five
standard list and number-theoretic predicates are definable by genuine
first-order formulae in the language of Peano arithmetic.

The formulae have only the symbols of arithmetic—zero, successor, addition,
multiplication, and equality—together with first-order logical connectives and
quantifiers. Their displayed numeric arguments are free variables, or
**parameters**, of those formulae. No list type, semantic oracle, or additional
list-valued function symbol is added to PA's object language.

## List codes

Both developments use a canonical functional sequence representation with the
same public contract:

- every external finite list of natural numbers has a single-natural-number
  code;
- every valid code decodes to exactly one finite list;
- encoding followed by decoding returns the original list;
- equality of canonical encodings implies equality of lists; and
- malformed natural numbers are separately recognized as invalid; if an
  implementation uses a totalized decoder with a default result, that result
  confers no list meaning without the validity guard.

The concrete encodings are deliberately allowed to differ. Lean specializes
the sequence coding already provided by
`FormalizedFormalLogic/Foundation`: a list is the Ackermann code of the graph
of a function whose domain is an initial segment. Coq uses a self-delimiting
nested polynomial code, with zero for the empty list and a positive paired
node for a head and the strictly smaller code of its tail. The round-trip and
functionality theorems, rather than accidental equality of the two numeric
encodings, are the parity boundary between the ports.

List positions are **zero based** throughout. Thus element zero is the first
element, and asking for an element at an index greater than or equal to the
length is false. This is separate from the explicitly one-based enumeration
of primes introduced below.

## Represented predicates

For the following descriptions, `decode(v) = xs` includes the assertion that
`v` is valid. The result code is written first in constructor-like relations.

1. **Valid code**: `p` decodes to some finite list.
2. **Length**: `v` decodes to `xs` and `length xs = n`.
3. **Element**: `v` decodes to `xs` and the zero-based `k`-th element of `xs`
   is `m`.
4. **Singleton**: `v` decodes to exactly `[m]`.
5. **Concatenation**: `v`, `t`, and `u` decode to `xs`, `ys`, and `zs`, and
   `xs = ys ++ zs`.
6. **Flattening**: `w` decodes to a list of valid list codes; decoding those
   inner codes in order and concatenating their lists gives the list decoded
   by `v`.
7. **Occurrences**: the list decoded by `v` contains exactly `n` occurrences
   of `m`, including multiplicity and regardless of the other elements.
8. **Permutation**: the lists decoded by `v` and `w` are permutations in the
   usual multiplicity-preserving sense.
9. **Contiguous substring**: the list decoded by `w` is `prefix ++ xs ++ suffix`,
   where `xs` is the list decoded by `v`.
10. **Subsequence**: the list decoded by `v` is obtained from the list decoded
    by `w` by deleting zero or more elements without changing the order of the
    retained elements. Adjacency is not required.
11. **No duplicates**: the list decoded by `v` has pairwise distinct elements.
12. **Nondecreasing order**: each element of the list decoded by `v` is at most
    its successor. Valid empty and singleton lists are sorted.
13. **Lexicographic order**: `v` decodes to a list of valid inner list codes,
    and their decoded lists are in nondecreasing lexicographic order. A proper
    prefix comes first, and otherwise the first unequal elements determine the
    order. Numeric code values themselves are never used as the lexicographic
    keys.
14. **All permutations**: `v` decodes to the canonical lexicographically
    sorted list of codes of all distinct permutations of the list decoded by
    `w`.
15. **Sum**: `p` is the left-to-right sum of the entries decoded from `v`;
    the empty list has sum zero.
16. **Product**: `p` is the left-to-right product of the entries decoded from
    `v`; the empty list has product one.
17. **Greatest element**: `m` occurs in the list decoded from `v` and every
    entry is at most `m`.  This is false for the empty list.
18. **Least element**: `m` occurs in the list decoded from `v` and every entry
    is at least `m`.  This is false for the empty list.
19. **Twice the median**: after sorting the nonempty decoded list, `m` is twice
    its central entry at odd length, or the sum of its two central entries at
    even length.
20. **Unique mode**: `m` occurs in the decoded list and its multiplicity is
    strictly greater than the multiplicity of every different entry.
21. **Nth prime**: `p` is the `n`-th prime, with **one-based** indexing.  Thus
    the first prime is `2`, while index zero has no corresponding prime.
22. **Natural power**: `m = a^k`, including the convention `a^0 = 1` and hence
    `0^0 = 1`.
23. **Prime factorization**: `v` decodes to the strictly prime-sorted list of
    two-entry codes `[p, e]` for the positive prime powers in the factorization
    of `m`.  The factorization of one is empty; zero has no factorization.
24. **Base digits**: `v` is the canonical most-significant-digit-first
    expansion of `m` in base `b`.  Bases are at least two, zero is `[0]`, and
    every other expansion has a nonzero leading digit.
25. **Positive divisors**: `v` is the strictly increasing list containing
    every positive divisor of `m` exactly once.  This is false for zero.

The six scalar relations use the result-first parameter order shown above:
`(p, v)` for sum and product and `(m, v)` for the four statistics.  A scalar
result is an arbitrary natural number, not another list code; only `v` is
subject to the validity guard.

The number-theoretic relations likewise put the constructed result first:
`(p, n)` for the one-based `n`-th prime, `(m, a, k)` for powers, `(v, m)` for
factorizations and divisor lists, and `(v, m, b)` for base-`b` digits.

Every predicate is strict about malformed inputs. If any argument that is
supposed to code a list is invalid, the predicate is false. Flattening and the
two predicates about lists of list codes additionally require every inner code
to be valid. In particular, two invalid numbers are not permutations, an
invalid number is not vacuously sorted, and an invalid inner code cannot be
hidden in a flattening witness.

## Aggregate and statistical conventions

Sum and product are certified by sequences of partial results.  Their initial
values, zero and one respectively, make the empty-list conventions part of
the arithmetic definitions rather than exceptional metalevel cases.

The median relation uses a nondecreasing permutation of the input.  At length
`2k+1` its result is twice entry `k`; at length `2k+2` its result is the sum of
entries `k` and `k+1`.  This is exactly twice the conventional median while
remaining a natural number and avoiding division in the PA formula.  Sorted
permutations have the same order statistics, so the witness cannot change the
result.

For the mode, only values that occur in the list can be competitors.  The
candidate must occur and must have a strictly larger count than every
different occurring value.  Thus the relation is false for the empty list
and for every tie at the maximal frequency.

Both formalizations prove the corresponding natural properties: sum and
product exist uniquely for every valid list code; greatest, least, and twice
the median exist for every valid nonempty code and are functional; and a
unique mode, whenever it exists, is functional.  Named checked regressions
record both empty folds, the four empty-list failures, a tied-mode failure,
and odd- and even-length median examples.

## Number-theoretic conventions

The nth-prime formula counts primes strictly below `p` and asserts that this
count plus one is `n`.  This avoids truncated subtraction and makes the
one-based convention, including rejection of index zero, explicit in PA.

Power is witnessed by a multiplication trace of length `k+1`, starting at one.
Prime-factor pairs are themselves ordinary two-element list codes.  Every
exponent is positive, the prime components are strictly increasing, and the
product of the certified powers is exactly the factored number.  These clauses
rule out omissions, duplicate primes, zero exponents, and alternative orders.

A digit expansion uses a Horner trace beginning at zero and repeatedly taking
`accumulator * base + nextDigit`.  Requiring a nonempty list, bounded digits,
and a nonzero leading digit except in `[0]` makes the most-significant-first
representation canonical.  A divisor list is similarly extensional: every
listed value is a positive divisor and every positive divisor occurs; strict
ordering fixes both multiplicity and order.

The checked natural properties make these specifications functional, not just
recognizers for possible witnesses.  Every positive one-based index has a
unique prime, and every prime has a unique one-based index; exponentiation has
a unique result; every nonzero natural has exactly one canonical factorization
code; each number has exactly one canonical base expansion for every base at
least two; and every positive number has exactly one canonical divisor-list
code.  The audit also records the boundary cases named above.

Here and in the preceding aggregate section, these are metatheorems about the
standard natural-number interpretation of the displayed PA formulae.  They do
not claim formal derivations, inside a PA proof calculus, of the universal
closures of every functionality and existence statement; the precise
distinction is spelled out under “What ‘represented by a PA formula’ means”
below.

## The all-permutations convention

The all-permutations predicate has four logically separate requirements:

- **soundness**: every decoded entry of the outer list is a permutation of the
  input list;
- **completeness**: every list value that is a permutation of the input occurs
  among the decoded entries;
- **exactly once**: the decoded outer list has no duplicate list values; and
- **order**: those values are sorted lexicographically.

Completeness is important: merely checking that every listed entry is a
permutation would also accept the empty outer list. It is stated extensionally
over decoded list values, rather than relying on the behavior of a particular
permutation-generating program. If the input contains repeated numbers, two
index rearrangements that produce the same list value count as the same
permutation here. Each distinct resulting list occurs exactly once. Together
with the total lexicographic order, these clauses specify the intended
canonical output independently of an enumeration algorithm. This development
represents that exact relation; a separate existence-and-uniqueness theorem for
the output of every input code is not part of the exported theorem surface.

## What “represented by a PA formula” means

Each public representation theorem exposes an actual arithmetic formula of
the appropriate arity and proves a standard-model equivalence of the form

```text
the formula is true in the standard natural-number model at parameters a
  if and only if
the corresponding guarded relation holds of a.
```

This is semantic definability in the standard model of PA, not an abbreviation
that treats an arbitrary metalevel predicate as an atomic formula. Lean uses
Foundation's arithmetic formula and definability interfaces; the Coq port uses
the PA syntax and `natModel` semantics from the repository's PA/HF
development. The Lean sequence primitives are in fact developed uniformly
over models of `IΣ₁`, and therefore apply to PA models, while the exported
external encode/decode bijection is stated over the standard natural numbers.

The headline result should not be confused with the stronger
proof-theoretic assertion that PA proves every true closed numeral instance
and proves the negation of every false instance. Such **strong
representability** requires separate syntactic derivations or a general
representability theorem. The modules here advertise standard-model formula
correctness; audit output records the precise assumptions of the exported
results.

## Formalization map

- Lean's `PAListCoding.Basic` supplies encoding, decoding, validity, and the
  round-trip/functionality results. `PAListCoding.Predicates` defines the
  guarded relations, constructs their arithmetic formulae through
  Foundation's definability infrastructure, and proves the formula-evaluation
  correctness theorems. `PAListCoding.Standard` connects the original
  relations to ordinary Lean lists, while `PAListCoding.Aggregates` proves the
  six scalar bridges, determinacy and existence properties, and edge cases.
  `PAListCoding.NumberTheory` defines the five number-theoretic relations and
  their formulae, then proves their standard interpretations and canonicality
  properties. `PAListCoding.lean` is the public facade, and
  `PAListCoding.Audit` checks the theorem surface and its assumptions.
- Coq's `ListCode.v` supplies the independent executable nested code and the
  metalevel meanings of the original twenty predicates. `Representability.v`
  provides compositional representation machinery over the repository's PA
  formula syntax. `ListFormulas.v` constructs the actual PA formulae and
  proves their standard-model equivalences. `NumberTheory.v` supplies the
  number-theoretic semantics and canonicality proofs, while
  `NumberTheoryFormulas.v` constructs and verifies the five additional PA
  formulae. The isolated `NumberTheoryFactorization.v` module uses MathComp's
  unbounded-primes theorem and verified fundamental theorem of arithmetic to
  provide positive-index nth-prime totality and canonical prime-factorization
  existence and uniqueness. `Audit.v` checks the complete public surface and
  prints its assumptions.

The Lean development depends on the vendored
`lib/FormalizedFormalLogic-Foundation` project and its pinned mathlib version.
The Coq formula layer depends on `Logic/Interpretability/PAHF/Coq`; its coding
and finite-list reasoning use only the Rocq standard library.  The isolated
nth-prime totality and prime-factorization canonicality bridge additionally
requires `rocq-mathcomp-boot` version `2.5.0`; the PA formulae and their
correctness theorems do not depend on MathComp.

With the repository's Rocq switch active, that additional package can be
installed reproducibly with `opam install rocq-mathcomp-boot.2.5.0`.

## Checking

From the repository root, build the complete Lean project and run its audit:

```powershell
lake --dir Logic/PeanoArithmetic/ListCoding/Lean build
lake --dir Logic/PeanoArithmetic/ListCoding/Lean env lean `
  PAListCoding/Audit.lean
```

The root Rocq project records the authoritative dependency order and logical
paths for the Coq port. Build and kernel-check the complete registered
workspace with:

```powershell
rocq makefile -f _CoqProject -o Makefile.coq
make -f Makefile.coq
```

For a focused Coq audit, first build the PAHF dependency and the preceding
ListCoding modules, then run:

```powershell
rocq compile -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  Logic/PeanoArithmetic/ListCoding/Coq/Audit.v
rocqchk -silent -Q Logic/FirstOrder/Coq FirstOrder `
  -Q Logic/Interpretability/PAHF/Coq PAHF `
  -Q Logic/PeanoArithmetic/ListCoding/Coq PAListCoding `
  PAListCoding.ListCode PAListCoding.Representability PAListCoding.ListFormulas `
  PAListCoding.NumberTheory PAListCoding.NumberTheoryFormulas `
  PAListCoding.NumberTheoryFactorization PAListCoding.Audit
```

The audit modules check all twenty-five formula/correctness results together with
the ordinary-list bridges, aggregate functionality and existence properties,
edge cases, and the coding existence, decoding functionality, round-trip, and
injectivity theorems. No generated enumeration is part of the trusted theorem
boundary:
the all-permutations result is checked against its soundness, completeness,
exact-once, and lexicographic specification.
