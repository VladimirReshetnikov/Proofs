# A158415 Proof-Shortening and Build-Time Research

Date: 2026-07-09.

This note records the proof-format experiments performed after formalizing the
known values through `a(15) = 791`. The main conclusion is that generated data
representation matters much more than local tactic golf. The best changes make
Lean check a small soundness kernel plus finite data, rather than repeatedly
elaborating the same proof shape.

Wolfram's `RootReduce` remains a discovery tool only. The generated Lean files
contain exact expressions, rational interval certificates, and finite route or
index tables. No floating-point comparison or arbitrary epsilon enters the
trusted proof.

## Implemented improvements

### 1. Typed route tables instead of expression-witness forests

Sizes 14 and 15 now store one canonical route per value. For example, a
size-15 route is one of:

```lean
inductive Values15Route where
  | sqrt14 (i : Fin 455)
  | oneAdd13 (i : Fin 264)
  | sqrtTwoAdd10 (i : Fin 54)
  | add5_9 (i : Fin 5) (j : Fin 33)
  | add6_8 (i : Fin 8) (j : Fin 20)
  | add7_7 (i j : Fin 13)
```

Its evaluator gives the real value, and a six-case theorem proves that every
route belongs to `recursiveValueSet 15`. This replaces thousands of generated
expression declarations, size proofs, evaluation proofs, and route-equality
proofs.

Observed effects:

| Artifact | Before | After |
|---|---:|---:|
| `A158415FifteenTable.lean` source | about 1.75 MB / 14,829 lines | about 34 KB / 935 lines |
| `A158415FifteenTable.olean` | 31.6 MB | 4.50 MB |
| focused size-15 table build | much larger old certificate | 16-18 s |
| `A158415FourteenTable.lean` source | 59.9 KB / 1,001 lines | 20.9 KB / 583 lines |
| `A158415FourteenTable.olean` | 4.22 MB | 2.67 MB |
| focused size-14 table build | about 49 s before route conversion | 30 s after final route conversion |

This is the largest source and object-size win in the current work.

### 2. Boolean rational interval validation

`IntervalCert.Valid` used to be a tree of propositions over `Real`. Every
generated special comparison separately invoked arithmetic tactics to prove
the same kinds of inequalities. It is now backed by a Boolean `valid` checker
whose arithmetic is entirely in `Rat`:

```lean
def Valid (c : IntervalCert) : Prop := c.valid = true

def separated (left right : IntervalCert) : Bool :=
  left.valid && right.valid && decide (left.upper < right.lower)
```

The generic soundness proof performs the rational-to-real casts once. Each
generated interval module has one finite `native_decide` theorem validating
all adjacent special certificate pairs. Individual order lemmas only select a
pair, connect its exact expression to the table entry, and invoke
`lt_of_separated`.

Observed effects:

| Module | Before | After |
|---|---:|---:|
| size-15 intervals, focused build | about 478 s | about 85 s |
| size-15 intervals `.olean` | 30.83 MB | 10.38 MB |
| size-14 intervals, focused build | about 770 s under the earlier shape | about 139 s |
| size-14 intervals `.olean` | about 33.8 MB | about 22.4 MB |

The timings were collected amid intermittent unrelated Lean builds, so they
are not controlled microbenchmarks. The improvement is nevertheless much
larger than the observed contention.

### 3. Modulo-backed finite indices

Generated range witnesses formerly had both a `Nat` lookup table and a second
large proof that every result was below the target table length. They now use:

```lean
def candidate_index (i : Fin sourceLength) : Fin targetLength :=
  Fin.ofNat targetLength (candidate_indexNat i.1)
```

Every generated index is already in range, so the modulo does not alter its
value. It removes a duplicate `fin_cases ... <;> decide` certificate and makes
the `Fin` bound true by construction.

Before the later route compression, this reduced the size-15 range object
files as follows:

| Module | Before `.olean` | After `.olean` | Focused build after change |
|---|---:|---:|---:|
| `A158415FifteenRangeA` | 10.90 MB | 7.81 MB | 74 s, from about 90 s |
| `A158415FifteenRangeB` | 1.21 MB | 0.97 MB | 19 s |
| `A158415FifteenRangeC` | 8.06 MB | 5.86 MB | 141 s |

### 4. Derive padded range families instead of generating them

Several size-14 range families were redundant. Once `1 + x` is known to occur
for every size-12 value, values from smaller sizes can be padded into size 12.
The generic lemmas now derive lower one-add and two-add families from
`recursiveValueSet_subset_of_le` and
`natCast_add_mem_recursiveValueSet_add_two_mul`.

This removed five generated families:

- `1 + values11`
- `1 + values10`
- `2 + values10`
- `1 + values9`
- `2 + values9`

The size-14 range source fell from about 100 KB / 3,000 lines to 54 KB / 1,825
lines before the later route compression. Its focused build improved from
about 748 s to 624 s, and its `.olean` fell from 27.07 MB to 23.47 MB (31.06 MB
before the modulo-backed-index change).

The same mathematical pattern had already proved useful at size 15. It should
be preferred whenever a larger canonical family subsumes smaller padded
families.

### 5. Direct inherited-order proofs

When adjacent entries are both `1 + values13 i`, the order proof no longer
asks `linarith` to rediscover monotonicity. It uses the inherited theorem
directly:

```lean
exact add_lt_add_right
  (values13_strictMono (by decide : (i : Nat) < j)) 1
```

This reduced the size-15 order build from about 379 s to 351 s and its `.olean`
from 8.62 MB to 7.44 MB. The analogous size-14 change reduced its build from
about 160 s to 133 s and its `.olean` from 4.88 MB to 4.18 MB.

### 6. Route-checked exact and almost-exact unary ranges

The square-root range families are definitionally exact: the first 264
size-14 routes are `sqrt13`, and the first 455 size-15 routes are `sqrt14`.
Enumerating one `rfl` branch per input is unnecessary. The generator now emits
one finite route theorem:

```lean
private theorem sqrt_values13_mem_range_values14_route_spec :
    forall i : Fin 264,
      values14RouteNat (sqrt_values13_mem_range_values14_index i).1 =
        Values14Route.sqrt13 i := by
  native_decide
```

The real-valued range equality then follows by rewriting the route and `rfl`.
The size-14 range built in 506 s with this change, versus 624 s after the
padding-family cleanup, despite concurrent load.

The one-add families are almost exact: 153 of 154 size-14 cases and 263 of 264
size-15 cases are direct `oneAdd` routes. In each family, index zero is the
only algebraic collision. The generator therefore emits a route theorem under
`Not (i = 0)`, retains the original exact proof for index zero, and dispatches
with one `by_cases`. Together, these route checks remove 1,135 repetitive
branches while preserving the two genuine collision proofs.

After both route compressions, `A158415FourteenRange.lean` is about 48 KB /
1,414 lines and its `.olean` is 19.96 MB. `A158415FifteenRangeA.lean` is about
14 KB / 792 lines and its `.olean` is 1.77 MB, down from 7.81 MB after the
modulo-backed-index change. The optimization is deliberately limited to
structurally exact cases; other algebraic collisions still receive explicit
equality certificates.

## Final verification

After merging current `main`, both final targets built successfully:

```text
lake build LeanProofs.A158415Fourteen
lake build LeanProofs.A158415Fifteen
```

The successful post-merge size-15 run rebuilt the table (31 s), intervals
(246 s), range A (246 s), range B (60 s), range C (246 s), order proof (366 s),
and final theorem (27 s). The machine was concurrently running unrelated Lean
builds, so these figures are a verification record rather than controlled
benchmarks. The resulting modules prove `a158415 14 = 455` and
`a158415 15 = 791` with exact certificates.

## Experiments rejected

### Broad `try rfl` sweeps

Replacing explicit branches by
`fin_cases ... <;> try rfl` made `A158415FifteenRangeA` much shorter (roughly
1,508 lines to 790), but slowed its build from about 90 s to 115 s. Lean was
paying to search all goals rather than following generated deterministic
branches. The experiment was reverted.

The typed-route finite check achieves the desired source compression without
that elaboration penalty.

### Splitting the size-14 range into five modules

Parallel module compilation reduced one contended wall-clock run only from
about 748 s to 713 s, while the combined `.olean` footprint grew to roughly
94 MB from 27 MB. The aggregator alone took about 93 s. Repeated imports and
environment serialization outweighed the limited parallelism. The split was
fully reverted.

### Tactic-only strict-order compression

An ultra-short `values15_strictMono` built from broad `all_goals` tactic sweeps
was slow and fragile. Generated branch-local proofs are longer, but give Lean
the intended theorem immediately. The lesson is consistent: source line count
is not a useful objective unless elaboration time and object size are measured
alongside it.

## Further ways to shorten the proofs

The following ideas remain promising, in approximate payoff order.

### 1. A checked collision-certificate language

Most remaining range cost is in algebraic collisions: a generated candidate
has the same value as a canonical route but is not definitionally the same
expression. Introduce a small certificate syntax whose steps are known exact
identities, for example:

- commutativity and associativity of addition;
- route unfolding;
- named radical identities already proved in the development;
- congruence under `sqrt` and addition;
- transitivity through an intermediate canonical expression.

A single sound interpreter would turn certificate data into real equalities.
The generator could then emit compact data rather than hundreds of tactic
scripts. Unlike asking Lean to normalize arbitrary nested radicals, this keeps
the successful current strategy: Wolfram discovers a path, Lean checks each
step.

### 2. Batch the adjacent-order dispatcher

Rational certificate validity is already batched, but the final strict-order
modules still dispatch one branch per adjacent pair. A table indexed by
`Fin (count - 1)` could store either:

- an inherited-monotonicity route, or
- indices into the special interval-pair table.

One theorem over the dispatcher would replace most of the 454/790-way order
case splits. The key is to make dispatch decidable data and keep expression
evaluation lemmas separate, avoiding a broad tactic sweep.

### 3. DAG-shaped interval certificates

`IntervalCert` is tree-shaped, so repeated radical subexpressions duplicate
source and elaboration work. A generated array of certificate nodes could
refer to child nodes by index. Prove soundness by a well-founded node order or
store a topological `Fin` bound in each reference. Reused radicals would then
be validated once.

This is likely the best route to scaling the interval method beyond size 15.

### 4. Benchmark array-backed lookup tables

The route and index maps are currently large `Nat` pattern matches. An
`Array`/`Vector` representation may produce smaller environments and faster
native checks, but it may also add lookup-proof overhead. Benchmark it on the
455-entry route table before changing the generator. The existing pattern
match is simple and already performs well, so this is an empirical question.

### 5. Share canonical padded-family theorems across sizes

The size-14 and size-15 padding arguments have nearly the same shape. A generic
lemma parameterized by a table-range hypothesis could package the arithmetic
once. This is a modest source/readability improvement, not a major build-time
win, but it would keep future size proofs from copying orchestration code.

### 6. Verified algebraic-number certificates

The ambitious endpoint is a Lean-side algebraic-number comparison backend:
minimal polynomials, isolating rational intervals, and exact sign or root
selection proofs. `RootReduce` could emit those certificates, while Lean proves
that each nested radical is the isolated root and compares roots exactly.

This may eventually beat interval trees for deeply nested expressions, but it
is a separate formalization project. The collision language and DAG interval
format are smaller, more immediate steps.

## Recommended next implementation order

1. Prototype the checked collision-certificate interpreter on the size-15
   binary range module, where explicit collision proofs dominate.
2. Replace the adjacent-order branch dispatcher with a typed finite table.
3. Prototype DAG interval certificates and compare source, `.olean`, and build
   time on size 15.
4. Benchmark an array-backed route table before adopting it globally.
5. Consider algebraic-number isolation only after the lighter certificate
   formats reach their limits.

The practical rule from all of these experiments is simple: generate explicit
data for choices, prove its interpreter sound once, and let native finite
computation check the data. Do not ask the elaborator to search for structure
that the generator already knows.
