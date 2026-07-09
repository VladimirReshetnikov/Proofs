# A158415 Proof-Shortening Research

Date: 2026-07-09.

This note records concrete ways to shorten the current A158415 Lean
formalization after the size-15 proof work.  The main lesson is that the
largest remaining savings are in generated certificate shape, not in local
tactic golf.

## Current proof surface

Line counts and rough declaration counts after the size-15 work:

| File | Lines | Defs | Theorems | Macros | `next` branches |
|---|---:|---:|---:|---:|---:|
| `LeanProofs/A158415.lean` | 1973 | 13 | 106 | 0 | 0 |
| `LeanProofs/A158415Ten.lean` | 778 | 2 | 26 | 0 | 0 |
| `LeanProofs/A158415Eleven.lean` | 1074 | 6 | 62 | 1 | 0 |
| `LeanProofs/A158415Twelve.lean` | 2778 | 2 | 51 | 1 | 0 |
| `LeanProofs/A158415Thirteen.lean` | 6892 | 2 | 76 | 1 | 0 |
| `LeanProofs/A158415Fourteen.lean` | 13875 | 2 | 121 | 0 | 1829 |
| `LeanProofs/A158415Fifteen.lean` | 196 | 0 | 9 | 0 | 0 |
| `LeanProofs/A158415FifteenIntervals.lean` | 6161 | 352 | 175 | 0 | 0 |
| `LeanProofs/A158415FifteenOrder.lean` | 841 | 0 | 4 | 2 | 790 |
| `LeanProofs/A158415FifteenRangeA.lean` | 2945 | 4 | 4 | 0 | 719 |
| `LeanProofs/A158415FifteenRangeB.lean` | 311 | 2 | 2 | 0 | 54 |
| `LeanProofs/A158415FifteenRangeC.lean` | 2916 | 6 | 6 | 0 | 494 |
| `LeanProofs/A158415FifteenTable.lean` | 19070 | 70 | 98 | 0 | 1895 |

Range proof branch counts:

| File | Branches | Exact `rfl` branches | Nontrivial branches |
|---|---:|---:|---:|
| `A158415FifteenRangeA.lean` | 719 | 718 | 1 |
| `A158415FifteenRangeB.lean` | 54 | 33 | 21 |
| `A158415FifteenRangeC.lean` | 494 | 40 | 454 |

## Highest-payoff opportunities

### 1. Remove the route table layer from expression witnesses

The generated size-15 table currently carries parallel data:

- `values15Nat`
- `values15RouteNat`
- `values15Route`
- `values15ExprNat`
- `values15Expr`
- per-index route equality proofs
- per-index expression evaluation via route equality

The generator emits this in
`Oeis/A158415/computations/wolfram/generate-a158415-data.wl`, in
`printLeanExprWitnesses`.  The route layer was useful while developing the
certificate format, but the final membership theorem only needs:

1. an expression witness,
2. its size proof,
3. an exact proof that evaluating the expression equals the target value.

So the generator can emit direct `valuesmExpr_eval` proofs and stop emitting
`valuesmRouteNat`, `valuesmRoute`, and `valuesmRoute_eq_values` for production
tables.  This should save thousands of generated lines in
`A158415FifteenTable.lean`; it also removes one moving part from every future
`m`.

Risk: low to medium.  This is generator surgery rather than mathematical proof
work.  The direct proofs should still be mechanically checkable by the same
table tactics.

### 2. Compress exact range branches with `all_goals try rfl`

The range modules are mostly generated case splits.  `RangeA` is especially
ripe: 718 of 719 branches are exact `rfl` cases.  The generator can produce:

```lean
  all_goals try rfl
```

after the `fin_cases` split, then emit only the nontrivial collision branches.

This should almost delete `A158415FifteenRangeA.lean` and noticeably shrink
`RangeB`.  `RangeC` has many real collisions, so the win there is smaller.

Risk: low for `RangeA`, medium elsewhere.  A similar ultra-compact experiment
on the order proof was too costly for elaboration, but the range proof's exact
`rfl` branches are simpler.  Build time still needs to be measured.

### 3. Factor interval order theorem boilerplate

`A158415FifteenIntervals.lean` already has `IntervalCert`, but every special
ordering theorem still repeats the same shape:

1. show left certificate validity,
2. show right certificate validity,
3. rewrite certificate evaluations,
4. finish from a rational endpoint gap.

A generic lemma could capture the pattern:

```lean
theorem IntervalCert.lt_of_gap
    (left right : IntervalCert)
    (hleft : left.Valid)
    (hright : right.Valid)
    (hleftEval : x = left.expr.eval)
    (hrightEval : y = right.expr.eval)
    (hgap : (left.upper : Real) < (right.lower : Real)) :
    x < y := ...
```

The generated special theorems would then be reduced to certificate validity,
two evaluation rewrites, and `norm_num` on the gap.

Risk: low.  The proof principle is already used repeatedly; this just names it.
The payoff is moderate for line count and good for readability.

### 4. Port size 14 and older special-order proofs to interval certificates

`A158415Fourteen.lean` is still 13875 lines and uses older hand-expanded
rational upper/lower proofs.  Size 15 showed that named interval certificates
are a better surface: the order proof is split, more inspectable, and easier
to regenerate.

The likely next cleanup is to split size 14 into table/order/range modules and
reuse the interval-certificate generator.  The same approach may simplify size
13 and size 12, though the payoff drops quickly with `m`.

Risk: medium.  This is not conceptually hard, but it touches older generated
artifacts and may expose compile-time regressions.

### 5. Share interval subcertificates

`IntervalCert` is currently tree-shaped.  Repeated nested radicals therefore
duplicate source text and elaboration work.  A DAG-style certificate table
would name shared subcertificates once and refer to them by index.

Potential shape:

- a generated array/list of certificate nodes,
- a validity theorem per node,
- an evaluation theorem per node,
- order certificates that point at node indices.

Risk: medium to high.  This is a bigger certificate-format change, but it is
one of the few options that could reduce both source size and elaboration work
substantially for later `n`.

### 6. Long-term: algebraic-number certificates

Wolfram/Tungsten `RootReduce` is useful for discovery, but Lean cannot trust
it directly.  A more ambitious direction is to emit algebraic-number
certificates:

- a minimal polynomial,
- an isolating interval,
- a proof that the nested radical expression is the isolated root,
- exact comparison via interval separation or polynomial sign data.

This could eventually replace large nested radical interval trees.  It is
probably not the next engineering step; it is a separate formalization project.

## Less promising tactic-only compression

An ultra-compact `values15_strictMono` proof using broad `all_goals` tactic
sweeps was much shorter on paper, but it was too slow or fragile in practice.
The current generated macro-per-branch proof is less elegant, but it builds.
Future proof shortening should therefore measure elaboration time, not just
source lines.

## Suggested next implementation order

1. Implement `all_goals try rfl` compression for generated range modules and
   rebuild `LeanProofs.A158415Fifteen`.
2. Remove the route table layer from `printLeanExprWitnesses`; regenerate
   `A158415FifteenTable.lean`; rebuild.
3. Add `IntervalCert.lt_of_gap`; regenerate or manually shorten the special
   interval-order theorems.
4. Port size 14 to the size-15 split/certificate style.

The first two items are likely to produce the most visible line-count reduction
with the least mathematical risk.
