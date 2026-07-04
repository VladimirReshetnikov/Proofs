# Lean Proofs

- Created (UTC): 2026-07-04T17:38:16Z
- Repository HEAD: afe87774ab8b2530233ade60ef271aa843b2712b

`src/Lean/` is a repository-local Lake workspace for Lean proofs that are
not owned by one of the more specialized subprojects.

The initial module,
[`LeanProofs/FermatFour.lean`](LeanProofs/FermatFour.lean), records the
`n = 4` special case of Fermat's Last Theorem:

```lean
theorem fermat_four_no_positive_nat_solutions
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 + b ^ 4 ≠ c ^ 4
```

This is the positive-natural-number form of the statement that there are no
positive integers satisfying `a^4 + b^4 = c^4`. The same module also records
the stronger integer descent statement `a^4 + b^4 != c^2`, which is the
classical route to Fermat's `n = 4` case.

[`LeanProofs/FloorSqrtSum.lean`](LeanProofs/FloorSqrtSum.lean) records the
reconstructed blurred formula:

```lean
theorem sum_floor_sqrt_eq (n : Nat) :
    ((∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) : Rat) =
      (Nat.sqrt n : Rat) * (n + 1 : Rat)
        - (Nat.sqrt n : Rat) * ((Nat.sqrt n : Rat) + 1)
          * (2 * (Nat.sqrt n : Rat) + 1) / 6
```

Here `Nat.sqrt k` is Lean's natural-number floor square-root.

## Building

```powershell
cd src/Lean
lake exe cache get
lake build
```
