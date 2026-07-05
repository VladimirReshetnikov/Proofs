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
    (∑ k ∈ Finset.Icc 1 n, Nat.sqrt k : Nat) =
      Nat.sqrt n * (n + 1)
        - Nat.sqrt n * (Nat.sqrt n + 1)
          * (2 * Nat.sqrt n + 1) / 6
```

Here `Nat.sqrt k` is Lean's natural-number floor square-root, and the
formula is stated as a natural-number identity.

[`LeanProofs/RationalFloorOrbit.lean`](LeanProofs/RationalFloorOrbit.lean)
proves that the orbit starting at `0` under
`q ↦ 1 / (1 - q + 2 * floor q)` visits every nonnegative rational exactly
once:

```lean
theorem rationalFloorOrbit_visits_each_nonnegative_rat_exactly_once
    (q : Rat) (hq : 0 ≤ q) :
    ∃ n : Nat, rationalFloorOrbit n = q ∧
      ∀ m : Nat, rationalFloorOrbit m = q → m = n
```

[`LeanProofs/TinyExponentTower.lean`](LeanProofs/TinyExponentTower.lean)
proves the tiny-exponent power-tower floor identity:

```lean
theorem floor_tinyExponentTower_sub :
    ⌊tinyExponentTower⌋ - (10 : Int) ^ (10 ^ 10 : Nat) =
      (2811012357389 : Int)

theorem floor_expanded_tinyExponentTower_sub :
    Int.floor
      ((10 : ℝ) ^
        ((10 : ℝ) ^
          ((10 : ℝ) ^
            ((10 : ℝ) ^
              ((10 : ℝ) ^ (-((10 ^ 10 : Nat) : ℝ))))))) -
      (10 : Int) ^ (10 ^ 10 : Nat) = (2811012357389 : Int)
```

[`LeanProofs/TrigGoldenRatio.lean`](LeanProofs/TrigGoldenRatio.lean) proves
the trigonometric golden-ratio identity from the degree angles in the image:

```lean
theorem sin_deg9_add_sin_deg21_add_sin_deg39 :
    Real.sin (9 * Real.pi / 180) +
        Real.sin (21 * Real.pi / 180) +
        Real.sin (39 * Real.pi / 180) = φ / √2
```

## Building

```powershell
cd src/Lean
lake exe cache get
lake build
```
