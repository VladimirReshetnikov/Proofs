import LeanProofs.PowTower
import LeanProofs.SparseBinary
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.NAry

/-!
# Initial values of OEIS A002845

OEIS A002845 counts the distinct values taken by `2^2^...^2`, with `n`
copies of `2` and all binary parenthesizations allowed.

The primary definition below is the shared lexical one from `PowTower.Expr`:
the single atom is interpreted as the literal `2`, and the binary node is
interpreted as natural-number exponentiation.  The sparse-binary logarithm
representation (`LeanProofs.SparseBinary`) is a computation-facing view, with
Lean proofs connecting it back to the shared lexical definition.  Large values
are computed through the shared proved hash-set fast table from
`PowTower.Expr`, and the sparse combine operation itself is the verified total
`Sparse.shift`, Lean-proved on canonical inputs to compute the canonical
representation of `eval a * 2 ^ eval b`.  No `implemented_by` substitution is
involved anywhere in this module: the executable path *is* the proved path,
and the only remaining trust in the value certificates is `native_decide`
itself.
-/

set_option maxRecDepth 100000

namespace LeanProofs

namespace A002845

/-- A002845 uses the shared one-token lexical syntax directly. -/
abbrev PowExpr := PowTower.Expr

namespace PowExpr

open PowTower.Expr

/-- Legacy spelling for the shared lexical atom, kept for computation-facing code. -/
abbrev two : PowExpr := PowTower.Expr.atom

/-- Legacy spelling for the shared lexical binary node, kept for computation-facing code. -/
abbrev pow : PowExpr -> PowExpr -> PowExpr := PowTower.Expr.pow

/-- Compatibility name: A002845 syntax is now the shared one-token lexical syntax. -/
abbrev toSharedLex (e : PowExpr) : PowTower.Expr := e

/-- Compatibility name: A002845 syntax is now the shared one-token lexical syntax. -/
abbrev ofSharedLex (e : PowTower.Expr) : PowExpr := e

theorem toSharedLex_ofSharedLex (e : PowTower.Expr) :
    toSharedLex (ofSharedLex e) = e := by
  rfl

theorem ofSharedLex_toSharedLex (e : PowExpr) :
    ofSharedLex (toSharedLex e) = e := by
  rfl

/-- Evaluate a parenthesized power expression using natural-number exponentiation. -/
abbrev eval : PowExpr -> Nat :=
  PowTower.Expr.eval 2 (fun a b : Nat => a ^ b)

/-- Shared lexical interpretation for A002845: atom is `2`, node is `Nat.pow`. -/
abbrev sharedEval : PowTower.Expr -> Nat :=
  PowTower.Expr.eval 2 (fun a b : Nat => a ^ b)

/-- The existing A002845 syntax evaluates the same way as the shared lexical syntax. -/
theorem eval_eq_sharedEval_toSharedLex (e : PowExpr) :
    eval e = sharedEval (toSharedLex e) := by
  rfl

/--
The shared canonical lexical value set for A002845.
-/
def canonicalValueSet (n : Nat) : Set Nat :=
  PowTower.Expr.valueSet 2 (fun a b : Nat => a ^ b) n

/-- The number of literal `2` leaves in a power expression. -/
def size : PowExpr -> Nat :=
  PowTower.Expr.size

/-- All legal binary parenthesizations with exactly `n` copies of `2`. -/
def parenthesizations : Nat -> List PowExpr :=
  PowTower.Expr.parenthesizations

/-- Compatibility theorem: the A002845 spelling is the shared lexical parenthesization. -/
theorem toSharedLex_mem_parenthesizations {n : Nat} {e : PowExpr}
    (he : e ∈ parenthesizations n) : toSharedLex e ∈ PowTower.Expr.parenthesizations n := by
  exact he

/-- Compatibility theorem: the shared lexical parenthesization is the A002845 spelling. -/
theorem ofSharedLex_mem_parenthesizations {n : Nat} {e : PowTower.Expr}
    (he : e ∈ PowTower.Expr.parenthesizations n) : ofSharedLex e ∈ parenthesizations n := by
  exact he

/-- Compatibility value set computed through the A002845 literal-`2` spelling. -/
def valueSet (n : Nat) : Set Nat :=
  {v | ∃ e ∈ parenthesizations n, eval e = v}

/-- The A002845 compatibility value set is the shared generic evaluator set. -/
theorem valueSet_eq_evalSet (n : Nat) :
    valueSet n = PowTower.Expr.evalSet eval n := by
  rfl

/-- The A002845 compatibility value set is the shared canonical lexical value set. -/
theorem valueSet_eq_canonicalValueSet (n : Nat) :
    valueSet n = canonicalValueSet n := by
  rw [valueSet_eq_evalSet, canonicalValueSet,
    PowTower.Expr.valueSet_eq_evalSet 2 (fun a b : Nat => a ^ b)]

/--
OEIS A002845, defined canonically as the cardinality of the shared lexical
natural-number exponentiation value set.
-/
noncomputable def a002845 (n : Nat) : Nat :=
  PowTower.Expr.valueCard 2 (fun a b : Nat => a ^ b) n

/-- A002845 can equivalently be read from the shared canonical lexical syntax. -/
theorem a002845_eq_canonicalValueSet_ncard (n : Nat) :
    a002845 n = (canonicalValueSet n).ncard := by
  rfl

/--
The shared recursive value-set cardinality computes the same number as the
canonical lexical definition.
-/
theorem a002845_eq_recursiveValueSet_ncard (n : Nat) :
    a002845 n =
      (PowTower.Expr.recursiveValueSet 2 (fun a b : Nat => a ^ b) n).ncard := by
  exact PowTower.Expr.valueCard_eq_recursiveValueSet_ncard 2 (fun a b : Nat => a ^ b) n

/-- The exact base-two logarithm of a semantic power expression. -/
def logEval : PowExpr → Nat
  | .atom => 1
  | .pow a b => logEval a * 2 ^ logEval b

/-- Exact-logarithm combine operation induced by `2^a ^ 2^b = 2^(a * 2^b)`. -/
def logCombine (a b : Nat) : Nat :=
  a * 2 ^ b

theorem logEval_eq_sharedEval (e : PowExpr) :
    logEval e = PowTower.Expr.eval 1 logCombine e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [logEval, PowTower.Expr.eval, logCombine, iha, ihb]

/-- Every semantic value is `2` raised to its exact logarithm. -/
theorem eval_eq_two_pow_logEval (e : PowExpr) :
    eval e = 2 ^ logEval e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      change eval a ^ eval b = 2 ^ (logEval a * 2 ^ logEval b)
      rw [iha, ihb, pow_mul]

/-- The canonical exact-logarithm value set corresponding to `valueSet`. -/
def logValueSet (n : Nat) : Set Nat :=
  PowTower.Expr.evalSet logEval n

/-- Cardinality of the exact-logarithm value set. -/
noncomputable def a002845LogCard (n : Nat) : Nat :=
  (logValueSet n).ncard

/-- Semantic values are exactly `2^m` for semantic logarithms `m`. -/
theorem valueSet_eq_pow2_image_logValueSet (n : Nat) :
    valueSet n = (fun m : Nat => 2 ^ m) '' logValueSet n := by
  rw [valueSet_eq_evalSet, logValueSet]
  exact PowTower.Expr.evalSet_eq_image_evalSet_of_eval_eq
    eval logEval (fun m : Nat => 2 ^ m) eval_eq_two_pow_logEval n

/--
The canonical semantic count equals the count of exact logarithms.  This is
the first proof boundary: switching from values to logarithms is justified by
injectivity of `m ↦ 2^m`.
-/
theorem a002845_eq_logCard (n : Nat) : a002845 n = a002845LogCard n := by
  rw [a002845, a002845LogCard, logValueSet]
  exact PowTower.Expr.valueCard_eq_evalSet_ncard_of_eval_eq_of_injOn
    2 (fun a b : Nat => a ^ b) logEval (fun m : Nat => 2 ^ m)
    eval_eq_two_pow_logEval n
    ((Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat))).injOn)

/-- Direct finite computation of the canonical logarithm set. -/
def directLogFinset (n : Nat) : Finset Nat :=
  PowTower.Expr.evalFinset logEval n

/-- Direct finite computation of the canonical logarithm count. -/
def directLogCard (n : Nat) : Nat :=
  (directLogFinset n).card

theorem logValueSet_eq_directLogFinset (n : Nat) :
    logValueSet n = (directLogFinset n : Set Nat) := by
  exact PowTower.Expr.evalSet_eq_evalFinset logEval n

theorem a002845LogCard_eq_directLogCard (n : Nat) :
    a002845LogCard n = directLogCard n := by
  rw [a002845LogCard, directLogCard, logValueSet_eq_directLogFinset]
  exact Set.ncard_coe_finset (directLogFinset n)

theorem directLogFinset_eq_recursiveValueFinset (n : Nat) :
    directLogFinset n = PowTower.Expr.recursiveValueFinset 1 logCombine n := by
  rw [directLogFinset]
  exact PowTower.Expr.evalFinset_eq_recursiveValueFinset_of_eval_eq
    logEval 1 logCombine logEval_eq_sharedEval n

/--
The canonical semantic definition agrees with the direct logarithm-list
computation.  This path is practical for the small initial values whose exact
natural logarithms are still modest.
-/
theorem a002845_eq_directLogCard (n : Nat) : a002845 n = directLogCard n := by
  rw [a002845_eq_logCard, a002845LogCard_eq_directLogCard]

end PowExpr

export PowExpr (a002845 a002845_eq_recursiveValueSet_ncard)

/-- OEIS A002845 has value `1` at `n = 1`. -/
theorem a002845_one : a002845 1 = 1 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/-- OEIS A002845 has value `1` at `n = 2`. -/
theorem a002845_two : a002845 2 = 1 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/-- OEIS A002845 has value `1` at `n = 3`. -/
theorem a002845_three : a002845 3 = 1 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/-- OEIS A002845 has value `2` at `n = 4`. -/
theorem a002845_four : a002845 4 = 2 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/-- OEIS A002845 has value `4` at `n = 5`. -/
theorem a002845_five : a002845 5 = 4 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/-- OEIS A002845 has value `8` at `n = 6`. -/
theorem a002845_six : a002845 6 = 8 := by
  rw [PowExpr.a002845_eq_directLogCard]
  native_decide

/--
The exact logarithm-combine operation:
`log₂ ((2^a)^(2^b)) = a * 2^b`, implemented by the verified total sparse
shift from `LeanProofs.SparseBinary`.
-/
def combineLog (a b : Sparse) : Sparse :=
  Sparse.shift a b

/--
The logarithm-combine operation used by every A002845 computation.  It *is*
the executable `combineLog`; on canonical inputs it is Lean-proved below to
compute the canonical sparse representation of `eval a * 2 ^ eval b`, so no
`implemented_by` substitution is involved anywhere in this module.
-/
def certifiedCombineLog (a b : Sparse) : Sparse :=
  combineLog a b

open Sparse in
theorem certifiedCombineLog_canonical {a b : Sparse}
    (ha : Canonical a) (hb : Canonical b) :
    Sparse.Canonical (certifiedCombineLog a b) :=
  (Sparse.shift_spec ha hb).1

open Sparse in
theorem certifiedCombineLog_eq_ofNat {a b : Sparse}
    (ha : Canonical a) (hb : Canonical b) :
    certifiedCombineLog a b = Sparse.ofNat (Sparse.eval a * 2 ^ Sparse.eval b) :=
  Sparse.shift_eq_ofNat ha hb

open Sparse in
theorem eval_certifiedCombineLog {a b : Sparse}
    (ha : Canonical a) (hb : Canonical b) :
    Sparse.eval (certifiedCombineLog a b) = Sparse.eval a * 2 ^ Sparse.eval b :=
  (Sparse.shift_spec ha hb).2


/-- Exact sparse logarithm of a canonical expression tree. -/
def sparseLogEval : PowExpr → Sparse
  | .atom => Sparse.ofNat 1
  | .pow a b => certifiedCombineLog (sparseLogEval a) (sparseLogEval b)

/-- Every computed sparse logarithm is canonical. -/
theorem canonical_sparseLogEval (e : PowExpr) :
    Sparse.Canonical (sparseLogEval e) := by
  induction e with
  | atom =>
      exact Sparse.canonical_ofNat 1
  | pow a b iha ihb =>
      exact certifiedCombineLog_canonical iha ihb

theorem sparseLogEval_eq_ofNat_logEval (e : PowExpr) :
    sparseLogEval e = Sparse.ofNat (PowExpr.logEval e) := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      rw [show sparseLogEval (.pow a b) =
            certifiedCombineLog (sparseLogEval a) (sparseLogEval b) from rfl,
        certifiedCombineLog_eq_ofNat (canonical_sparseLogEval a)
          (canonical_sparseLogEval b), iha, ihb,
        Sparse.eval_ofNat, Sparse.eval_ofNat]
      rfl

theorem sparseLogEval_eq_sharedEval (e : PowExpr) :
    sparseLogEval e = PowTower.Expr.eval (Sparse.ofNat 1) certifiedCombineLog e := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [sparseLogEval, PowTower.Expr.eval, iha, ihb]

/--
The finite sparse set obtained by evaluating every canonical expression tree.
The proof-facing definition is intentionally direct; `certifiedCombineLog`
supplies the efficient native implementation of each sparse logarithm combine.
-/
def certifiedSparseLogFinset (n : Nat) : Finset Sparse :=
  PowTower.Expr.evalFinset sparseLogEval n

theorem certifiedSparseLogFinset_eq_sharedSparseLogLevel (n : Nat) :
    certifiedSparseLogFinset n =
      PowTower.Expr.recursiveValueFinset (Sparse.ofNat 1) certifiedCombineLog n := by
  rw [certifiedSparseLogFinset]
  exact PowTower.Expr.evalFinset_eq_recursiveValueFinset_of_eval_eq
    sparseLogEval (Sparse.ofNat 1) certifiedCombineLog sparseLogEval_eq_sharedEval n

/-- Cardinality of the certified sparse-logarithm set. -/
def certifiedSparseCard (n : Nat) : Nat :=
  (certifiedSparseLogFinset n).card

theorem coe_certifiedSparseLogFinset (n : Nat) :
    (certifiedSparseLogFinset n : Set Sparse) =
      Sparse.ofNat '' PowExpr.logValueSet n := by
  ext s
  simp [certifiedSparseLogFinset, PowExpr.logValueSet, PowTower.Expr.evalSet,
    PowTower.Expr.evalFinset, sparseLogEval_eq_ofNat_logEval]

/--
Certified sparse expression evaluation computes exactly the canonical semantic
A002845 count.
-/
theorem a002845_eq_certifiedSparseCard (n : Nat) : a002845 n = certifiedSparseCard n := by
  rw [PowExpr.a002845_eq_logCard, PowExpr.a002845LogCard, certifiedSparseCard]
  rw [← Set.ncard_coe_finset (certifiedSparseLogFinset n)]
  rw [coe_certifiedSparseLogFinset]
  exact (Set.InjOn.ncard_image Sparse.ofNat_injective.injOn).symm

/--
Certified dynamic-programming level of exact sparse logarithms: the shared
finite split recurrence for the same canonical lexical syntax, with atom
interpreted as the sparse logarithm `ofNat 1` and power interpreted as
`certifiedCombineLog`.  Unlike `certifiedSparseLogFinset`, this constructs the
semantic set by expression size, reusing smaller certified levels instead of
enumerating all Catalan many expression trees.
-/
def certifiedLevel (n : Nat) : Finset Sparse :=
  PowTower.Expr.recursiveValueFinset (Sparse.ofNat 1) certifiedCombineLog n

/-- Cardinality of the certified dynamic-programming sparse-logarithm level. -/
def certifiedLevelCard (n : Nat) : Nat :=
  (certifiedLevel n).card

theorem coe_certifiedLevel (n : Nat) :
    (certifiedLevel n : Set Sparse) =
      Sparse.ofNat '' PowExpr.logValueSet n := by
  rw [certifiedLevel, ← certifiedSparseLogFinset_eq_sharedSparseLogLevel]
  exact coe_certifiedSparseLogFinset n

/--
The certified dynamic-programming sparse-logarithm levels compute exactly the
canonical semantic A002845 count.
-/
theorem a002845_eq_certifiedLevelCard (n : Nat) : a002845 n = certifiedLevelCard n := by
  rw [PowExpr.a002845_eq_logCard, PowExpr.a002845LogCard, certifiedLevelCard]
  rw [← Set.ncard_coe_finset (certifiedLevel n)]
  rw [coe_certifiedLevel]
  exact (Set.InjOn.ncard_image Sparse.ofNat_injective.injOn).symm

/--
The A002845 sparse-log recurrence is an instance of the shared
`PowTower.Expr` finite recurrence, with atom `1` and combine operation
`a * 2^b` represented sparsely.
-/
theorem certifiedLevel_eq_sharedSparseLogLevel (n : Nat) :
    certifiedLevel n =
      PowTower.Expr.recursiveValueFinset (Sparse.ofNat 1) certifiedCombineLog n := rfl

theorem certifiedSparseLogFinset_eq_certifiedLevel (n : Nat) :
    certifiedSparseLogFinset n = certifiedLevel n := by
  rw [certifiedSparseLogFinset_eq_sharedSparseLogLevel,
    certifiedLevel_eq_sharedSparseLogLevel]

theorem certifiedSparseCard_eq_certifiedLevelCard (n : Nat) :
    certifiedSparseCard n = certifiedLevelCard n := by
  rw [certifiedSparseCard, certifiedLevelCard, certifiedSparseLogFinset_eq_certifiedLevel]

/-- Shared memoized sparse-log count corresponding to A002845. -/
def sharedSparseLogCountMemo (n : Nat) : Nat :=
  (PowTower.Expr.recursiveValueFinsetMemo (Sparse.ofNat 1) certifiedCombineLog n).card

/-- Shared memoized sparse-log counts for sizes `1, ..., n`. -/
def sharedSparseLogCountsMemoThrough (n : Nat) : List Nat :=
  PowTower.Expr.recursiveValueCountsMemoThrough (Sparse.ofNat 1) certifiedCombineLog n

theorem sharedSparseLogCountMemo_eq_sharedSparseLogLevelCard (n : Nat) :
    sharedSparseLogCountMemo n =
      (PowTower.Expr.recursiveValueFinset (Sparse.ofNat 1) certifiedCombineLog n).card := by
  rw [sharedSparseLogCountMemo, PowTower.Expr.recursiveValueFinsetMemo_eq]

theorem certifiedLevelCard_eq_sharedSparseLogCountsMemoThrough_getD {N n : Nat}
    (hpos : 0 < n) (hN : n ≤ N) :
    certifiedLevelCard n = (sharedSparseLogCountsMemoThrough N).getD (n - 1) 0 := by
  rw [certifiedLevelCard, certifiedLevel_eq_sharedSparseLogLevel, sharedSparseLogCountsMemoThrough]
  exact PowTower.Expr.recursiveValueFinset_card_eq_countsMemoThrough_getD
    (atomValue := Sparse.ofNat 1) (powValue := certifiedCombineLog) hpos hN

theorem a002845_eq_sharedSparseLogCountMemo (n : Nat) :
    a002845 n = sharedSparseLogCountMemo n := by
  rw [a002845_eq_certifiedLevelCard, sharedSparseLogCountMemo, certifiedLevelCard]
  rw [PowTower.Expr.recursiveValueFinsetMemo_eq]
  rw [← certifiedLevel_eq_sharedSparseLogLevel]

theorem sharedSparseLogCountMemo_eq_countsMemoThrough_getD {N n : Nat}
    (hpos : 0 < n) (hN : n ≤ N) :
    sharedSparseLogCountMemo n =
      (sharedSparseLogCountsMemoThrough N).getD (n - 1) 0 := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero _ hpos).elim
  | succ i =>
      have hi : i < N := Nat.succ_le_iff.mp hN
      unfold sharedSparseLogCountMemo sharedSparseLogCountsMemoThrough
      simpa using
        (PowTower.Expr.recursiveValueCountsMemoThrough_getD
          (atomValue := Sparse.ofNat 1) (powValue := certifiedCombineLog)
          (N := N) (i := i) hi).symm

theorem a002845_eq_of_sharedSparseLogCountsMemoThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (sharedSparseLogCountsMemoThrough N).getD (n - 1) 0 = value) :
    a002845 n = value := by
  calc
    a002845 n = sharedSparseLogCountMemo n := a002845_eq_sharedSparseLogCountMemo n
    _ = (sharedSparseLogCountsMemoThrough N).getD (n - 1) 0 :=
      sharedSparseLogCountMemo_eq_countsMemoThrough_getD hpos hN
    _ = value := hcount

/-- OEIS A002845 has value `17` at `n = 7`. -/
theorem a002845_seven : a002845 7 = 17 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/-- OEIS A002845 has value `36` at `n = 8`. -/
theorem a002845_eight : a002845 8 = 36 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/-- OEIS A002845 has value `78` at `n = 9`. -/
theorem a002845_nine : a002845 9 = 78 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/-- OEIS A002845 has value `171` at `n = 10`. -/
theorem a002845_ten : a002845 10 = 171 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/-- OEIS A002845 has value `379` at `n = 11`. -/
theorem a002845_eleven : a002845 11 = 379 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/-- OEIS A002845 has value `851` at `n = 12`. -/
theorem a002845_twelve : a002845 12 = 851 := by
  rw [a002845_eq_certifiedSparseCard]
  native_decide

/--
Certified counts for sizes `1, ..., n`, computed from one shared hash-set fast
table.  Every fast row is proved to enumerate exactly the shared finite
recurrence, so no unproved executable backend is involved: the only
execution-level substitution left is `certifiedCombineLog`'s native
implementation by `combineLog`.
-/
def certifiedLevelCountsThrough (n : Nat) : List Nat :=
  PowTower.Expr.fastCountsThrough (Sparse.ofNat 1) certifiedCombineLog n

theorem certifiedLevelCard_eq_countsThrough_getD {N n : Nat}
    (hpos : 0 < n) (hN : n ≤ N) :
    certifiedLevelCard n = (certifiedLevelCountsThrough N).getD (n - 1) 0 := by
  rw [certifiedLevelCard, certifiedLevel, certifiedLevelCountsThrough]
  exact PowTower.Expr.recursiveValueFinset_card_eq_fastCountsThrough_getD hpos hN

theorem certifiedLevelCountsThrough_getD_eq_sharedSparseLogCountsMemoThrough_getD
    {N i : Nat} (hi : i < N) :
    (certifiedLevelCountsThrough N).getD i 0 =
      (sharedSparseLogCountsMemoThrough N).getD i 0 := by
  have hpos : 0 < i + 1 := Nat.succ_pos i
  have hN : i + 1 ≤ N := Nat.succ_le_iff.mpr hi
  have hcert := certifiedLevelCard_eq_countsThrough_getD (N := N) (n := i + 1) hpos hN
  have hshared :=
    certifiedLevelCard_eq_sharedSparseLogCountsMemoThrough_getD (N := N) (n := i + 1) hpos hN
  simpa using hcert.symm.trans hshared

theorem a002845_eq_of_certifiedLevelCountsThrough {N n value : Nat}
    (hpos : 0 < n) (hN : n ≤ N)
    (hcount : (certifiedLevelCountsThrough N).getD (n - 1) 0 = value) :
    a002845 n = value := by
  calc
    a002845 n = certifiedLevelCard n := a002845_eq_certifiedLevelCard n
    _ = (certifiedLevelCountsThrough N).getD (n - 1) 0 :=
      certifiedLevelCard_eq_countsThrough_getD hpos hN
    _ = value := hcount

def a002845ValuesThroughTwentyThree : List Nat :=
  [1, 1, 1, 2, 4, 8, 17, 36, 78, 171, 379, 851, 1928, 4396, 10087, 23273,
    53948, 125608, 293543, 688366, 1619087, 3818818, 9029719]

/-- Certified A002845 counts through `n = 23`, computed once as a prefix table. -/
theorem certifiedLevelCountsThrough_twenty_three :
    certifiedLevelCountsThrough 23 = a002845ValuesThroughTwentyThree := by
  native_decide

theorem a002845_eq_of_twenty_three_table {n value : Nat}
    (hpos : 0 < n) (hN : n ≤ 23)
    (hcount : a002845ValuesThroughTwentyThree.getD (n - 1) 0 = value) :
    a002845 n = value := by
  apply a002845_eq_of_certifiedLevelCountsThrough (N := 23) hpos hN
  rw [certifiedLevelCountsThrough_twenty_three]
  exact hcount

/-- OEIS A002845 has value `1928` at `n = 13`. -/
theorem a002845_thirteen : a002845 13 = 1928 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `4396` at `n = 14`. -/
theorem a002845_fourteen : a002845 14 = 4396 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `10087` at `n = 15`. -/
theorem a002845_fifteen : a002845 15 = 10087 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `23273` at `n = 16`. -/
theorem a002845_sixteen : a002845 16 = 23273 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `53948` at `n = 17`. -/
theorem a002845_seventeen : a002845 17 = 53948 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `125608` at `n = 18`. -/
theorem a002845_eighteen : a002845 18 = 125608 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `293543` at `n = 19`. -/
theorem a002845_nineteen : a002845 19 = 293543 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `688366` at `n = 20`. -/
theorem a002845_twenty : a002845 20 = 688366 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `1619087` at `n = 21`. -/
theorem a002845_twenty_one : a002845 21 = 1619087 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `3818818` at `n = 22`. -/
theorem a002845_twenty_two : a002845 22 = 3818818 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

/-- OEIS A002845 has value `9029719` at `n = 23`. -/
theorem a002845_twenty_three : a002845 23 = 9029719 := by
  apply a002845_eq_of_twenty_three_table <;> native_decide

end A002845

end LeanProofs
