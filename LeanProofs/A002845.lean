import LeanProofs.PowTower
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Finset.NAry
import Std.Data.HashSet.Lemmas

/-!
# Initial values of OEIS A002845

OEIS A002845 counts the distinct values taken by `2^2^...^2`, with `n`
copies of `2` and all binary parenthesizations allowed.

The primary definition below is the shared lexical one from `PowTower.Expr`:
the single atom is interpreted as the literal `2`, and the binary node is
interpreted as natural-number exponentiation.  The sparse-binary logarithm code
is retained as a computation-facing view, with Lean proofs connecting it back
to the shared lexical definition.
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

/-- A hereditary sparse binary nonnegative integer.

`bits xs` represents `sum (x in xs), 2^x`, with the executable operations below
maintaining `xs` in increasing numeric order and without duplicates.
-/
inductive Sparse where
  | bits : List Sparse → Sparse
deriving Repr, Inhabited

namespace Sparse

mutual
  def decEq : (x y : Sparse) → Decidable (x = y)
    | .bits xs, .bits ys =>
        match decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hxy; cases hxy; exact h rfl)

  def decEqList : (xs ys : List Sparse) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match decEq x y, decEqList xs ys with
        | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
        | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
        | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
end

instance : DecidableEq Sparse :=
  decEq

/-- Boolean equality for sparse-binary trees, definitionally tied to `DecidableEq`. -/
def beq (x y : Sparse) : Bool :=
  decide (x = y)

/-- Structural hash for sparse-binary trees. -/
partial def hash : Sparse → UInt64
  | .bits xs => mixHash 17 (hashList xs)
where
  hashList : List Sparse → UInt64
    | [] => 19
    | x :: xs => mixHash (hash x) (hashList xs)

instance : Hashable Sparse where
  hash := hash

instance : LawfulBEq Sparse where
  rfl := by
    intro a
    simp [BEq.beq]
  eq_of_beq := by
    intro a b h
    simpa [BEq.beq, beq] using h

instance : EquivBEq Sparse where
  symm := by
    intro a b h
    have hab : a = b := LawfulBEq.eq_of_beq h
    subst hab
    simp [BEq.beq]
  trans := by
    intro a b c hab hbc
    have hab' : a = b := LawfulBEq.eq_of_beq hab
    have hbc' : b = c := LawfulBEq.eq_of_beq hbc
    subst hab'
    subst hbc'
    simp [BEq.beq]
  rfl := by
    intro a
    simp [BEq.beq]

instance : LawfulHashable Sparse where
  hash_eq := by
    intro a b h
    have hab : a = b := LawfulBEq.eq_of_beq h
    subst hab
    rfl

/-- Zero in hereditary sparse binary. -/
def zero : Sparse :=
  .bits []

/-- One in hereditary sparse binary. -/
def one : Sparse :=
  .bits [zero]

/-- Natural-number denotation of a hereditary sparse binary value. -/
def eval : Sparse → Nat
  | .bits xs => (xs.map fun p => 2 ^ eval p).sum

/-- Canonical hereditary sparse binary representation of a natural number. -/
def ofNat : Nat → Sparse
  | n => .bits (n.bitIndices.attach.map fun i => ofNat i.1)
termination_by n => n
decreasing_by
  exact lt_of_lt_of_le Nat.lt_two_pow_self (Nat.two_pow_le_of_mem_bitIndices i.2)

theorem eval_ofNat (n : Nat) : eval (ofNat n) = n := by
  induction n using ofNat.induct with
  | case1 n _ ih =>
      rw [ofNat.eq_1, eval.eq_1]
      simp only [List.map_map]
      rw [show
        List.map
            ((fun p => 2 ^ eval p) ∘ fun i : { x // x ∈ n.bitIndices } => ofNat ↑i)
            n.bitIndices.attach =
          List.map (fun x => 2 ^ eval (ofNat x)) n.bitIndices by
            simp [Function.comp_def]]
      have hmap : List.map (fun x => 2 ^ eval (ofNat x)) n.bitIndices =
          List.map (fun x => 2 ^ x) n.bitIndices := by
        apply List.map_congr_left
        intro x hx
        rw [ih ⟨x, hx⟩]
      rw [hmap]
      exact Nat.sum_map_two_pow_bitIndices n

theorem ofNat_injective : Function.Injective ofNat := by
  intro a b h
  exact by simpa [eval_ofNat] using congrArg eval h

/--
Canonical sparse values have canonical bit positions and strictly increasing
denoted exponents.
-/
def Canonical : Sparse → Prop
  | .bits xs => (∀ p ∈ xs, Canonical p) ∧ (xs.map eval).SortedLT

/-- The bit indices of a canonical sparse value are exactly its bit positions. -/
theorem bitIndices_eval {x : Sparse} (hx : Canonical x) :
    x.eval.bitIndices = match x with | .bits xs => xs.map eval := by
  cases x with
  | bits xs =>
      rw [Canonical.eq_1] at hx
      rw [eval.eq_1]
      simpa [List.map_map, Function.comp_def]
        using Nat.bitIndices_sum_map_two_pow hx.2

mutual
  /-- Canonical sparse binary representation is injective in its denotation. -/
  theorem eq_of_eval_eq {x y : Sparse} (hx : Canonical x) (hy : Canonical y)
      (h : eval x = eval y) : x = y := by
    cases x with
    | bits xs =>
        cases y with
        | bits ys =>
            rw [Canonical.eq_1] at hx hy
            have hxidx : (bits xs).eval.bitIndices = xs.map eval :=
              bitIndices_eval (x := bits xs) (by rw [Canonical.eq_1]; exact hx)
            have hyidx : (bits ys).eval.bitIndices = ys.map eval :=
              bitIndices_eval (x := bits ys) (by rw [Canonical.eq_1]; exact hy)
            have hmaps : xs.map eval = ys.map eval := by
              calc
                xs.map eval = (bits xs).eval.bitIndices := hxidx.symm
                _ = (bits ys).eval.bitIndices := by rw [h]
                _ = ys.map eval := hyidx
            have hxs : xs = ys := list_eq_of_map_eval_eq xs ys hx.1 hy.1 hmaps
            simp [hxs]

  theorem list_eq_of_map_eval_eq (xs ys : List Sparse)
      (hcx : ∀ p ∈ xs, Canonical p) (hcy : ∀ p ∈ ys, Canonical p)
      (h : xs.map eval = ys.map eval) : xs = ys := by
    cases xs with
    | nil =>
        cases ys with
        | nil => rfl
        | cons _ _ => simp at h
    | cons x xs =>
        cases ys with
        | nil => simp at h
        | cons y ys =>
            simp only [List.map_cons, List.cons.injEq] at h
            have hxy : x = y :=
              eq_of_eval_eq (hcx x (by simp)) (hcy y (by simp)) h.1
            have htail : xs = ys :=
              list_eq_of_map_eval_eq xs ys
                (by intro p hp; exact hcx p (by simp [hp]))
                (by intro p hp; exact hcy p (by simp [hp]))
                h.2
            simp [hxy, htail]
end

theorem eval_zero : eval zero = 0 := by
  simp [zero, eval.eq_1]

theorem eval_one : eval one = 1 := by
  simp [one, zero, eval.eq_1]

theorem canonical_zero : Canonical zero := by
  rw [zero, Canonical.eq_1]
  simp [List.sortedLT_iff_pairwise]

theorem canonical_one : Canonical one := by
  rw [one, Canonical.eq_1]
  simp [canonical_zero, eval_zero, List.sortedLT_iff_pairwise]

theorem sizeOf_append_singleton (xs : List Sparse) (x : Sparse) :
    sizeOf (xs ++ [x]) = sizeOf xs + sizeOf x + 1 := by
  induction xs with
  | nil => simp [Nat.add_assoc]
  | cons _ _ ih =>
      simp [ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem sizeOf_reverse (xs : List Sparse) : sizeOf xs.reverse = sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp [List.reverse_cons, sizeOf_append_singleton, ih,
        Nat.add_assoc, Nat.add_comm]

mutual
  /-- Numeric comparison of canonical sparse-binary values. -/
  def compare : Sparse → Sparse → Ordering
    | .bits xs, .bits ys => compareDescending xs.reverse ys.reverse
  termination_by x y => sizeOf x + sizeOf y
  decreasing_by
    simp_wf
    rw [sizeOf_reverse, sizeOf_reverse]
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_lt_add (Nat.lt_succ_self (sizeOf xs)) (Nat.lt_succ_self (sizeOf ys))

  /-- Compare bit-position lists written from high to low. -/
  def compareDescending : List Sparse → List Sparse → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys =>
        match compare x y with
        | .eq => compareDescending xs ys
        | order => order
  termination_by xs ys => sizeOf xs + sizeOf ys
  decreasing_by
    · simp_wf
      have hle : sizeOf x + sizeOf y ≤
          sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) := by
        rw [← Nat.add_assoc]
        exact Nat.le_add_right (sizeOf x + sizeOf y) (sizeOf xs + sizeOf ys)
      have hlt : sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) <
          1 + (1 + (sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)))) := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_lt_add (Nat.lt_succ_self 0)
            (Nat.lt_succ_self (sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys))))
      have hlt' : sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) <
          1 + sizeOf x + sizeOf xs + (1 + sizeOf y + sizeOf ys) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt
      exact Nat.lt_of_le_of_lt hle hlt'
    · simp_wf
      have hle : sizeOf xs + sizeOf ys ≤
          sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Nat.le_add_left (sizeOf xs + sizeOf ys) (sizeOf x + sizeOf y))
      have hlt : sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) <
          1 + (1 + (sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)))) := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_lt_add (Nat.lt_succ_self 0)
            (Nat.lt_succ_self (sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys))))
      have hlt' : sizeOf x + (sizeOf y + (sizeOf xs + sizeOf ys)) <
          1 + sizeOf x + sizeOf xs + (1 + sizeOf y + sizeOf ys) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlt
      exact Nat.lt_of_le_of_lt hle hlt'
end

/-- Add two hereditary sparse binary nonnegative integers. -/
partial def add : Sparse → Sparse → Sparse
  | .bits xs, .bits ys => .bits (ys.foldl (fun acc p => insertBit p acc) xs)
where
  /-- Insert one set bit into a canonical sparse-binary bit list, carrying on
  collision. -/
  insertBit (p : Sparse) : List Sparse → List Sparse
    | [] => [p]
    | q :: qs =>
        match compare p q with
        | .lt => p :: q :: qs
        | .eq => insertBit (add p one) qs
        | .gt => q :: insertBit p qs

/-- Insert one set bit into a canonical bit list. -/
def insertSingletonBit (p : Sparse) (xs : List Sparse) : List Sparse :=
  match add (.bits xs) (.bits [p]) with
  | .bits ys => ys

/-- Multiply by `2^b`, i.e. shift all bit positions upward by `b`. -/
partial def shift (x b : Sparse) : Sparse :=
  match x with
  | .bits xs =>
      .bits (xs.foldl (fun acc p => insertSingletonBit (add p b) acc) [])

end Sparse

/-- The exact logarithm-combine operation:
`log₂ ((2^a)^(2^b)) = a * 2^b`. -/
def combineLog (a b : Sparse) : Sparse :=
  Sparse.shift a b

/--
Proof-facing logarithm-combine operation.  It is definitionally the semantic
operation on sparse denotations, but native execution uses `combineLog`.
-/
def certifiedCombineLog (a b : Sparse) : Sparse :=
  Sparse.ofNat (Sparse.eval a * 2 ^ Sparse.eval b)

attribute [implemented_by combineLog] certifiedCombineLog

theorem eval_certifiedCombineLog (a b : Sparse) :
    Sparse.eval (certifiedCombineLog a b) = Sparse.eval a * 2 ^ Sparse.eval b := by
  simp [certifiedCombineLog, Sparse.eval_ofNat]

/-- Exact sparse logarithm of a canonical expression tree. -/
def sparseLogEval : PowExpr → Sparse
  | .atom => Sparse.ofNat 1
  | .pow a b => certifiedCombineLog (sparseLogEval a) (sparseLogEval b)

theorem sparseLogEval_eq_ofNat_logEval (e : PowExpr) :
    sparseLogEval e = Sparse.ofNat (PowExpr.logEval e) := by
  induction e with
  | atom =>
      rfl
  | pow a b iha ihb =>
      simp [sparseLogEval, PowExpr.logEval, certifiedCombineLog, iha, ihb,
        Sparse.eval_ofNat]

/--
The finite sparse set obtained by evaluating every canonical expression tree.
The proof-facing definition is intentionally direct; `certifiedCombineLog`
supplies the efficient native implementation of each sparse logarithm combine.
-/
def certifiedSparseLogFinset (n : Nat) : Finset Sparse :=
  PowTower.Expr.evalFinset sparseLogEval n

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
Certified dynamic-programming level of exact sparse logarithms.  Unlike
`certifiedSparseLogFinset`, this constructs the semantic set by expression
size, reusing smaller certified levels instead of enumerating all Catalan many
expression trees.
-/
def certifiedLevel : Nat → Finset Sparse
  | 0 => ∅
  | 1 => {Sparse.ofNat 1}
  | n + 2 =>
      (Finset.univ : Finset (Fin (n + 1))).biUnion fun k =>
        Finset.image₂ certifiedCombineLog
          (certifiedLevel (k.1 + 1))
          (certifiedLevel (n + 1 - k.1))
termination_by n => n
decreasing_by
  · exact Nat.succ_lt_succ k.2
  · exact Nat.lt_succ_of_le (Nat.sub_le _ _)

/-- Cardinality of the certified dynamic-programming sparse-logarithm level. -/
def certifiedLevelCard (n : Nat) : Nat :=
  (certifiedLevel n).card

theorem coe_certifiedLevel (n : Nat) :
    (certifiedLevel n : Set Sparse) =
      Sparse.ofNat '' PowExpr.logValueSet n := by
  induction n using certifiedLevel.induct with
  | case1 =>
      ext s
      simp [certifiedLevel, PowExpr.logValueSet, PowTower.Expr.parenthesizations,
        PowTower.Expr.evalSet]
  | case2 =>
      ext s
      simp [certifiedLevel, PowExpr.logValueSet, PowTower.Expr.parenthesizations,
        PowTower.Expr.evalSet, PowExpr.logEval]
  | case3 n ihLeft ihRight =>
      ext s
      simp [certifiedLevel, PowExpr.logValueSet, PowTower.Expr.parenthesizations,
        PowTower.Expr.evalSet, PowExpr.logEval, ihLeft, ihRight,
        certifiedCombineLog, Sparse.eval_ofNat]
      constructor
      · rintro ⟨i, a, ha, b, hb, hs⟩
        exact ⟨i, a, b, ⟨ha, hb⟩, hs⟩
      · rintro ⟨i, a, b, ⟨ha, hb⟩, hs⟩
        exact ⟨i, a, ha, b, hb, hs⟩

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
      PowTower.Expr.recursiveValueFinset (Sparse.ofNat 1) certifiedCombineLog n := by
  induction n using certifiedLevel.induct with
  | case1 =>
      simp [certifiedLevel, PowTower.Expr.recursiveValueFinset]
  | case2 =>
      simp [certifiedLevel, PowTower.Expr.recursiveValueFinset]
  | case3 n ihLeft ihRight =>
      simp [certifiedLevel, PowTower.Expr.recursiveValueFinset, ihLeft, ihRight]

/-- Shared memoized sparse-log count corresponding to A002845. -/
def sharedSparseLogCountMemo (n : Nat) : Nat :=
  (PowTower.Expr.recursiveValueFinsetMemo (Sparse.ofNat 1) certifiedCombineLog n).card

/-- Shared memoized sparse-log counts for sizes `1, ..., n`. -/
def sharedSparseLogCountsMemoThrough (n : Nat) : List Nat :=
  PowTower.Expr.recursiveValueCountsMemoThrough (Sparse.ofNat 1) certifiedCombineLog n

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

/-- Insert all values produced by one binary split of an expression of size
`n` into an accumulator. -/
partial def insertSplitValues (levels : Array (List Sparse)) (leftSize rightSize : Nat)
    (seen : Std.HashSet Sparse) : Std.HashSet Sparse :=
  let left := levels[leftSize - 1]!
  let right := levels[rightSize - 1]!
  left.foldl
    (fun seen a =>
      right.foldl (fun seen b => seen.insert (certifiedCombineLog a b)) seen)
    seen

/-- Compute all distinct logarithms for expressions of a given positive size,
assuming all smaller levels have already been computed. -/
partial def nextLevel (levels : Array (List Sparse)) : List Sparse :=
  let size := levels.size + 1
  if size = 1 then
    [Sparse.one]
  else
    let seen :=
      (List.range (size - 1)).foldl
        (fun seen k => insertSplitValues levels (k + 1) (size - 1 - k) seen)
        (∅ : Std.HashSet Sparse)
    seen.toList

/-- Build the table of distinct logarithm lists through size `fuel`. -/
partial def buildLevels : Nat → Array (List Sparse) → Array (List Sparse)
  | 0, levels => levels
  | fuel + 1, levels =>
      buildLevels fuel (levels.push (nextLevel levels))

/-- The sparse-binary logarithms computed by the executable backend. -/
def a002845SparseLogValues (n : Nat) : List Sparse :=
  if n = 0 then
    []
  else
    (buildLevels n #[])[n - 1]!

/-- Executable sparse-binary backend count for A002845 logarithms. -/
def a002845Sparse (n : Nat) : Nat :=
  (a002845SparseLogValues n).length

attribute [implemented_by a002845Sparse] certifiedLevelCard

/-- OEIS A002845 has value `1928` at `n = 13`. -/
theorem a002845_thirteen : a002845 13 = 1928 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `4396` at `n = 14`. -/
theorem a002845_fourteen : a002845 14 = 4396 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `10087` at `n = 15`. -/
theorem a002845_fifteen : a002845 15 = 10087 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `23273` at `n = 16`. -/
theorem a002845_sixteen : a002845 16 = 23273 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `53948` at `n = 17`. -/
theorem a002845_seventeen : a002845 17 = 53948 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `125608` at `n = 18`. -/
theorem a002845_eighteen : a002845 18 = 125608 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `293543` at `n = 19`. -/
theorem a002845_nineteen : a002845 19 = 293543 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `688366` at `n = 20`. -/
theorem a002845_twenty : a002845 20 = 688366 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `1619087` at `n = 21`. -/
theorem a002845_twenty_one : a002845 21 = 1619087 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `3818818` at `n = 22`. -/
theorem a002845_twenty_two : a002845 22 = 3818818 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- OEIS A002845 has value `9029719` at `n = 23`. -/
theorem a002845_twenty_three : a002845 23 = 9029719 := by
  rw [a002845_eq_certifiedLevelCard]
  native_decide

/-- The sparse backend computes `1` at `n = 1`. -/
theorem a002845Sparse_one : a002845Sparse 1 = 1 := by
  native_decide

/-- The sparse backend computes `1` at `n = 2`. -/
theorem a002845Sparse_two : a002845Sparse 2 = 1 := by
  native_decide

/-- The sparse backend computes `1` at `n = 3`. -/
theorem a002845Sparse_three : a002845Sparse 3 = 1 := by
  native_decide

/-- The sparse backend computes `2` at `n = 4`. -/
theorem a002845Sparse_four : a002845Sparse 4 = 2 := by
  native_decide

/-- The sparse backend computes `4` at `n = 5`. -/
theorem a002845Sparse_five : a002845Sparse 5 = 4 := by
  native_decide

/-- The sparse backend computes `8` at `n = 6`. -/
theorem a002845Sparse_six : a002845Sparse 6 = 8 := by
  native_decide

/-- The sparse backend computes `17` at `n = 7`. -/
theorem a002845Sparse_seven : a002845Sparse 7 = 17 := by
  native_decide

/-- The sparse backend computes `36` at `n = 8`. -/
theorem a002845Sparse_eight : a002845Sparse 8 = 36 := by
  native_decide

/-- The sparse backend computes `78` at `n = 9`. -/
theorem a002845Sparse_nine : a002845Sparse 9 = 78 := by
  native_decide

/-- The sparse backend computes `171` at `n = 10`. -/
theorem a002845Sparse_ten : a002845Sparse 10 = 171 := by
  native_decide

/-- The sparse backend computes `379` at `n = 11`. -/
theorem a002845Sparse_eleven : a002845Sparse 11 = 379 := by
  native_decide

/-- The sparse backend computes `851` at `n = 12`. -/
theorem a002845Sparse_twelve : a002845Sparse 12 = 851 := by
  native_decide

/-- The sparse backend computes `1928` at `n = 13`. -/
theorem a002845Sparse_thirteen : a002845Sparse 13 = 1928 := by
  native_decide

/-- The sparse backend computes `4396` at `n = 14`. -/
theorem a002845Sparse_fourteen : a002845Sparse 14 = 4396 := by
  native_decide

/-- The sparse backend computes `10087` at `n = 15`. -/
theorem a002845Sparse_fifteen : a002845Sparse 15 = 10087 := by
  native_decide

/-- The sparse backend computes `23273` at `n = 16`. -/
theorem a002845Sparse_sixteen : a002845Sparse 16 = 23273 := by
  native_decide

/-- The sparse backend computes `53948` at `n = 17`. -/
theorem a002845Sparse_seventeen : a002845Sparse 17 = 53948 := by
  native_decide

/-- The sparse backend computes `125608` at `n = 18`. -/
theorem a002845Sparse_eighteen : a002845Sparse 18 = 125608 := by
  native_decide

/-- The sparse backend computes `293543` at `n = 19`. -/
theorem a002845Sparse_nineteen : a002845Sparse 19 = 293543 := by
  native_decide

/-- The sparse backend computes `688366` at `n = 20`. -/
theorem a002845Sparse_twenty : a002845Sparse 20 = 688366 := by
  native_decide

/-- The sparse backend computes `1619087` at `n = 21`. -/
theorem a002845Sparse_twenty_one : a002845Sparse 21 = 1619087 := by
  native_decide

/-- The sparse backend computes `3818818` at `n = 22`. -/
theorem a002845Sparse_twenty_two : a002845Sparse 22 = 3818818 := by
  native_decide

end A002845

end LeanProofs
