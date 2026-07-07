import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.List.Sort

/-!
# Verified hereditary sparse binary arithmetic

A hereditary sparse binary value `bits xs` denotes `sum (x in xs), 2 ^ eval x`,
with the bit exponents themselves hereditary sparse binary values.  This is the
number representation used by the A002845 exact-logarithm computations: the
denoted naturals are far too large to materialize, so all arithmetic must stay
structural.

This module defines the representation together with **total, Lean-proved**
executable arithmetic:

- `compare` orders values numerically on canonical representations
  (`compare_iff`);
- `incr`, `insBit`, `add`, and `shift` implement increment, single-bit
  insertion with carries, addition, and multiplication by `2 ^ b`, all by
  structural recursion;
- on canonical inputs each operation is proved to return the canonical
  representation of the expected number (`add_eq_ofNat`, `shift_eq_ofNat`),
  so no `implemented_by` substitution is needed anywhere downstream.

The canonical predicate `Canonical` (hereditarily canonical bit lists with
strictly increasing denoted exponents) characterizes exactly the `ofNat`
images (`canonical_ofNat`, `canonical_eq_ofNat_eval`).
-/

set_option maxRecDepth 100000

namespace LeanProofs

namespace A002845

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

/-- Every natural number has a canonical sparse representation. -/
theorem canonical_ofNat (n : Nat) : Canonical (ofNat n) := by
  induction n using ofNat.induct with
  | case1 n _ ih =>
      rw [ofNat.eq_1, Canonical.eq_1]
      constructor
      · intro p hp
        simp only [List.mem_map, List.mem_attach, true_and] at hp
        rcases hp with ⟨i, rfl⟩
        exact ih i
      · have hmap :
            (n.bitIndices.attach.map fun i => ofNat i.1).map eval = n.bitIndices := by
          rw [List.map_map]
          rw [show
            List.map
                (eval ∘ fun i : { x // x ∈ n.bitIndices } => ofNat ↑i)
                n.bitIndices.attach =
              List.map (fun i : { x // x ∈ n.bitIndices } => (i : Nat))
                n.bitIndices.attach by
                apply List.map_congr_left
                intro i _
                simp [eval_ofNat]]
          simp
        rw [hmap]
        exact Nat.bitIndices_sorted

/-- Canonical values are exactly the `ofNat` images of their denotations. -/
theorem canonical_eq_ofNat_eval {x : Sparse} (hx : Canonical x) :
    x = ofNat (eval x) :=
  eq_of_eval_eq hx (canonical_ofNat (eval x)) (by rw [eval_ofNat])

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

/-!
## Numeric correctness of `compare` on canonical values
-/

/-- Sum denoted by a bit list: `listEval xs = sum (p in xs), 2 ^ eval p`. -/
def listEval (xs : List Sparse) : Nat :=
  (xs.map fun p => 2 ^ eval p).sum

@[simp] theorem listEval_nil : listEval [] = 0 := rfl

@[simp] theorem listEval_cons (p : Sparse) (l : List Sparse) :
    listEval (p :: l) = 2 ^ eval p + listEval l := by
  simp [listEval]

theorem eval_bits (xs : List Sparse) : eval (.bits xs) = listEval xs := by
  rw [eval.eq_1]
  rfl

theorem listEval_reverse (xs : List Sparse) : listEval xs.reverse = listEval xs := by
  simp [listEval]

/-- Split a pairwise property of a mapped cons list into head bounds and tail. -/
theorem pairwise_map_eval_cons {R : Nat → Nat → Prop} {a : Sparse} {l : List Sparse}
    (h : ((a :: l).map eval).Pairwise R) :
    (∀ b ∈ l, R (eval a) (eval b)) ∧ (l.map eval).Pairwise R := by
  rw [List.map_cons, List.pairwise_cons] at h
  exact ⟨fun b hb => h.1 (eval b) (List.mem_map_of_mem hb), h.2⟩

/--
A strictly descending bit list headed by exponent value at most `t` denotes
less than `2 ^ (t + 1)`.
-/
theorem listEval_lt_two_pow : ∀ {l : List Sparse} {t : Nat},
    ((l.map eval).Pairwise (fun a b => b < a)) → (∀ p ∈ l, eval p ≤ t) →
    listEval l < 2 ^ (t + 1)
  | [], t, _, _ => by
      simpa using Nat.two_pow_pos (t + 1)
  | d :: ds, t, hdesc, hle => by
      rw [listEval_cons]
      cases ds with
      | nil =>
          have hd : eval d ≤ t := hle d (by simp)
          have h1 : (2 : Nat) ^ eval d ≤ 2 ^ t :=
            Nat.pow_le_pow_right (by omega) hd
          have h2 : (2 : Nat) ^ (t + 1) = 2 ^ t * 2 := pow_succ 2 t
          have h3 : 0 < (2 : Nat) ^ t := Nat.two_pow_pos t
          simp only [listEval_nil]
          omega
      | cons e es =>
          have hdesc' : ((e :: es).map eval).Pairwise (fun a b => b < a) :=
            (pairwise_map_eval_cons hdesc).2
          have hheadlt : ∀ p ∈ e :: es, eval p < eval d :=
            fun p hp => (pairwise_map_eval_cons hdesc).1 p hp
          have hdpos : 1 ≤ eval d := by
            have := hheadlt e (by simp)
            omega
          have hles : ∀ p ∈ e :: es, eval p ≤ eval d - 1 := by
            intro p hp
            have := hheadlt p hp
            omega
          have htail : listEval (e :: es) < 2 ^ (eval d - 1 + 1) :=
            listEval_lt_two_pow hdesc' hles
          have htail' : listEval (e :: es) < 2 ^ eval d := by
            have heq : eval d - 1 + 1 = eval d := by omega
            rwa [heq] at htail
          have hd : eval d ≤ t := hle d (by simp)
          have hpowd : (2 : Nat) ^ (eval d + 1) = 2 ^ eval d * 2 := pow_succ 2 (eval d)
          have hmono : (2 : Nat) ^ (eval d + 1) ≤ 2 ^ (t + 1) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega

theorem compareDescending_cons_of_lt {d e : Sparse} (ds es : List Sparse)
    (h : compare d e = Ordering.lt) :
    compareDescending (d :: ds) (e :: es) = Ordering.lt := by
  simp only [compareDescending, h]

theorem compareDescending_cons_of_eq {d e : Sparse} (ds es : List Sparse)
    (h : compare d e = Ordering.eq) :
    compareDescending (d :: ds) (e :: es) = compareDescending ds es := by
  simp only [compareDescending, h]

theorem compareDescending_cons_of_gt {d e : Sparse} (ds es : List Sparse)
    (h : compare d e = Ordering.gt) :
    compareDescending (d :: ds) (e :: es) = Ordering.gt := by
  simp only [compareDescending, h]

/--
Numeric trichotomy of the descending-list comparator, given the numeric
trichotomy of `compare` on all element pairs.
-/
theorem compareDescending_iff_of : ∀ {ds es : List Sparse},
    (∀ p ∈ ds, Canonical p) → (∀ q ∈ es, Canonical q) →
    ((ds.map eval).Pairwise (fun a b => b < a)) →
    ((es.map eval).Pairwise (fun a b => b < a)) →
    (∀ p ∈ ds, ∀ q ∈ es,
      (compare p q = Ordering.lt ↔ eval p < eval q) ∧
      (compare p q = Ordering.eq ↔ p = q) ∧
      (compare p q = Ordering.gt ↔ eval q < eval p)) →
    ((compareDescending ds es = Ordering.lt ↔ listEval ds < listEval es) ∧
     (compareDescending ds es = Ordering.eq ↔ ds = es) ∧
     (compareDescending ds es = Ordering.gt ↔ listEval es < listEval ds))
  | [], [], _, _, _, _, _ => by
      simp [compareDescending]
  | [], e :: es, _, _, _, _, _ => by
      have hpos : 0 < listEval (e :: es) := by
        have h1 : 0 < (2 : Nat) ^ eval e := Nat.two_pow_pos _
        simp only [listEval_cons]
        omega
      have hred : compareDescending [] (e :: es) = Ordering.lt := by
        simp [compareDescending]
      rw [hred]
      refine ⟨iff_of_true rfl (by simp only [listEval_nil]; exact hpos),
        iff_of_false (by decide) (by simp),
        iff_of_false (by decide) (by simp only [listEval_nil]; omega)⟩
  | d :: ds, [], _, _, _, _, _ => by
      have hpos : 0 < listEval (d :: ds) := by
        have h1 : 0 < (2 : Nat) ^ eval d := Nat.two_pow_pos _
        simp only [listEval_cons]
        omega
      have hred : compareDescending (d :: ds) [] = Ordering.gt := by
        simp [compareDescending]
      rw [hred]
      refine ⟨iff_of_false (by decide) (by simp only [listEval_nil]; omega),
        iff_of_false (by decide) (by simp),
        iff_of_true rfl (by simp only [listEval_nil]; exact hpos)⟩
  | d :: ds, e :: es, hdc, hec, hdd, hed, h => by
      have hd : Canonical d := hdc d (by simp)
      have he : Canonical e := hec e (by simp)
      have hcmp := h d (by simp) e (by simp)
      have hdd' : ((ds).map eval).Pairwise (fun a b => b < a) :=
        (pairwise_map_eval_cons hdd).2
      have hed' : ((es).map eval).Pairwise (fun a b => b < a) :=
        (pairwise_map_eval_cons hed).2
      -- head domination in both directions
      have hdomLt : eval d < eval e → listEval (d :: ds) < listEval (e :: es) := by
        intro hlt
        have hbound : listEval (d :: ds) < 2 ^ (eval d + 1) :=
          listEval_lt_two_pow hdd
            (by
              intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact Nat.le_refl _
              · exact Nat.le_of_lt ((pairwise_map_eval_cons hdd).1 p hp))
        have hstep : (2 : Nat) ^ (eval d + 1) ≤ 2 ^ eval e :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hhead : (2 : Nat) ^ eval e ≤ listEval (e :: es) := by
          simp only [listEval_cons]
          omega
        omega
      have hdomGt : eval e < eval d → listEval (e :: es) < listEval (d :: ds) := by
        intro hlt
        have hbound : listEval (e :: es) < 2 ^ (eval e + 1) :=
          listEval_lt_two_pow hed
            (by
              intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact Nat.le_refl _
              · exact Nat.le_of_lt ((pairwise_map_eval_cons hed).1 q hq))
        have hstep : (2 : Nat) ^ (eval e + 1) ≤ 2 ^ eval d :=
          Nat.pow_le_pow_right (by omega) (by omega)
        have hhead : (2 : Nat) ^ eval d ≤ listEval (d :: ds) := by
          simp only [listEval_cons]
          omega
        omega
      rcases hde : compare d e with _ | _ | _
      · -- compare d e = .lt
        have hlt : eval d < eval e := hcmp.1.mp hde
        have hsum : listEval (d :: ds) < listEval (e :: es) := hdomLt hlt
        rw [compareDescending_cons_of_lt ds es hde]
        refine ⟨iff_of_true rfl hsum, ?_, ?_⟩
        · refine iff_of_false (by simp) ?_
          intro habs
          injection habs with h1 h2
          subst h1
          exact absurd hlt (Nat.lt_irrefl _)
        · exact iff_of_false (by simp) (by omega)
      · -- compare d e = .eq
        have hdeq : d = e := hcmp.2.1.mp hde
        subst hdeq
        have hrest := compareDescending_iff_of
          (fun p hp => hdc p (by simp [hp]))
          (fun q hq => hec q (by simp [hq]))
          hdd' hed'
          (fun p hp q hq => h p (by simp [hp]) q (by simp [hq]))
        rw [compareDescending_cons_of_eq ds es hde]
        refine ⟨?_, ?_, ?_⟩
        · rw [hrest.1]
          simp only [listEval_cons]
          omega
        · rw [hrest.2.1]
          simp
        · rw [hrest.2.2]
          simp only [listEval_cons]
          omega
      · -- compare d e = .gt
        have hgt : eval e < eval d := hcmp.2.2.mp hde
        have hsum : listEval (e :: es) < listEval (d :: ds) := hdomGt hgt
        rw [compareDescending_cons_of_gt ds es hde]
        refine ⟨?_, ?_, iff_of_true rfl hsum⟩
        · exact iff_of_false (by simp) (by omega)
        · refine iff_of_false (by simp) ?_
          intro habs
          injection habs with h1 h2
          subst h1
          exact absurd hgt (Nat.lt_irrefl _)

/-- `compare` decides the numeric order of canonical sparse values. -/
theorem compare_iff : ∀ (x y : Sparse), Canonical x → Canonical y →
    (compare x y = Ordering.lt ↔ eval x < eval y) ∧
    (compare x y = Ordering.eq ↔ x = y) ∧
    (compare x y = Ordering.gt ↔ eval y < eval x)
  | .bits xs, .bits ys, hx, hy => by
      rw [Canonical.eq_1] at hx hy
      have hxd : ((xs.reverse).map eval).Pairwise (fun a b => b < a) := by
        rw [List.map_reverse, List.pairwise_reverse]
        simpa [List.sortedLT_iff_pairwise] using hx.2
      have hyd : ((ys.reverse).map eval).Pairwise (fun a b => b < a) := by
        rw [List.map_reverse, List.pairwise_reverse]
        simpa [List.sortedLT_iff_pairwise] using hy.2
      have hres := compareDescending_iff_of
        (fun p hp => hx.1 p (List.mem_reverse.mp hp))
        (fun q hq => hy.1 q (List.mem_reverse.mp hq))
        hxd hyd
        (fun p hp q hq =>
          compare_iff p q (hx.1 p (List.mem_reverse.mp hp))
            (hy.1 q (List.mem_reverse.mp hq)))
      rw [compare]
      refine ⟨?_, ?_, ?_⟩
      · rw [hres.1, listEval_reverse, listEval_reverse, eval_bits, eval_bits]
      · rw [hres.2.1]
        constructor
        · intro hrev
          have := List.reverse_injective hrev
          simp [this]
        · intro hxy
          cases hxy
          rfl
      · rw [hres.2.2, listEval_reverse, listEval_reverse, eval_bits, eval_bits]
termination_by x y => sizeOf x + sizeOf y
decreasing_by
  have hp' : sizeOf p < sizeOf xs := List.sizeOf_lt_of_mem (List.mem_reverse.mp hp)
  have hq' : sizeOf q < sizeOf ys := List.sizeOf_lt_of_mem (List.mem_reverse.mp hq)
  simp only [Sparse.bits.sizeOf_spec]
  omega

/-!
## Total executable arithmetic
-/

mutual
  /-- Add `1` to a hereditary sparse binary value. -/
  def incr : Sparse → Sparse
    | .bits xs => .bits (insBit zero xs)
  termination_by x => sizeOf x
  decreasing_by
    simp only [Sparse.bits.sizeOf_spec]
    omega

  /-- Insert one set bit `2 ^ p` into a sorted bit list, carrying on collision. -/
  def insBit (p : Sparse) : List Sparse → List Sparse
    | [] => [p]
    | q :: qs =>
        match compare p q with
        | .lt => p :: q :: qs
        | .eq => insBit (incr q) qs
        | .gt => q :: insBit p qs
  termination_by l => sizeOf l
  decreasing_by
    · simp only [List.cons.sizeOf_spec]
      omega
    · simp only [List.cons.sizeOf_spec]
      omega
    · simp only [List.cons.sizeOf_spec]
      omega
end

/-- Add two hereditary sparse binary nonnegative integers. -/
def add : Sparse → Sparse → Sparse
  | .bits xs, .bits ys => .bits (ys.foldl (fun acc p => insBit p acc) xs)

/-- Multiply by `2 ^ b`, i.e. shift all bit positions upward by `b`. -/
def shift (x b : Sparse) : Sparse :=
  match x with
  | .bits xs => .bits (xs.foldl (fun acc p => insBit (add p b) acc) [])

/-!
## Correctness of the arithmetic on canonical values
-/

/--
Specification of the bit insertion, with the increment behavior of the list
elements supplied as a hypothesis (discharged below once `incr_spec` is
available).
-/
theorem insBit_spec_of : ∀ {p : Sparse} {l : List Sparse},
    Canonical p → (∀ q ∈ l, Canonical q) → ((l.map eval).Pairwise (· < ·)) →
    (∀ q ∈ l, Canonical (incr q) ∧ eval (incr q) = eval q + 1) →
    (∀ r ∈ insBit p l, Canonical r) ∧
      ((insBit p l).map eval).Pairwise (· < ·) ∧
      listEval (insBit p l) = 2 ^ eval p + listEval l ∧
      (∀ r ∈ insBit p l, eval p ≤ eval r ∨ r ∈ l)
  | p, [], hp, _, _, _ => by
      rw [insBit]
      refine ⟨?_, ?_, by simp, ?_⟩
      · intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact hp
      · simp
      · intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact Or.inl (Nat.le_refl _)
  | p, q :: qs, hp, hl, hs, hincr => by
      have hq : Canonical q := hl q (by simp)
      have hqs : ∀ r ∈ qs, Canonical r := fun r hr => hl r (by simp [hr])
      have hs' : (qs.map eval).Pairwise (· < ·) :=
        (List.pairwise_cons.mp (by simpa using hs)).2
      have hqlt : ∀ r ∈ qs, eval q < eval r := by
        intro r hr
        exact (List.pairwise_cons.mp (by simpa using hs)).1 (eval r)
          (List.mem_map_of_mem hr)
      rw [insBit]
      rcases hpq : compare p q with _ | _ | _
      · -- eval p < eval q: insert in front
        have hlt : eval p < eval q := ((compare_iff p q hp hq).1).mp hpq
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hp
          · exact hl r hr
        · simp only [List.map_cons]
          refine List.Pairwise.cons ?_ (by simpa using hs)
          intro b hb
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact hlt
          · rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
            exact Nat.lt_trans hlt (hqlt r hr)
        · simp
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Or.inl (Nat.le_refl _)
          · exact Or.inr hr
      · -- p = q: carry
        have hpeq : p = q := ((compare_iff p q hp hq).2.1).mp hpq
        have hqinc := hincr q (by simp)
        have hspec := insBit_spec_of (p := incr q) (l := qs) hqinc.1 hqs hs'
          (fun r hr => hincr r (by simp [hr]))
        refine ⟨hspec.1, hspec.2.1, ?_, ?_⟩
        · rw [hspec.2.2.1, hqinc.2, hpeq]
          have hpow : (2 : Nat) ^ (eval q + 1) = 2 ^ eval q + 2 ^ eval q := by
            rw [pow_succ]
            omega
          simp only [listEval_cons]
          omega
        · intro r hr
          rcases hspec.2.2.2 r hr with hge | hmem
          · refine Or.inl ?_
            rw [hpeq]
            have : eval q + 1 ≤ eval r := by
              rw [← hqinc.2]
              exact hge
            omega
          · exact Or.inr (by simp [hmem])
      · -- eval q < eval p: keep head, insert into tail
        have hgt : eval q < eval p := ((compare_iff p q hp hq).2.2).mp hpq
        have hspec := insBit_spec_of (p := p) (l := qs) hp hqs hs'
          (fun r hr => hincr r (by simp [hr]))
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hq
          · exact hspec.1 r hr
        · simp only [List.map_cons]
          refine List.Pairwise.cons ?_ hspec.2.1
          intro b hb
          rcases List.mem_map.mp hb with ⟨r, hr, rfl⟩
          rcases hspec.2.2.2 r hr with hge | hmem
          · exact Nat.lt_of_lt_of_le hgt hge
          · exact hqlt r hmem
        · rw [listEval_cons, hspec.2.2.1]
          simp only [listEval_cons]
          omega
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact Or.inr (by simp)
          · rcases hspec.2.2.2 r hr with hge | hmem
            · exact Or.inl hge
            · exact Or.inr (by simp [hmem])

/-- Increment computes the canonical successor. -/
theorem incr_spec : ∀ (x : Sparse), Canonical x →
    Canonical (incr x) ∧ eval (incr x) = eval x + 1
  | .bits xs, hx => by
      rw [Canonical.eq_1] at hx
      have hspec := insBit_spec_of (p := zero) (l := xs) canonical_zero hx.1
        (by simpa [List.sortedLT_iff_pairwise] using hx.2)
        (fun q hq => incr_spec q (hx.1 q hq))
      rw [incr]
      constructor
      · rw [Canonical.eq_1]
        exact ⟨hspec.1, by simpa [List.sortedLT_iff_pairwise] using hspec.2.1⟩
      · rw [eval_bits, eval_bits, hspec.2.2.1, eval_zero]
        omega
termination_by x => sizeOf x
decreasing_by
  have := List.sizeOf_lt_of_mem hq
  simp only [Sparse.bits.sizeOf_spec]
  omega

/-- Bit insertion into a canonical sorted bit list, fully discharged. -/
theorem insBit_spec {p : Sparse} {l : List Sparse} (hp : Canonical p)
    (hl : ∀ q ∈ l, Canonical q) (hs : (l.map eval).Pairwise (· < ·)) :
    (∀ r ∈ insBit p l, Canonical r) ∧
      ((insBit p l).map eval).Pairwise (· < ·) ∧
      listEval (insBit p l) = 2 ^ eval p + listEval l :=
  ⟨(insBit_spec_of hp hl hs (fun q hq => incr_spec q (hl q hq))).1,
   (insBit_spec_of hp hl hs (fun q hq => incr_spec q (hl q hq))).2.1,
   (insBit_spec_of hp hl hs (fun q hq => incr_spec q (hl q hq))).2.2.1⟩

/-- Folding bit insertions accumulates canonically and additively. -/
theorem foldl_insBit_spec : ∀ (ps : List Sparse) (acc : List Sparse),
    (∀ q ∈ acc, Canonical q) → ((acc.map eval).Pairwise (· < ·)) →
    (∀ p ∈ ps, Canonical p) →
    (∀ r ∈ ps.foldl (fun acc p => insBit p acc) acc, Canonical r) ∧
      (((ps.foldl (fun acc p => insBit p acc) acc).map eval).Pairwise (· < ·)) ∧
      listEval (ps.foldl (fun acc p => insBit p acc) acc) =
        listEval acc + listEval ps
  | [], acc, hacc, hsort, _ => by
      simpa using ⟨hacc, hsort⟩
  | p :: ps, acc, hacc, hsort, hps => by
      rw [List.foldl_cons]
      have h1 := insBit_spec (hps p (by simp)) hacc hsort
      have h2 := foldl_insBit_spec ps (insBit p acc) h1.1 h1.2.1
        (fun r hr => hps r (by simp [hr]))
      refine ⟨h2.1, h2.2.1, ?_⟩
      rw [h2.2.2, h1.2.2]
      simp only [listEval_cons]
      omega

/-- Addition of canonical sparse values is canonical and denotes the sum. -/
theorem add_spec : ∀ {x y : Sparse}, Canonical x → Canonical y →
    Canonical (add x y) ∧ eval (add x y) = eval x + eval y
  | .bits xs, .bits ys, hx, hy => by
      rw [Canonical.eq_1] at hx hy
      have hspec := foldl_insBit_spec ys xs hx.1
        (by simpa [List.sortedLT_iff_pairwise] using hx.2) hy.1
      rw [add]
      constructor
      · rw [Canonical.eq_1]
        exact ⟨hspec.1, by simpa [List.sortedLT_iff_pairwise] using hspec.2.1⟩
      · rw [eval_bits, eval_bits, eval_bits, hspec.2.2]

/-- The shift fold accumulates the exponent-translated bits. -/
theorem foldl_shift_spec (b : Sparse) (hb : Canonical b) :
    ∀ (ps : List Sparse) (acc : List Sparse),
    (∀ q ∈ acc, Canonical q) → ((acc.map eval).Pairwise (· < ·)) →
    (∀ p ∈ ps, Canonical p) →
    (∀ r ∈ ps.foldl (fun acc p => insBit (add p b) acc) acc, Canonical r) ∧
      (((ps.foldl (fun acc p => insBit (add p b) acc) acc).map eval).Pairwise (· < ·)) ∧
      listEval (ps.foldl (fun acc p => insBit (add p b) acc) acc) =
        listEval acc + (ps.map fun p => 2 ^ (eval p + eval b)).sum
  | [], acc, hacc, hsort, _ => by
      simpa using ⟨hacc, hsort⟩
  | p :: ps, acc, hacc, hsort, hps => by
      rw [List.foldl_cons]
      have hpb := add_spec (hps p (by simp)) hb
      have h1 := insBit_spec hpb.1 hacc hsort
      have h2 := foldl_shift_spec b hb ps (insBit (add p b) acc) h1.1 h1.2.1
        (fun r hr => hps r (by simp [hr]))
      refine ⟨h2.1, h2.2.1, ?_⟩
      rw [h2.2.2, h1.2.2, hpb.2]
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Translating every exponent by `c` multiplies the denoted sum by `2 ^ c`. -/
theorem sum_pow_add (xs : List Sparse) (c : Nat) :
    (xs.map fun p => 2 ^ (eval p + c)).sum = listEval xs * 2 ^ c := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      rw [List.map_cons, List.sum_cons, ih, listEval_cons, Nat.add_mul, pow_add]

/-- Shifting a canonical value by a canonical exponent multiplies by `2 ^ b`. -/
theorem shift_spec : ∀ {x b : Sparse}, Canonical x → Canonical b →
    Canonical (shift x b) ∧ eval (shift x b) = eval x * 2 ^ eval b
  | .bits xs, b, hx, hb => by
      rw [Canonical.eq_1] at hx
      have hspec := foldl_shift_spec b hb xs [] (by simp) (by simp) hx.1
      rw [shift]
      constructor
      · rw [Canonical.eq_1]
        exact ⟨hspec.1, by simpa [List.sortedLT_iff_pairwise] using hspec.2.1⟩
      · rw [eval_bits, eval_bits, hspec.2.2, sum_pow_add]
        simp

/-- Addition agrees with the canonical semantic addition. -/
theorem add_eq_ofNat {x y : Sparse} (hx : Canonical x) (hy : Canonical y) :
    add x y = ofNat (eval x + eval y) :=
  eq_of_eval_eq (add_spec hx hy).1 (canonical_ofNat _)
    (by rw [(add_spec hx hy).2, eval_ofNat])

/-- Shifting agrees with the canonical semantic multiplication by `2 ^ b`. -/
theorem shift_eq_ofNat {x b : Sparse} (hx : Canonical x) (hb : Canonical b) :
    shift x b = ofNat (eval x * 2 ^ eval b) :=
  eq_of_eval_eq (shift_spec hx hb).1 (canonical_ofNat _)
    (by rw [(shift_spec hx hb).2, eval_ofNat])

end Sparse

end A002845

end LeanProofs
