import PAListCoding.Standard

/-!
# Aggregate and statistical operations on PA-coded lists

This file proves that the six additional arithmetic relations have their
expected meanings on ordinary finite lists.  Sum and product share a generic
running-trace argument.  Median is deliberately characterized through a
sorted permutation: this is the division-free order-statistic definition
used by the PA formula itself.
-/

namespace PAListCoding

open LO FirstOrder
open LO.FirstOrder.Arithmetic

private theorem aggregate_znth_encode_eq_getD (xs : List ℕ) {i : ℕ}
    (hi : i < xs.length) :
    znth (encode xs) i = xs.getD i 0 := by
  rw [List.getD_eq_getElem xs 0 hi]
  exact encode_nth xs ⟨i, hi⟩

/-! ### Generic running aggregates -/

/--
The external counterpart of the coded partial-sum and partial-product
traces.  Keeping the binary operation abstract lets the two long coding
arguments share exactly the same proof.
-/
def RunningAggregateTrace (unit : ℕ) (op : ℕ → ℕ → ℕ)
    (xs trace : List ℕ) (p : ℕ) : Prop :=
  trace.length = xs.length + 1 ∧ trace.getD 0 0 = unit ∧
    (∀ i < xs.length,
      trace.getD (i + 1) 0 = op (trace.getD i 0) (xs.getD i 0)) ∧
    trace.getD xs.length 0 = p

theorem exists_runningAggregateTrace_iff_foldl (unit : ℕ)
    (op : ℕ → ℕ → ℕ) (xs : List ℕ) (p : ℕ) :
    (∃ trace, RunningAggregateTrace unit op xs trace p) ↔
      xs.foldl op unit = p := by
  constructor
  · rintro ⟨trace, hlen, hzero, hstep, hlast⟩
    have hprefix : ∀ i, i < xs.length + 1 →
        trace.getD i 0 = (xs.take i).foldl op unit := by
      intro i hi
      induction i with
      | zero => simpa using hzero
      | succ i ih =>
          have hix : i < xs.length := by omega
          rw [hstep i hix, ih (by omega), List.take_add_one,
            List.getElem?_eq_getElem hix, List.foldl_append]
          rw [List.getD_eq_getElem xs 0 hix]
          rfl
    have hp := hprefix xs.length (Nat.lt_succ_self _)
    rw [List.take_length] at hp
    exact hp.symm.trans hlast
  · intro hfold
    let trace : List ℕ :=
      List.ofFn fun i : Fin (xs.length + 1) ↦ (xs.take i).foldl op unit
    have hget (i : ℕ) (hi : i < xs.length + 1) :
        trace.getD i 0 = (xs.take i).foldl op unit := by
      rw [List.getD_eq_getElem trace 0 (by simpa [trace] using hi)]
      simpa [trace] using List.getElem_ofFn
        (f := fun i : Fin (xs.length + 1) ↦ (xs.take i).foldl op unit)
        (by simpa [trace] using hi)
    refine ⟨trace, by simp [trace], by simpa using hget 0 (by omega), ?_, ?_⟩
    · intro i hi
      rw [hget (i + 1) (by omega), hget i (by omega), List.take_add_one,
        List.getElem?_eq_getElem hi, List.foldl_append]
      rw [List.getD_eq_getElem xs 0 hi]
      rfl
    · simpa [List.take_length, hfold] using
        hget xs.length (Nat.lt_succ_self _)

/-- Convert a coded aggregate witness into its ordinary-list trace and back. -/
theorem coded_runningAggregate_iff (unit : ℕ)
    (op : ℕ → ℕ → ℕ) (xs : List ℕ) (p : ℕ) :
    (∃ traceCode, Seq traceCode ∧
        lh traceCode = lh (encode xs) + 1 ∧ znth traceCode 0 = unit ∧
        (∀ i < lh (encode xs),
          znth traceCode (i + 1) =
            op (znth traceCode i) (znth (encode xs) i)) ∧
        znth traceCode (lh (encode xs)) = p) ↔
      ∃ trace, RunningAggregateTrace unit op xs trace p := by
  constructor
  · rintro ⟨traceCode, htrace, hlen, hzero, hstep, hlast⟩
    let trace := decode traceCode
    have hcode : encode trace = traceCode := encode_decode htrace
    rw [← hcode] at hlen hzero hstep hlast
    have hlen' : trace.length = xs.length + 1 := by simpa using hlen
    refine ⟨trace, hlen', ?_, ?_, ?_⟩
    · have hpos : 0 < trace.length := by omega
      calc
        trace.getD 0 0 = znth (encode trace) 0 :=
          (aggregate_znth_encode_eq_getD trace hpos).symm
        _ = unit := hzero
    · intro i hi
      have hiTrace : i < trace.length := by omega
      have hiTrace1 : i + 1 < trace.length := by omega
      calc
        trace.getD (i + 1) 0 = znth (encode trace) (i + 1) :=
          (aggregate_znth_encode_eq_getD trace hiTrace1).symm
        _ = op (znth (encode trace) i) (znth (encode xs) i) :=
          hstep i (by simpa using hi)
        _ = op (trace.getD i 0) (xs.getD i 0) := by
          rw [aggregate_znth_encode_eq_getD trace hiTrace,
            aggregate_znth_encode_eq_getD xs hi]
    · have hlastIndex : xs.length < trace.length := by omega
      calc
        trace.getD xs.length 0 = znth (encode trace) xs.length :=
          (aggregate_znth_encode_eq_getD trace hlastIndex).symm
        _ = p := by simpa using hlast
  · rintro ⟨trace, hlen, hzero, hstep, hlast⟩
    refine ⟨encode trace, encode_valid trace, by simpa using hlen, ?_, ?_, ?_⟩
    · have hpos : 0 < trace.length := by omega
      calc
        znth (encode trace) 0 = trace.getD 0 0 :=
          aggregate_znth_encode_eq_getD trace hpos
        _ = unit := hzero
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      have hiTrace : i < trace.length := by omega
      have hiTrace1 : i + 1 < trace.length := by omega
      calc
        znth (encode trace) (i + 1) = trace.getD (i + 1) 0 :=
          aggregate_znth_encode_eq_getD trace hiTrace1
        _ = op (trace.getD i 0) (xs.getD i 0) := hstep i hi'
        _ = op (znth (encode trace) i) (znth (encode xs) i) := by
          rw [aggregate_znth_encode_eq_getD trace hiTrace,
            aggregate_znth_encode_eq_getD xs hi']
    · have hlastIndex : xs.length < trace.length := by omega
      calc
        znth (encode trace) (lh (encode xs)) =
            znth (encode trace) xs.length := by simp
        _ = trace.getD xs.length 0 :=
          aggregate_znth_encode_eq_getD trace hlastIndex
        _ = p := hlast

@[simp] theorem sumElements_encode_iff_sum (p : ℕ) (xs : List ℕ) :
    SumElements p (encode xs) ↔ xs.sum = p := by
  rw [SumElements]
  simp only [encode_valid, true_and]
  rw [coded_runningAggregate_iff 0 (· + ·),
    exists_runningAggregateTrace_iff_foldl]
  simp only [List.sum_eq_foldl_nat]

@[simp] theorem productElements_encode_iff_prod (p : ℕ) (xs : List ℕ) :
    ProductElements p (encode xs) ↔ xs.prod = p := by
  rw [ProductElements]
  simp only [encode_valid, true_and]
  rw [coded_runningAggregate_iff 1 (· * ·),
    exists_runningAggregateTrace_iff_foldl]
  simp only [List.prod_eq_foldl_nat]

theorem sumElements_existsUnique (xs : List ℕ) :
    ∃! p, SumElements p (encode xs) := by
  exact ⟨xs.sum, (sumElements_encode_iff_sum xs.sum xs).mpr rfl,
    fun p hp ↦ (sumElements_encode_iff_sum p xs).mp hp |>.symm⟩

theorem productElements_existsUnique (xs : List ℕ) :
    ∃! p, ProductElements p (encode xs) := by
  exact ⟨xs.prod, (productElements_encode_iff_prod xs.prod xs).mpr rfl,
    fun p hp ↦ (productElements_encode_iff_prod p xs).mp hp |>.symm⟩

/-- Sum is total and single-valued on every valid natural-number code. -/
theorem sumElements_existsUnique_of_valid {v : ℕ} (hv : Seq v) :
    ∃! p, SumElements p v := by
  have hcode : encode (decode v) = v := encode_decode hv
  simpa only [hcode] using sumElements_existsUnique (decode v)

/-- Product is total and single-valued on every valid natural-number code. -/
theorem productElements_existsUnique_of_valid {v : ℕ} (hv : Seq v) :
    ∃! p, ProductElements p v := by
  have hcode : encode (decode v) = v := encode_decode hv
  simpa only [hcode] using productElements_existsUnique (decode v)

/-! ### Extrema -/

@[simp] theorem greatest_encode_iff (m : ℕ) (xs : List ℕ) :
    Greatest m (encode xs) ↔ m ∈ xs ∧ ∀ x ∈ xs, x ≤ m := by
  constructor
  · rintro ⟨-, i, hi, him, hall⟩
    have hi' : i < xs.length := by simpa using hi
    let ii : Fin xs.length := ⟨i, hi'⟩
    have hget : xs.get ii = m := by
      calc
        xs.get ii = znth (encode xs) i := (encode_nth xs ii).symm
        _ = m := him
    refine ⟨List.mem_iff_get.mpr ⟨ii, hget⟩, ?_⟩
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨j, hjx⟩
    have hj := hall (j : ℕ) (by simpa using j.isLt)
    rw [LO.FirstOrder.Arithmetic.le_def, encode_nth xs j] at hj
    have hle : xs.get j ≤ m := hj.elim Nat.le_of_eq Nat.le_of_lt
    simpa only [hjx] using hle
  · rintro ⟨hmem, hall⟩
    rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
    refine ⟨encode_valid xs, i, by simpa using i.isLt, ?_, ?_⟩
    · simpa only [encode_nth xs i, hi]
    · intro j hj
      have hj' : j < xs.length := by simpa using hj
      have hle := hall xs[j] (List.getElem_mem hj')
      rw [aggregate_znth_encode_eq_getD xs hj', List.getD_eq_getElem xs 0 hj',
        LO.FirstOrder.Arithmetic.le_def]
      exact (Nat.lt_or_eq_of_le hle).elim Or.inr Or.inl

@[simp] theorem least_encode_iff (m : ℕ) (xs : List ℕ) :
    Least m (encode xs) ↔ m ∈ xs ∧ ∀ x ∈ xs, m ≤ x := by
  constructor
  · rintro ⟨-, i, hi, him, hall⟩
    have hi' : i < xs.length := by simpa using hi
    let ii : Fin xs.length := ⟨i, hi'⟩
    have hget : xs.get ii = m := by
      calc
        xs.get ii = znth (encode xs) i := (encode_nth xs ii).symm
        _ = m := him
    refine ⟨List.mem_iff_get.mpr ⟨ii, hget⟩, ?_⟩
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨j, hjx⟩
    have hj := hall (j : ℕ) (by simpa using j.isLt)
    rw [LO.FirstOrder.Arithmetic.le_def, encode_nth xs j] at hj
    have hle : m ≤ xs.get j := hj.elim Nat.le_of_eq Nat.le_of_lt
    simpa only [hjx] using hle
  · rintro ⟨hmem, hall⟩
    rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
    refine ⟨encode_valid xs, i, by simpa using i.isLt, ?_, ?_⟩
    · simpa only [encode_nth xs i, hi]
    · intro j hj
      have hj' : j < xs.length := by simpa using hj
      have hle := hall xs[j] (List.getElem_mem hj')
      rw [aggregate_znth_encode_eq_getD xs hj', List.getD_eq_getElem xs 0 hj',
        LO.FirstOrder.Arithmetic.le_def]
      exact (Nat.lt_or_eq_of_le hle).elim Or.inr Or.inl

/-- Every nonempty ordinary list has an entry which realizes `Greatest`. -/
private theorem greatest_exists_cons (x : ℕ) (xs : List ℕ) :
    ∃ m, Greatest m (encode (x :: xs)) := by
  induction xs generalizing x with
  | nil =>
      exact ⟨x, (greatest_encode_iff x [x]).mpr (by simp)⟩
  | cons y ys ih =>
      rcases ih y with ⟨m, hm⟩
      have hm' := (greatest_encode_iff m (y :: ys)).mp hm
      by_cases hxm : x ≤ m
      · refine ⟨m, (greatest_encode_iff m (x :: y :: ys)).mpr ⟨by simp [hm'.1], ?_⟩⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxm
        · exact hm'.2 z (by simpa only [List.mem_cons] using hz)
      · have hmx : m ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hxm)
        refine ⟨x, (greatest_encode_iff x (x :: y :: ys)).mpr ⟨by simp, ?_⟩⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Nat.le_refl _
        · exact Nat.le_trans (hm'.2 z (by simpa only [List.mem_cons] using hz)) hmx

/-- Every nonempty ordinary list has an entry which realizes `Least`. -/
private theorem least_exists_cons (x : ℕ) (xs : List ℕ) :
    ∃ m, Least m (encode (x :: xs)) := by
  induction xs generalizing x with
  | nil =>
      exact ⟨x, (least_encode_iff x [x]).mpr (by simp)⟩
  | cons y ys ih =>
      rcases ih y with ⟨m, hm⟩
      have hm' := (least_encode_iff m (y :: ys)).mp hm
      by_cases hmx : m ≤ x
      · refine ⟨m, (least_encode_iff m (x :: y :: ys)).mpr ⟨by simp [hm'.1], ?_⟩⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hmx
        · exact hm'.2 z (by simpa only [List.mem_cons] using hz)
      · have hxm : x ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmx)
        refine ⟨x, (least_encode_iff x (x :: y :: ys)).mpr ⟨by simp, ?_⟩⟩
        intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Nat.le_refl _
        · exact Nat.le_trans hxm (hm'.2 z (by simpa only [List.mem_cons] using hz))

/-- `Greatest` exists on every valid code whose decoded list is nonempty. -/
theorem greatest_exists_of_valid_of_decode_ne_nil {v : ℕ} (hv : Seq v)
    (hne : decode v ≠ []) : ∃ m, Greatest m v := by
  cases hdec : decode v with
  | nil => exact (hne hdec).elim
  | cons x xs =>
      have hcode : encode (x :: xs) = v := by
        simpa only [hdec] using encode_decode hv
      rcases greatest_exists_cons x xs with ⟨m, hm⟩
      exact ⟨m, by simpa only [hcode] using hm⟩

/-- `Least` exists on every valid code whose decoded list is nonempty. -/
theorem least_exists_of_valid_of_decode_ne_nil {v : ℕ} (hv : Seq v)
    (hne : decode v ≠ []) : ∃ m, Least m v := by
  cases hdec : decode v with
  | nil => exact (hne hdec).elim
  | cons x xs =>
      have hcode : encode (x :: xs) = v := by
        simpa only [hdec] using encode_decode hv
      rcases least_exists_cons x xs with ⟨m, hm⟩
      exact ⟨m, by simpa only [hcode] using hm⟩

theorem greatest_functional {m n : ℕ} {xs : List ℕ}
    (hm : Greatest m (encode xs)) (hn : Greatest n (encode xs)) : m = n := by
  have hm' := (greatest_encode_iff m xs).mp hm
  have hn' := (greatest_encode_iff n xs).mp hn
  exact Nat.le_antisymm (hn'.2 m hm'.1) (hm'.2 n hn'.1)

theorem least_functional {m n : ℕ} {xs : List ℕ}
    (hm : Least m (encode xs)) (hn : Least n (encode xs)) : m = n := by
  have hm' := (least_encode_iff m xs).mp hm
  have hn' := (least_encode_iff n xs).mp hn
  exact Nat.le_antisymm (hm'.2 n hn'.1) (hn'.2 m hm'.1)

@[simp] theorem greatest_empty_false (m : ℕ) :
    ¬ Greatest m (encode []) := by
  intro h
  simpa using (greatest_encode_iff m []).mp h |>.1

@[simp] theorem least_empty_false (m : ℕ) :
    ¬ Least m (encode []) := by
  intro h
  simpa using (least_encode_iff m []).mp h |>.1

/-! ### Twice the median -/

/-- Ordinary-list reading of the division-free median relation. -/
def ListTwiceMedian (xs : List ℕ) (m : ℕ) : Prop :=
  ∃ sorted : List ℕ,
    List.Perm sorted xs ∧ sorted.SortedLE ∧
      ((∃ k, xs.length = k + k + 1 ∧
          m = sorted.getD k 0 + sorted.getD k 0) ∨
       ∃ k, xs.length = (k + 1) + (k + 1) ∧
          m = sorted.getD k 0 + sorted.getD (k + 1) 0)

@[simp] theorem twiceMedian_encode_iff (m : ℕ) (xs : List ℕ) :
    TwiceMedian m (encode xs) ↔ ListTwiceMedian xs m := by
  constructor
  · rintro ⟨-, sortedCode, hperm, hsorted, hcase⟩
    let sorted := decode sortedCode
    have hsCode : Seq sortedCode := hperm.1
    have hcode : encode sorted = sortedCode := encode_decode hsCode
    have hp : List.Perm sorted xs := by
      apply (permutation_encode_iff sorted xs).mp
      simpa only [hcode] using hperm
    have hs : sorted.SortedLE := by
      apply (nondecreasing_encode_iff sorted).mp
      simpa only [hcode] using hsorted
    refine ⟨sorted, hp, hs, ?_⟩
    rcases hcase with ⟨k, hlen, hm⟩ | ⟨k, hlen, hm⟩
    · left
      have hlen' : xs.length = k + k + 1 := by simpa using hlen
      have hk : k < sorted.length := by
        have hpermLen := hp.length_eq
        omega
      rw [← hcode, aggregate_znth_encode_eq_getD sorted hk] at hm
      exact ⟨k, hlen', hm⟩
    · right
      have hlen' : xs.length = (k + 1) + (k + 1) := by simpa using hlen
      have hk : k < sorted.length := by
        have hpermLen := hp.length_eq
        omega
      have hk1 : k + 1 < sorted.length := by
        have hpermLen := hp.length_eq
        omega
      rw [← hcode, aggregate_znth_encode_eq_getD sorted hk,
        aggregate_znth_encode_eq_getD sorted hk1] at hm
      exact ⟨k, hlen', hm⟩
  · rintro ⟨sorted, hperm, hsorted, hcase⟩
    refine ⟨encode_valid xs, encode sorted,
      (permutation_encode_iff sorted xs).mpr hperm,
      (nondecreasing_encode_iff sorted).mpr hsorted, ?_⟩
    rcases hcase with ⟨k, hlen, hm⟩ | ⟨k, hlen, hm⟩
    · left
      have hk : k < sorted.length := by
        have := hperm.length_eq
        omega
      refine ⟨k, by simpa only [encode_length] using hlen, ?_⟩
      simpa only [aggregate_znth_encode_eq_getD sorted hk] using hm
    · right
      have hk : k < sorted.length := by
        have := hperm.length_eq
        omega
      have hk1 : k + 1 < sorted.length := by
        have := hperm.length_eq
        omega
      refine ⟨k, by simpa only [encode_length] using hlen, ?_⟩
      simpa only [aggregate_znth_encode_eq_getD sorted hk,
        aggregate_znth_encode_eq_getD sorted hk1] using hm

/-- Any sorted permutation in `ListTwiceMedian` is the canonical insertion sort. -/
theorem listTwiceMedian_iff_insertionSort (xs : List ℕ) (m : ℕ) :
    ListTwiceMedian xs m ↔
      let sorted := xs.insertionSort (· ≤ ·)
      ((∃ k, xs.length = k + k + 1 ∧
          m = sorted.getD k 0 + sorted.getD k 0) ∨
       ∃ k, xs.length = (k + 1) + (k + 1) ∧
          m = sorted.getD k 0 + sorted.getD (k + 1) 0) := by
  dsimp only
  constructor
  · rintro ⟨sorted, hp, hs, hvalue⟩
    have heq : sorted = xs.insertionSort (· ≤ ·) :=
      (hp.trans (List.perm_insertionSort (· ≤ ·) xs).symm).eq_of_pairwise'
        hs.pairwise (List.sortedLE_insertionSort (l := xs)).pairwise
    simpa only [heq] using hvalue
  · intro hvalue
    exact ⟨xs.insertionSort (· ≤ ·),
      List.perm_insertionSort (· ≤ ·) xs,
      List.sortedLE_insertionSort, hvalue⟩

/-- Every nonempty ordinary list has a (necessarily unique) twice-median. -/
private theorem twiceMedian_exists_encode_of_ne_nil (xs : List ℕ)
    (hne : xs ≠ []) : ∃ m, TwiceMedian m (encode xs) := by
  obtain ⟨k, heven | hodd⟩ := Nat.even_or_odd' xs.length
  · cases k with
    | zero =>
        have : xs.length = 0 := by omega
        exact (hne (List.length_eq_zero_iff.mp this)).elim
    | succ q =>
        let sorted := xs.insertionSort (· ≤ ·)
        refine ⟨sorted.getD q 0 + sorted.getD (q + 1) 0, ?_⟩
        apply (twiceMedian_encode_iff _ xs).mpr
        apply (listTwiceMedian_iff_insertionSort xs _).mpr
        dsimp only [sorted]
        exact Or.inr ⟨q, by omega, rfl⟩
  · let sorted := xs.insertionSort (· ≤ ·)
    refine ⟨sorted.getD k 0 + sorted.getD k 0, ?_⟩
    apply (twiceMedian_encode_iff _ xs).mpr
    apply (listTwiceMedian_iff_insertionSort xs _).mpr
    dsimp only [sorted]
    exact Or.inl ⟨k, by omega, rfl⟩

/-- `TwiceMedian` exists on every valid code with a nonempty decoded list. -/
theorem twiceMedian_exists_of_valid_of_decode_ne_nil {v : ℕ} (hv : Seq v)
    (hne : decode v ≠ []) : ∃ m, TwiceMedian m v := by
  have hcode : encode (decode v) = v := encode_decode hv
  rcases twiceMedian_exists_encode_of_ne_nil (decode v) hne with ⟨m, hm⟩
  exact ⟨m, by simpa only [hcode] using hm⟩

theorem twiceMedian_functional {m n : ℕ} {xs : List ℕ}
    (hm : TwiceMedian m (encode xs)) (hn : TwiceMedian n (encode xs)) : m = n := by
  rw [twiceMedian_encode_iff, listTwiceMedian_iff_insertionSort] at hm hn
  rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
    rcases hn with ⟨j, hj, hvalue⟩ | ⟨j, hj, hvalue⟩
  · have : k = j := by omega
    simpa only [this] using hvalue.symm
  · omega
  · omega
  · have : k = j := by omega
    simpa only [this] using hvalue.symm

@[simp] theorem twiceMedian_empty_false (m : ℕ) :
    ¬ TwiceMedian m (encode []) := by
  rw [twiceMedian_encode_iff, listTwiceMedian_iff_insertionSort]
  simp

theorem twiceMedian_odd_example : TwiceMedian 6 (encode [3, 1, 9]) := by
  rw [twiceMedian_encode_iff]
  refine ⟨[1, 3, 9], by decide, by decide, Or.inl ⟨1, by decide, ?_⟩⟩
  decide

theorem twiceMedian_even_example : TwiceMedian 7 (encode [8, 2, 5, 1]) := by
  rw [twiceMedian_encode_iff]
  refine ⟨[1, 2, 5, 8], by decide, by decide, Or.inr ⟨1, by decide, ?_⟩⟩
  decide

/-! ### A unique most frequent entry -/

@[simp] theorem uniqueMode_encode_iff (m : ℕ) (xs : List ℕ) :
    UniqueMode m (encode xs) ↔
      m ∈ xs ∧ ∀ x ∈ xs, x ≠ m → xs.count x < xs.count m := by
  constructor
  · rintro ⟨-, i, hi, him, hall⟩
    have hi' : i < xs.length := by simpa using hi
    let ii : Fin xs.length := ⟨i, hi'⟩
    have hmem : m ∈ xs := by
      have hii : xs.get ii = m := by
        calc
          xs.get ii = znth (encode xs) i := (encode_nth xs ii).symm
          _ = m := him
      exact List.mem_iff_get.mpr ⟨ii, hii⟩
    refine ⟨hmem, ?_⟩
    intro x hx hne
    rcases List.mem_iff_get.mp hx with ⟨j, hjx⟩
    have hj := hall (j : ℕ) (by simpa using j.isLt) (by
      simpa only [encode_nth xs j, hjx] using hne)
    rcases hj with ⟨cm, cx, hcm, hcx, hlt⟩
    have hcm' := (occurrences_encode_iff_count xs cm m).mp hcm
    have hcx' := (occurrences_encode_iff_count xs cx (xs.get j)).mp (by
      simpa only [encode_nth xs j] using hcx)
    rw [hjx] at hcx'
    omega
  · rintro ⟨hmem, hall⟩
    rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
    refine ⟨encode_valid xs, i, by simpa using i.isLt,
      by simpa only [encode_nth xs i, hi], ?_⟩
    intro j hj hjm
    have hj' : j < xs.length := by simpa using hj
    let jj : Fin xs.length := ⟨j, hj'⟩
    have hx : znth (encode xs) j = xs.get jj := by
      simpa only [jj] using encode_nth xs jj
    have hne : xs.get jj ≠ m := by
      intro heq
      exact hjm (hx.trans heq)
    refine ⟨xs.count m, xs.count (xs.get jj),
      (occurrences_encode_iff_count xs (xs.count m) m).mpr rfl, ?_,
      hall (xs.get jj) (List.mem_iff_get.mpr ⟨jj, rfl⟩) hne⟩
    rw [hx]
    exact (occurrences_encode_iff_count xs
      (xs.count (xs.get jj)) (xs.get jj)).mpr rfl

theorem uniqueMode_functional {m n : ℕ} {xs : List ℕ}
    (hm : UniqueMode m (encode xs)) (hn : UniqueMode n (encode xs)) : m = n := by
  have hm' := (uniqueMode_encode_iff m xs).mp hm
  have hn' := (uniqueMode_encode_iff n xs).mp hn
  by_contra hne
  have hmn := hm'.2 n hn'.1 (fun h ↦ hne h.symm)
  have hnm := hn'.2 m hm'.1 hne
  omega

@[simp] theorem uniqueMode_empty_false (m : ℕ) :
    ¬ UniqueMode m (encode []) := by
  intro h
  simpa using (uniqueMode_encode_iff m []).mp h |>.1

theorem uniqueMode_tie_false :
    ¬ UniqueMode 1 (encode [1, 2]) ∧ ¬ UniqueMode 2 (encode [1, 2]) := by
  constructor <;> simp

end PAListCoding
