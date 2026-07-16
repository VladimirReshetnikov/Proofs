import PAListCoding.Predicates
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Lex
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort

/-!
# Agreement with ordinary Lean lists

The representation and formula theorems are stated internally, using only
arithmetic.  This file checks that, in the standard model, those predicates
have their familiar `List Nat` meanings.
-/

namespace PAListCoding

open LO FirstOrder
open LO.FirstOrder.Arithmetic

@[simp] theorem valid_encode_iff (xs : List ℕ) : Seq (encode xs) ↔ True := by
  simp

@[simp] theorem hasLength_encode_iff (xs : List ℕ) (n : ℕ) :
    HasLength (encode xs) n ↔ xs.length = n := by
  simp [HasLength]

/-- The semantic lookup predicate is zero-based on ordinary lists as well. -/
theorem entry_encode_iff (xs : List ℕ) (k m : ℕ) :
    Entry (encode xs) k m ↔
      ∃ hk : k < xs.length, xs.get ⟨k, hk⟩ = m := by
  constructor
  · rintro ⟨-, hk, hkm⟩
    have hk' : k < xs.length := by simpa using hk
    refine ⟨hk', ?_⟩
    calc
      xs.get ⟨k, hk'⟩ = znth (encode xs) k := (encode_nth xs ⟨k, hk'⟩).symm
      _ = m := hkm
  · rintro ⟨hk, hkm⟩
    refine ⟨encode_valid xs, ?_, ?_⟩
    · simpa using hk
    · calc
        znth (encode xs) k = xs.get ⟨k, hk⟩ := encode_nth xs ⟨k, hk⟩
        _ = m := hkm

@[simp] theorem singleton_encode_iff (xs : List ℕ) (m : ℕ) :
    Singleton (encode xs) m ↔ xs = [m] := by
  constructor
  · rintro ⟨-, hlen, hentry⟩
    have hlen' : xs.length = 1 := by simpa using hlen
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen'
    have ha : a = m := by
      calc
        a = znth (encode [a]) 0 := (encode_nth [a] ⟨0, by simp⟩).symm
        _ = m := hentry
    simp [ha]
  · rintro rfl
    refine ⟨encode_valid [m], by simp, ?_⟩
    simpa using encode_nth [m] ⟨0, by simp⟩

@[simp] theorem concat_encode_iff (xs ys zs : List ℕ) :
    Concat (encode xs) (encode ys) (encode zs) ↔ xs = ys ++ zs := by
  constructor
  · rintro ⟨-, -, -, hlen, hleft, hright⟩
    have hlen' : xs.length = (ys ++ zs).length := by simpa using hlen
    apply List.ext_get hlen'
    intro i hix hiappend
    by_cases hiy : i < ys.length
    · have he := hleft i (by simpa using hiy)
      have hx := encode_nth xs ⟨i, hix⟩
      have hy := encode_nth ys ⟨i, hiy⟩
      calc
        xs.get ⟨i, hix⟩ = znth (encode xs) i := hx.symm
        _ = znth (encode ys) i := he
        _ = ys.get ⟨i, hiy⟩ := hy
        _ = (ys ++ zs).get ⟨i, hiappend⟩ := by
          simpa using (List.getElem_append_left (as := ys) (bs := zs) hiy).symm
    · have hyi : ys.length ≤ i := Nat.le_of_not_gt hiy
      have hiz : i - ys.length < zs.length := by
        have : i < ys.length + zs.length := by simpa using hiappend
        omega
      have he := hright (i - ys.length) (by simpa using hiz)
      have hx := encode_nth xs ⟨i, hix⟩
      have hz := encode_nth zs ⟨i - ys.length, hiz⟩
      have hidx : ys.length + (i - ys.length) = i := Nat.add_sub_of_le hyi
      calc
        xs.get ⟨i, hix⟩ = znth (encode xs) i := hx.symm
        _ = znth (encode xs) (lh (encode ys) + (i - ys.length)) := by
          simp only [encode_length, hidx]
        _ = znth (encode zs) (i - ys.length) := he
        _ = zs.get ⟨i - ys.length, hiz⟩ := hz
        _ = (ys ++ zs).get ⟨i, hiappend⟩ := by
          simpa using (List.getElem_append_right (as := ys) (bs := zs) hyi).symm
  · rintro rfl
    refine ⟨encode_valid (ys ++ zs), encode_valid ys, encode_valid zs,
      by simp, ?_, ?_⟩
    · intro i hi
      have hi' : i < ys.length := by simpa using hi
      have hiappend : i < (ys ++ zs).length := by
        simp only [List.length_append]
        omega
      calc
        znth (encode (ys ++ zs)) i = (ys ++ zs).get ⟨i, hiappend⟩ :=
          encode_nth (ys ++ zs) ⟨i, hiappend⟩
        _ = ys.get ⟨i, hi'⟩ := by
          simpa using List.getElem_append_left (as := ys) (bs := zs) hi'
        _ = znth (encode ys) i := (encode_nth ys ⟨i, hi'⟩).symm
    · intro j hj
      have hj' : j < zs.length := by simpa using hj
      have hsum : ys.length + j < (ys ++ zs).length := by simp [hj']
      calc
        znth (encode (ys ++ zs)) (lh (encode ys) + j) =
            znth (encode (ys ++ zs)) (ys.length + j) := by simp
        _ = (ys ++ zs).get ⟨ys.length + j, hsum⟩ :=
          encode_nth (ys ++ zs) ⟨ys.length + j, hsum⟩
        _ = zs.get ⟨j, hj'⟩ := by
          simpa using List.getElem_append_right (as := ys) (bs := zs)
            (i := ys.length + j) (Nat.le_add_right ys.length j)
        _ = znth (encode zs) j := (encode_nth zs ⟨j, hj'⟩).symm

@[simp] theorem encode_nil : encode ([] : List ℕ) = (∅ : ℕ) := by
  simpa [encode, Matrix.empty_eq] using (vecToSeq_nil (V := ℕ))

@[simp] theorem decode_empty : decode (∅ : ℕ) = [] := by
  rw [← encode_nil]
  exact decode_encode []

theorem concat_iff_decode (v t u : ℕ) :
    Concat v t u ↔
      Seq v ∧ Seq t ∧ Seq u ∧ decode v = decode t ++ decode u := by
  constructor
  · intro h
    have hv := h.1
    have ht := h.2.1
    have hu := h.2.2.1
    refine ⟨hv, ht, hu, ?_⟩
    apply (concat_encode_iff (decode v) (decode t) (decode u)).mp
    simpa only [encode_decode hv, encode_decode ht, encode_decode hu] using h
  · rintro ⟨hv, ht, hu, hconcat⟩
    have hc := (concat_encode_iff (decode v) (decode t) (decode u)).mpr hconcat
    simpa only [encode_decode hv, encode_decode ht, encode_decode hu] using hc

@[simp] theorem concatAll_encode_iff_flatten (flat : List ℕ)
    (xss : List (List ℕ)) :
    ConcatAll (encode flat) (encode (xss.map encode)) ↔
      flat = xss.flatten := by
  constructor
  · rintro ⟨-, -, -, traceCode, -, -, hzero, hstep, hlast⟩
    have hprefix : ∀ i, i < xss.length + 1 →
        decode (znth traceCode i) = (xss.take i).flatten := by
      intro i hi
      induction i with
      | zero => simpa [hzero]
      | succ i ih =>
          have hix : i < xss.length := by omega
          have hc := (concat_iff_decode _ _ _).mp
            (hstep i (by simpa using hix))
          have hrec := hc.2.2.2
          have hw := encode_nth (xss.map encode) ⟨i, by simpa using hix⟩
          have hw' : decode (znth (encode (xss.map encode)) i) = xss[i] := by
            rw [hw]
            simp
          rw [ih (by omega), hw'] at hrec
          rw [List.take_add_one, List.getElem?_eq_getElem hix]
          rw [List.flatten_append, Option.toList_some, List.flatten_singleton]
          exact hrec
    have hp := hprefix xss.length (Nat.lt_succ_self _)
    rw [List.take_length] at hp
    have hend : decode (znth traceCode (lh (encode (xss.map encode)))) = flat := by
      rw [hlast]
      simp
    have hend' : decode (znth traceCode xss.length) = flat := by simpa using hend
    exact hend'.symm.trans hp
  · intro hflat
    let traceCodes : List ℕ :=
      List.ofFn fun i : Fin (xss.length + 1) ↦ encode (xss.take i).flatten
    refine ⟨encode_valid flat, encode_valid (xss.map encode), ?_,
      encode traceCodes, encode_valid traceCodes, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < xss.length := by simpa using hi
      have hw : znth (encode (xss.map encode)) i = encode xss[i] := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
          _ = encode xss[i] := by simp
      rw [hw]
      exact encode_valid xss[i]
    · simp [traceCodes]
    · have hzero := encode_nth traceCodes ⟨0, by simp [traceCodes]⟩
      simpa [traceCodes] using hzero
    · intro i hi
      have hi' : i < xss.length := by simpa using hi
      have hiTrace : i < traceCodes.length := by
        simp only [traceCodes, List.length_ofFn]
        omega
      have hiTrace1 : i + 1 < traceCodes.length := by simp [traceCodes]; omega
      have hn := encode_nth traceCodes ⟨i + 1, hiTrace1⟩
      have hc := encode_nth traceCodes ⟨i, hiTrace⟩
      have hn' : znth (encode traceCodes) (i + 1) =
          encode (xss.take (i + 1)).flatten := by
        calc
          znth (encode traceCodes) (i + 1) = traceCodes.get ⟨i + 1, hiTrace1⟩ := hn
          _ = encode (xss.take (i + 1)).flatten := by simp [traceCodes]
      have hc' : znth (encode traceCodes) i = encode (xss.take i).flatten := by
        calc
          znth (encode traceCodes) i = traceCodes.get ⟨i, hiTrace⟩ := hc
          _ = encode (xss.take i).flatten := by
            simpa [traceCodes] using
              List.get_ofFn (fun j : Fin (xss.length + 1) ↦
                encode (xss.take j).flatten) ⟨i, hiTrace⟩
      have hw' : znth (encode (xss.map encode)) i = encode xss[i] := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
          _ = encode xss[i] := by simp
      rw [hn', hc', hw']
      apply (concat_encode_iff _ _ _).mpr
      rw [List.take_add_one, List.getElem?_eq_getElem hi']
      rw [List.flatten_append, Option.toList_some, List.flatten_singleton]
    · have hlastTrace : xss.length < traceCodes.length := by simp [traceCodes]
      have hn := encode_nth traceCodes ⟨xss.length, hlastTrace⟩
      have hn' : znth (encode traceCodes) xss.length =
          encode (xss.take xss.length).flatten := by
        calc
          znth (encode traceCodes) xss.length =
              traceCodes.get ⟨xss.length, hlastTrace⟩ := hn
          _ = encode (xss.take xss.length).flatten := by
            simpa [traceCodes] using
              List.get_ofFn (fun j : Fin (xss.length + 1) ↦
                encode (xss.take j).flatten) ⟨xss.length, hlastTrace⟩
      have hidx : lh (encode (xss.map encode)) = xss.length := by simp
      rw [hidx, hn', List.take_length]
      exact (congrArg encode hflat).symm

@[simp] theorem noDuplicates_encode_iff (xs : List ℕ) :
    NoDuplicates (encode xs) ↔ xs.Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_get]
  constructor
  · rintro ⟨-, h⟩ i j hij
    have hn := h (i : ℕ) (by simpa using i.isLt) (j : ℕ)
      (by simpa using j.isLt) (by simpa using hij)
    simpa only [encode_nth xs i, encode_nth xs j] using hn
  · intro h
    refine ⟨encode_valid xs, ?_⟩
    intro i hi j hj hij
    have hn := h ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ (by simpa using hij)
    simpa only [encode_nth xs ⟨i, by simpa using hi⟩,
      encode_nth xs ⟨j, by simpa using hj⟩] using hn

@[simp] theorem permutation_encode_iff (xs ys : List ℕ) :
    PAListCoding.Permutation (encode xs) (encode ys) ↔ List.Perm xs ys := by
  constructor
  · rintro ⟨-, -, hlen, indices, hnodup, hilen, hentries⟩
    have hlen' : xs.length = ys.length := by simpa using hlen
    let f : Fin xs.length → Fin ys.length := fun i ↦
      ⟨znth indices i, by
        have he := (hentries (i : ℕ) (by simpa using i.isLt)).1
        simpa using he⟩
    have hfinj : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with hijlt | hjilt
      · have hd := hnodup.2 (i : ℕ) (by simpa [hilen] using i.isLt)
          (j : ℕ) (by simpa [hilen] using j.isLt) (by simpa using hijlt)
        exact hd (Fin.ext_iff.mp hij)
      · have hd := hnodup.2 (j : ℕ) (by simpa [hilen] using j.isLt)
          (i : ℕ) (by simpa [hilen] using i.isLt) (by simpa using hjilt)
        exact hd (Fin.ext_iff.mp hij).symm
    let σ : Equiv.Perm (Fin xs.length) := by
      let f' : Fin xs.length → Fin xs.length := fun i ↦
        Fin.cast hlen'.symm (f i)
      have hf'inj : Function.Injective f' := by
        intro i j hij
        apply hfinj
        exact Fin.cast_injective hlen'.symm hij
      exact Equiv.ofBijective f' hf'inj.bijective_of_finite
    have hsigma (i : Fin xs.length) :
        (σ i : ℕ) = (f i : ℕ) := by
      change ((Fin.cast hlen'.symm (f i) : Fin xs.length) : ℕ) = (f i : ℕ)
      rfl
    have hpoint (i : Fin xs.length) : xs.get i = ys.get (f i) := by
      have he := (hentries (i : ℕ) (by simpa using i.isLt)).2
      calc
        xs.get i = znth (encode xs) i := (encode_nth xs i).symm
        _ = znth (encode ys) (znth indices i) := he
        _ = ys.get (f i) := encode_nth ys (f i)
    let g : Fin xs.length → ℕ := fun i ↦ ys.get (Fin.cast hlen' i)
    have hgf (i : Fin xs.length) : g (σ i) = ys.get (f i) := by
      apply congrArg ys.get
      apply Fin.ext
      simpa [g] using hsigma i
    have hgenerated : List.ofFn (g ∘ σ) = xs := by
      apply List.ext_getElem
      · simp
      · intro i hi₁ hi₂
        let ii : Fin xs.length := ⟨i, by simpa using hi₂⟩
        have hp := hpoint ii
        have helem : (List.ofFn (g ∘ σ)).get ⟨i, hi₁⟩ = g (σ ii) := by
          simpa [ii] using List.get_ofFn (g ∘ σ) ⟨i, hi₁⟩
        change (List.ofFn (g ∘ σ)).get ⟨i, hi₁⟩ = xs.get ⟨i, hi₂⟩
        rw [helem, hgf]
        simpa [ii] using hp.symm
    have hsource : List.ofFn g = ys := by
      calc
        List.ofFn g = List.ofFn ys.get :=
          (List.ofFn_congr hlen'.symm ys.get).symm
        _ = ys := List.ofFn_get ys
    have hp := σ.ofFn_comp_perm g
    rw [hgenerated, hsource] at hp
    exact hp
  · intro hperm
    let indices : List ℕ :=
      List.ofFn fun i : Fin xs.length ↦ (hperm.idxBij i : ℕ)
    refine ⟨encode_valid xs, encode_valid ys, by simpa using hperm.length_eq,
      encode indices, ?_, ?_, ?_⟩
    · rw [noDuplicates_encode_iff, List.nodup_ofFn]
      intro i j hij
      apply hperm.idxBij_injective
      exact Fin.ext hij
    · simp [indices]
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      let ii : Fin xs.length := ⟨i, hi'⟩
      have hindex : znth (encode indices) i = (hperm.idxBij ii : ℕ) := by
        simpa [indices, ii] using encode_nth indices ⟨i, by simp [indices, hi']⟩
      constructor
      · rw [hindex]
        simpa using (hperm.idxBij ii).isLt
      · rw [hindex, encode_nth xs ii, encode_nth ys (hperm.idxBij ii)]
        exact (hperm.getElem_idxBij_eq_getElem ii).symm

/-! ### Running counts -/

/-- The ordinary-list version of the coded running-count witness. -/
def CountingTrace (xs trace : List ℕ) (n m : ℕ) : Prop :=
  trace.length = xs.length + 1 ∧ trace.getD 0 0 = 0 ∧
    (∀ i < xs.length,
      (xs.getD i 0 = m ∧ trace.getD (i + 1) 0 = trace.getD i 0 + 1) ∨
      (xs.getD i 0 ≠ m ∧ trace.getD (i + 1) 0 = trace.getD i 0)) ∧
    trace.getD xs.length 0 = n

theorem exists_countingTrace_iff_count (xs : List ℕ) (n m : ℕ) :
    (∃ trace, CountingTrace xs trace n m) ↔ xs.count m = n := by
  constructor
  · rintro ⟨trace, hlen, hzero, hstep, hlast⟩
    have hprefix : ∀ i, i < xs.length + 1 →
        trace.getD i 0 = (xs.take i).count m := by
      intro i hi
      induction i with
      | zero => simpa using hzero
      | succ i ih =>
          have hix : i < xs.length := by omega
          have ih' := ih (by omega)
          have hxget : xs.getD i 0 = xs[i] := List.getD_eq_getElem xs 0 hix
          rcases hstep i hix with hmatch | hne
          · have hxm : xs[i] = m := hxget.symm.trans hmatch.1
            rw [hmatch.2, ih', List.take_add_one,
              List.getElem?_eq_getElem hix, List.count_append]
            simp [hxm]
          · have hxne : xs[i] ≠ m := by
              intro hxm
              exact hne.1 (hxget.trans hxm)
            rw [hne.2, ih', List.take_add_one,
              List.getElem?_eq_getElem hix, List.count_append]
            simp [hxne]
    have hp := hprefix xs.length (Nat.lt_succ_self _)
    rw [List.take_length] at hp
    exact hp.symm.trans hlast
  · intro hcount
    let trace : List ℕ :=
      List.ofFn fun i : Fin (xs.length + 1) ↦ (xs.take i).count m
    have hget (i : ℕ) (hi : i < xs.length + 1) :
        trace.getD i 0 = (xs.take i).count m := by
      rw [List.getD_eq_getElem trace 0 (by simpa [trace] using hi)]
      simpa [trace] using List.getElem_ofFn
        (f := fun i : Fin (xs.length + 1) ↦ (xs.take i).count m)
        (by simpa [trace] using hi)
    refine ⟨trace, by simp [trace], by simpa using hget 0 (by omega), ?_, ?_⟩
    · intro i hi
      have hi1 : i + 1 < xs.length + 1 := by omega
      have hxget : xs.getD i 0 = xs[i] := List.getD_eq_getElem xs 0 hi
      by_cases hxm : xs[i] = m
      · left
        constructor
        · exact hxget.trans hxm
        · rw [hget (i + 1) hi1, hget i (by omega), List.take_add_one,
            List.getElem?_eq_getElem hi, List.count_append]
          simp [hxm]
      · right
        constructor
        · intro hgetm
          exact hxm (hxget.symm.trans hgetm)
        · rw [hget (i + 1) hi1, hget i (by omega), List.take_add_one,
            List.getElem?_eq_getElem hi, List.count_append]
          simp [hxm]
    · simpa [List.take_length, hcount] using hget xs.length (Nat.lt_succ_self _)

private theorem znth_encode_eq_getD (xs : List ℕ) {i : ℕ} (hi : i < xs.length) :
    znth (encode xs) i = xs.getD i 0 := by
  rw [List.getD_eq_getElem xs 0 hi]
  exact encode_nth xs ⟨i, hi⟩

theorem occurrences_encode_iff_countingTrace (xs : List ℕ) (n m : ℕ) :
    Occurrences (encode xs) n m ↔ ∃ trace, CountingTrace xs trace n m := by
  constructor
  · rintro ⟨-, traceCode, htrace, hlen, hzero, hstep, hlast⟩
    let trace := decode traceCode
    have hcode : encode trace = traceCode := encode_decode htrace
    rw [← hcode] at hlen hzero hstep hlast
    have hlen' : trace.length = xs.length + 1 := by simpa using hlen
    refine ⟨trace, hlen', ?_, ?_, ?_⟩
    · have hpos : 0 < trace.length := by omega
      calc
        trace.getD 0 0 = znth (encode trace) 0 :=
          (znth_encode_eq_getD trace hpos).symm
        _ = 0 := hzero
    · intro i hi
      have hiCode : i < lh (encode xs) := by simpa using hi
      have hiTrace : i < trace.length := by omega
      have hiTrace1 : i + 1 < trace.length := by omega
      have hx := znth_encode_eq_getD xs hi
      have ht := znth_encode_eq_getD trace hiTrace
      have ht1 := znth_encode_eq_getD trace hiTrace1
      rcases hstep i hiCode with hmatch | hne
      · left
        constructor
        · exact hx.symm.trans hmatch.1
        · calc
            trace.getD (i + 1) 0 = znth (encode trace) (i + 1) := ht1.symm
            _ = znth (encode trace) i + 1 := hmatch.2
            _ = trace.getD i 0 + 1 := by rw [ht]
      · right
        constructor
        · intro hget
          exact hne.1 (hx.trans hget)
        · calc
            trace.getD (i + 1) 0 = znth (encode trace) (i + 1) := ht1.symm
            _ = znth (encode trace) i := hne.2
            _ = trace.getD i 0 := ht
    · have hlastIndex : xs.length < trace.length := by omega
      calc
        trace.getD xs.length 0 = znth (encode trace) xs.length :=
          (znth_encode_eq_getD trace hlastIndex).symm
        _ = n := by simpa using hlast
  · rintro ⟨trace, hlen, hzero, hstep, hlast⟩
    refine ⟨encode_valid xs, encode trace, encode_valid trace, ?_, ?_, ?_, ?_⟩
    · simpa using hlen
    · have hpos : 0 < trace.length := by omega
      calc
        znth (encode trace) 0 = trace.getD 0 0 := znth_encode_eq_getD trace hpos
        _ = 0 := hzero
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      have hiTrace : i < trace.length := by omega
      have hiTrace1 : i + 1 < trace.length := by omega
      have hx := znth_encode_eq_getD xs hi'
      have ht := znth_encode_eq_getD trace hiTrace
      have ht1 := znth_encode_eq_getD trace hiTrace1
      rcases hstep i hi' with hmatch | hne
      · left
        constructor
        · exact hx.trans hmatch.1
        · calc
            znth (encode trace) (i + 1) = trace.getD (i + 1) 0 := ht1
            _ = trace.getD i 0 + 1 := hmatch.2
            _ = znth (encode trace) i + 1 := by rw [ht]
      · right
        constructor
        · intro hznth
          exact hne.1 (hx.symm.trans hznth)
        · calc
            znth (encode trace) (i + 1) = trace.getD (i + 1) 0 := ht1
            _ = trace.getD i 0 := hne.2
            _ = znth (encode trace) i := ht.symm
    · have hlastIndex : xs.length < trace.length := by omega
      calc
        znth (encode trace) (lh (encode xs)) = znth (encode trace) xs.length := by simp
        _ = trace.getD xs.length 0 := znth_encode_eq_getD trace hlastIndex
        _ = n := hlast

@[simp] theorem occurrences_encode_iff_count (xs : List ℕ) (n m : ℕ) :
    Occurrences (encode xs) n m ↔ xs.count m = n := by
  rw [occurrences_encode_iff_countingTrace, exists_countingTrace_iff_count]

@[simp] theorem nondecreasing_encode_iff (xs : List ℕ) :
    Nondecreasing (encode xs) ↔ xs.SortedLE := by
  rw [List.sortedLE_iff_isChain, List.isChain_iff_getElem]
  constructor
  · rintro ⟨-, h⟩ i hi
    have hi0 : i < lh (encode xs) := by
      simpa using (Nat.lt_trans (Nat.lt_succ_self i) hi)
    have hi1 : i + 1 < lh (encode xs) := by simpa using hi
    have hn := h i hi0 hi1
    let ii : Fin xs.length := ⟨i, Nat.lt_trans (Nat.lt_succ_self i) hi⟩
    let ii1 : Fin xs.length := ⟨i + 1, hi⟩
    have hzi : znth (encode xs) i = xs.get ii := by
      simpa [ii] using encode_nth xs ii
    have hzi1 : znth (encode xs) (i + 1) = xs.get ii1 := by
      simpa [ii1] using encode_nth xs ii1
    rw [LO.FirstOrder.Arithmetic.le_def, hzi, hzi1] at hn
    have hle : Nat.le
        (xs.get ii) (xs.get ii1) :=
      hn.elim (fun heq ↦ Nat.le_of_eq heq) Nat.le_of_lt
    simpa using hle
  · intro h
    refine ⟨encode_valid xs, ?_⟩
    intro i hi hnext
    have hi' : i < xs.length := by simpa using hi
    have hnext' : i + 1 < xs.length := by simpa using hnext
    have hn := h i hnext'
    let ii : Fin xs.length := ⟨i, hi'⟩
    let ii1 : Fin xs.length := ⟨i + 1, hnext'⟩
    have hn' : Nat.le (xs.get ii) (xs.get ii1) := by
      simpa using hn
    have hzi : znth (encode xs) i = xs.get ii := by
      simpa [ii] using encode_nth xs ii
    have hzi1 : znth (encode xs) (i + 1) = xs.get ii1 := by
      simpa [ii1] using encode_nth xs ii1
    rw [LO.FirstOrder.Arithmetic.le_def, hzi, hzi1]
    rcases Nat.lt_or_eq_of_le hn' with hlt | heq
    · exact Or.inr hlt
    · exact Or.inl heq

@[simp] theorem substring_encode_iff (xs ys : List ℕ) :
    Substring (encode xs) (encode ys) ↔ xs <:+: ys := by
  rw [List.infix_iff_getElem?]
  constructor
  · rintro ⟨-, -, offset, -, hfit, hentries⟩
    have hfitOr : offset + xs.length = ys.length ∨ offset + xs.length < ys.length := by
      simpa [LO.FirstOrder.Arithmetic.le_def] using hfit
    have hfit' : xs.length + offset ≤ ys.length := by omega
    refine ⟨offset, hfit', ?_⟩
    intro i hi
    have hiCode : i < lh (encode xs) := by simpa using hi
    have hij : i + offset < ys.length := by omega
    have hx := encode_nth xs ⟨i, hi⟩
    have hy := encode_nth ys ⟨i + offset, hij⟩
    have he := hentries i hiCode
    have hval : ys.get ⟨i + offset, hij⟩ = xs.get ⟨i, hi⟩ := by
      calc
        ys.get ⟨i + offset, hij⟩ = znth (encode ys) (i + offset) := hy.symm
        _ = znth (encode ys) (offset + i) := by rw [Nat.add_comm]
        _ = znth (encode xs) i := he.symm
        _ = xs.get ⟨i, hi⟩ := hx
    rw [List.getElem?_eq_getElem hij]
    simpa using hval
  · rintro ⟨offset, hfit, hentries⟩
    refine ⟨encode_valid xs, encode_valid ys, offset, ?_, ?_, ?_⟩
    · simpa using (show offset < ys.length + 1 by omega)
    · rw [LO.FirstOrder.Arithmetic.le_def]
      have : offset + xs.length ≤ ys.length := by omega
      have hor : offset + xs.length = ys.length ∨ offset + xs.length < ys.length :=
        (Nat.lt_or_eq_of_le this).elim Or.inr Or.inl
      simpa only [encode_length] using hor
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      have hij : i + offset < ys.length := by omega
      have he := hentries i hi'
      rw [List.getElem?_eq_getElem hij] at he
      have hval : ys.get ⟨i + offset, hij⟩ = xs.get ⟨i, hi'⟩ := by
        simpa using he
      calc
        znth (encode xs) i = xs.get ⟨i, hi'⟩ := encode_nth xs ⟨i, hi'⟩
        _ = ys.get ⟨i + offset, hij⟩ := hval.symm
        _ = znth (encode ys) (i + offset) := (encode_nth ys ⟨i + offset, hij⟩).symm
        _ = znth (encode ys) (offset + i) := by rw [Nat.add_comm]

@[simp] theorem increasingIndices_encode_iff (indices : List ℕ) :
    IncreasingIndices (encode indices) ↔ indices.SortedLT := by
  rw [List.sortedLT_iff_pairwise, List.pairwise_iff_get]
  constructor
  · rintro ⟨-, h⟩ i j hij
    have hn := h (i : ℕ) (by simpa using i.isLt) (j : ℕ)
      (by simpa using j.isLt) (by simpa using hij)
    simpa only [encode_nth indices i, encode_nth indices j] using hn
  · intro h
    refine ⟨encode_valid indices, ?_⟩
    intro i hi j hj hij
    have hn := h ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ (by simpa using hij)
    simpa only [encode_nth indices ⟨i, by simpa using hi⟩,
      encode_nth indices ⟨j, by simpa using hj⟩] using hn

@[simp] theorem subsequence_encode_iff (xs ys : List ℕ) :
    Subsequence (encode xs) (encode ys) ↔ List.Sublist xs ys := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  constructor
  · rintro ⟨-, -, indices, hinc, hlen, hentries⟩
    let f : Fin xs.length → Fin ys.length := fun i ↦
      ⟨znth indices i, by
        have he := (hentries (i : ℕ) (by simpa using i.isLt)).1
        simpa using he⟩
    have hfmono : StrictMono f := by
      intro i j hij
      apply Fin.mk_lt_mk.mpr
      exact hinc.2 (i : ℕ) (by simpa [hlen] using i.isLt)
        (j : ℕ) (by simpa [hlen] using j.isLt) (by simpa using hij)
    refine ⟨OrderEmbedding.ofStrictMono f hfmono, ?_⟩
    intro i
    have he := (hentries (i : ℕ) (by simpa using i.isLt)).2
    have hy := encode_nth ys (f i)
    have hx := encode_nth xs i
    calc
      xs.get i = znth (encode xs) i := hx.symm
      _ = znth (encode ys) (znth indices i) := he
      _ = ys.get (f i) := hy
  · rintro ⟨f, hf⟩
    let indices : List ℕ := List.ofFn fun i : Fin xs.length ↦ (f i : ℕ)
    refine ⟨encode_valid xs, encode_valid ys, encode indices, ?_, ?_, ?_⟩
    · rw [increasingIndices_encode_iff]
      have hval : StrictMono (fun i : Fin xs.length ↦ (f i : ℕ)) := by
        intro i j hij
        simpa using f.strictMono hij
      simpa [indices] using hval.sortedLT_ofFn
    · simp [indices]
    · intro i hi
      have hi' : i < xs.length := by simpa using hi
      let ii : Fin xs.length := ⟨i, hi'⟩
      have hindex : znth (encode indices) i = (f ii : ℕ) := by
        simpa [indices, ii] using encode_nth indices ⟨i, by simp [indices, hi']⟩
      constructor
      · rw [hindex]
        simpa using (f ii).isLt
      · rw [hindex, encode_nth xs ii, encode_nth ys (f ii)]
        exact hf ii

/-! ### Lexicographic order and exact permutation enumeration -/

/-- The usual non-strict lexicographic order, written by first difference. -/
def ListLexLE (xs ys : List ℕ) : Prop :=
  (Nat.le xs.length ys.length ∧
      ∀ i < xs.length, xs.getD i 0 = ys.getD i 0) ∨
    ∃ i < xs.length, i < ys.length ∧
      (∀ j < i, xs.getD j 0 = ys.getD j 0) ∧
      xs.getD i 0 < ys.getD i 0

@[simp] theorem lexLE_encode_iff (xs ys : List ℕ) :
    LexLE (encode xs) (encode ys) ↔ ListLexLE xs ys := by
  constructor
  · rintro ⟨-, -, hpref | hdiff⟩
    · left
      have hlenCode := hpref.1
      rw [LO.FirstOrder.Arithmetic.le_def] at hlenCode
      have hlenOr : xs.length = ys.length ∨ xs.length < ys.length := by
        simpa only [encode_length] using hlenCode
      refine ⟨hlenOr.elim Nat.le_of_eq Nat.le_of_lt, ?_⟩
      intro i hi
      have he := hpref.2 i (by simpa using hi)
      calc
        xs.getD i 0 = znth (encode xs) i := (znth_encode_eq_getD xs hi).symm
        _ = znth (encode ys) i := he
        _ = ys.getD i 0 :=
          znth_encode_eq_getD ys
            (Nat.lt_of_lt_of_le hi (hlenOr.elim Nat.le_of_eq Nat.le_of_lt))
    · right
      rcases hdiff with ⟨i, hix, hiy, hbefore, hlt⟩
      have hix' : i < xs.length := by simpa using hix
      have hiy' : i < ys.length := by simpa using hiy
      refine ⟨i, hix', hiy', ?_, ?_⟩
      · intro j hj
        have he := hbefore j (by simpa using hj)
        calc
          xs.getD j 0 = znth (encode xs) j :=
            (znth_encode_eq_getD xs (by omega)).symm
          _ = znth (encode ys) j := he
          _ = ys.getD j 0 := znth_encode_eq_getD ys (by omega)
      · simpa only [znth_encode_eq_getD xs hix',
          znth_encode_eq_getD ys hiy'] using hlt
  · intro h
    refine ⟨encode_valid xs, encode_valid ys, ?_⟩
    rcases h with hpref | hdiff
    · left
      constructor
      · rw [LO.FirstOrder.Arithmetic.le_def]
        have hor : xs.length = ys.length ∨ xs.length < ys.length :=
          (Nat.lt_or_eq_of_le hpref.1).elim Or.inr Or.inl
        simpa only [encode_length] using hor
      · intro i hi
        have hix : i < xs.length := by simpa using hi
        have hiy : i < ys.length := Nat.lt_of_lt_of_le hix hpref.1
        calc
          znth (encode xs) i = xs.getD i 0 := znth_encode_eq_getD xs hix
          _ = ys.getD i 0 := hpref.2 i hix
          _ = znth (encode ys) i := (znth_encode_eq_getD ys hiy).symm
    · right
      rcases hdiff with ⟨i, hix, hiy, hbefore, hlt⟩
      refine ⟨i, by simpa using hix, by simpa using hiy, ?_, ?_⟩
      · intro j hj
        have hj' : j < i := by simpa using hj
        calc
          znth (encode xs) j = xs.getD j 0 :=
            znth_encode_eq_getD xs (by omega)
          _ = ys.getD j 0 := hbefore j hj'
          _ = znth (encode ys) j :=
            (znth_encode_eq_getD ys (by omega)).symm
      · simpa only [znth_encode_eq_getD xs hix,
          znth_encode_eq_getD ys hiy] using hlt

/-- Adjacent ordinary lists are non-decreasing in lexicographic order. -/
def ListLexSorted (xss : List (List ℕ)) : Prop :=
  List.IsChain ListLexLE xss

@[simp] theorem lexSorted_encode_iff (xss : List (List ℕ)) :
    LexSorted (encode (xss.map encode)) ↔ ListLexSorted xss := by
  rw [ListLexSorted, List.isChain_iff_getElem]
  constructor
  · rintro ⟨-, -, hsorted⟩ i hi
    have hi' : i < xss.length := Nat.lt_trans (Nat.lt_succ_self i) hi
    have hi0 : i < lh (encode (xss.map encode)) := by simpa using hi'
    have hi1 : i + 1 < lh (encode (xss.map encode)) := by simpa using hi
    have hs := hsorted i hi0 hi1
    have hc : znth (encode (xss.map encode)) i = encode xss[i] := by
      calc
        znth (encode (xss.map encode)) i =
            (xss.map encode).get ⟨i, by simpa using (by omega : i < xss.length)⟩ :=
          encode_nth (xss.map encode) ⟨i, by simpa using (by omega : i < xss.length)⟩
        _ = encode xss[i] := by simp
    have hn : znth (encode (xss.map encode)) (i + 1) = encode xss[i + 1] := by
      calc
        znth (encode (xss.map encode)) (i + 1) =
            (xss.map encode).get ⟨i + 1, by simpa using hi⟩ :=
          encode_nth (xss.map encode) ⟨i + 1, by simpa using hi⟩
        _ = encode xss[i + 1] := by simp
    rw [hc, hn] at hs
    exact (lexLE_encode_iff xss[i] xss[i + 1]).mp hs
  · intro hsorted
    refine ⟨encode_valid (xss.map encode), ?_, ?_⟩
    · intro i hi
      have hi' : i < xss.length := by simpa using hi
      have hc : znth (encode (xss.map encode)) i = encode xss[i] := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
          _ = encode xss[i] := by simp
      rw [hc]
      exact encode_valid xss[i]
    · intro i hi hi1
      have hi' : i < xss.length := by simpa using hi
      have hi1' : i + 1 < xss.length := by simpa using hi1
      have hs := hsorted i hi1'
      have hc : znth (encode (xss.map encode)) i = encode xss[i] := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
          _ = encode xss[i] := by simp
      have hn : znth (encode (xss.map encode)) (i + 1) = encode xss[i + 1] := by
        calc
          znth (encode (xss.map encode)) (i + 1) =
              (xss.map encode).get ⟨i + 1, by simpa using hi1'⟩ :=
            encode_nth (xss.map encode) ⟨i + 1, by simpa using hi1'⟩
          _ = encode xss[i + 1] := by simp
      rw [hc, hn]
      exact (lexLE_encode_iff xss[i] xss[i + 1]).mpr hs

/--
An exact ordinary-list characterization of the requested final predicate:
distinctness gives “once”, the biconditional gives soundness and completeness,
and `ListLexSorted` supplies the order.
-/
def CompletePermutationList (xss : List (List ℕ)) (base : List ℕ) : Prop :=
  xss.Nodup ∧ ListLexSorted xss ∧
    ∀ ys : List ℕ, ys ∈ xss ↔ List.Perm ys base

@[simp] theorem allPermutations_encode_iff (xss : List (List ℕ))
    (base : List ℕ) :
    AllPermutations (encode (xss.map encode)) (encode base) ↔
      CompletePermutationList xss base := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hn := noDuplicates_encode_iff (xss.map encode) |>.mp
        h.noDuplicates
      exact (List.nodup_map_iff encode_injective).mp hn
    · exact (lexSorted_encode_iff xss).mp h.lexSorted
    · intro ys
      constructor
      · intro hmem
        rcases List.mem_iff_get.mp hmem with ⟨i, hiGet⟩
        have hiCode : (i : ℕ) < lh (encode (xss.map encode)) := by
          simpa using i.isLt
        have hs := h.sound hiCode
        have hc : znth (encode (xss.map encode)) i = encode (xss.get i) := by
          calc
            znth (encode (xss.map encode)) i =
                (xss.map encode).get ⟨i, by simpa using i.isLt⟩ :=
              encode_nth (xss.map encode) ⟨i, by simpa using i.isLt⟩
            _ = encode (xss.get i) := by simp
        rw [hc] at hs
        have hp := (permutation_encode_iff (xss.get i) base).mp hs
        simpa only [hiGet] using hp
      · intro hperm
        have hpCode : PAListCoding.Permutation (encode ys) (encode base) :=
          (permutation_encode_iff ys base).mpr hperm
        rcases h.complete (encode_valid ys) hpCode with ⟨i, hi, heq⟩
        have hi' : i < xss.length := by simpa using hi
        have hc : znth (encode (xss.map encode)) i = encode xss[i] := by
          calc
            znth (encode (xss.map encode)) i =
                (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
              encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
            _ = encode xss[i] := by simp
        rw [hc] at heq
        have : xss[i] = ys := encode_injective heq
        rw [← this]
        exact List.getElem_mem hi'
  · rintro ⟨hnodup, hsorted, hall⟩
    refine ⟨encode_valid (xss.map encode), encode_valid base, ?_, ?_, ?_, ?_⟩
    · rw [noDuplicates_encode_iff, List.nodup_map_iff encode_injective]
      exact hnodup
    · exact (lexSorted_encode_iff xss).mpr hsorted
    · intro i hi
      have hi' : i < xss.length := by simpa using hi
      have hc : znth (encode (xss.map encode)) i = encode xss[i] := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using hi'⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using hi'⟩
          _ = encode xss[i] := by simp
      rw [hc]
      apply (permutation_encode_iff xss[i] base).mpr
      exact (hall xss[i]).mp (List.getElem_mem hi')
    · intro p hp hperm
      have hpCode : encode (decode p) = p := encode_decode hp
      have hdecoded : List.Perm (decode p) base := by
        apply (permutation_encode_iff (decode p) base).mp
        simpa only [hpCode] using hperm
      have hmem := (hall (decode p)).mpr hdecoded
      rcases List.mem_iff_get.mp hmem with ⟨i, hi⟩
      refine ⟨i, by simpa using i.isLt, ?_⟩
      have hc : znth (encode (xss.map encode)) i = encode (xss.get i) := by
        calc
          znth (encode (xss.map encode)) i =
              (xss.map encode).get ⟨i, by simpa using i.isLt⟩ :=
            encode_nth (xss.map encode) ⟨i, by simpa using i.isLt⟩
          _ = encode (xss.get i) := by simp
      rw [hc, hi, hpCode]

end PAListCoding
