import PAListCoding.Predicates
import Mathlib.Data.List.FinRange
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
            (i := ys.length + j) (show ys.length ≤ ys.length + j by omega)
        _ = znth (encode zs) j := (encode_nth zs ⟨j, hj'⟩).symm

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

end PAListCoding
