import LeanProofs.A198683SevenUpper

/-!
# First unconditional bounds on `A198683(8)`

The recurrence presents level `8` as principal powers `x^y` with
`x ∈ valueSet k`, `y ∈ valueSet (8-k)`, and the certified value lists for
levels `1..7` (`mem_valueSet_one` … `mem_valueSet_six`,
`a198683_seven_subset_canonicalReps`) bound the candidate pool by
`Σ_k a(k)·a(8-k) = 34+15+14+9+14+15+34 = 135`.  This module records the
first unconditional bounds at `n = 8`:

* `a198683_eight_le : a198683 8 ≤ 135`;
* `a198683_eight_pos : 1 ≤ a198683 8`.

The heuristically expected value is `77`; closing the gap from `135` to `77`
is the merge/separation campaign described in the wave-5 status ledger
(`Oeis/A198683/reports/wave-5/a198683-formalization-status-and-remaining-work.md`).
-/

namespace LeanProofs

open A198683Support

/-- One split block of level-8 candidates: all `x^y` with `x` drawn from a
level-`k` list and `y` from a level-`(8-k)` list. -/
private noncomputable def block (L L' : List ℂ) : List ℂ :=
  L.flatMap fun x => L'.map fun y => principalPow x y

private theorem mem_block {x y : ℂ} {L L' : List ℂ}
    (hx : x ∈ L) (hy : y ∈ L') :
    principalPow x y ∈ block L L' :=
  List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩

private theorem block_length (L L' : List ℂ) :
    (block L L').length = L.length * L'.length := by
  simp [block, List.length_flatMap]

/-- The certified cover lists for levels `1..7`. -/
private noncomputable def L1 : List ℂ := [Complex.I]
private noncomputable def L2 : List ℂ := [principalPow Complex.I Complex.I]
private noncomputable def L3 : List ℂ :=
  [principalPow Complex.I (principalPow Complex.I Complex.I),
   principalPow (principalPow Complex.I Complex.I) Complex.I]
private noncomputable def L4 : List ℂ := [p4A, p4B, p4C]
private noncomputable def L5 : List ℂ := [p5A, p5B, p5C, p5D, p5E, p5F, p5G]
private noncomputable def L6 : List ℂ :=
  [p6A, p6B, p6C, p6D, p6E, p6F, p6G, p6H, p6I, p6J, p6K, p6L, p6M, p6N, p6O]
private noncomputable def L7 : List ℂ := a198683SevenCanonicalReps

/-- The `135` level-8 candidate values presented by the recurrence. -/
noncomputable def a198683EightCandidates : List ℂ :=
  block L1 L7 ++ (block L2 L6 ++ (block L3 L5 ++ (block L4 L4 ++
    (block L5 L3 ++ (block L6 L2 ++ block L7 L1)))))

theorem a198683EightCandidates_length :
    a198683EightCandidates.length = 135 := by
  simp [a198683EightCandidates, block_length, L1, L2, L3, L4, L5, L6, L7,
    a198683SevenCanonicalReps]

/-- Every level-8 value is one of the `135` recurrence candidates. -/
theorem a198683ValueSet_eight_subset :
    a198683ValueSet 8 ⊆ {z | z ∈ a198683EightCandidates} := by
  intro z hz
  simp only [a198683ValueSet] at hz
  obtain ⟨k, x, hx, y, hy, rfl⟩ := hz
  have hmem7 : ∀ {w : ℂ}, w ∈ a198683ValueSet 7 → w ∈ L7 := by
    intro w hw
    obtain ⟨i, rfl⟩ := a198683_seven_subset_canonicalReps hw
    exact List.get_mem _ i
  fin_cases k <;> norm_num at hx hy ⊢
  · -- split 1 + 7
    rw [mem_valueSet_one] at hx
    subst hx
    exact List.mem_append_left _
      (mem_block (by simp [L1]) (hmem7 hy))
  · -- split 2 + 6
    rw [mem_valueSet_two] at hx
    rw [mem_valueSet_six] at hy
    have hx' : x ∈ L2 := by simp [L2, hx]
    have hy' : y ∈ L6 := by simp [L6]; tauto
    exact List.mem_append_right _ (List.mem_append_left _ (mem_block hx' hy'))
  · -- split 3 + 5
    rw [mem_valueSet_three] at hx
    rw [mem_valueSet_five] at hy
    have hx' : x ∈ L3 := by simp [L3]; tauto
    have hy' : y ∈ L5 := by simp [L5]; tauto
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ (mem_block hx' hy')))
  · -- split 4 + 4
    rw [mem_valueSet_four] at hx
    rw [mem_valueSet_four] at hy
    have hx' : x ∈ L4 := by simp [L4]; tauto
    have hy' : y ∈ L4 := by simp [L4]; tauto
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ (mem_block hx' hy'))))
  · -- split 5 + 3
    rw [mem_valueSet_five] at hx
    rw [mem_valueSet_three] at hy
    have hx' : x ∈ L5 := by simp [L5]; tauto
    have hy' : y ∈ L3 := by simp [L3]; tauto
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ (mem_block hx' hy')))))
  · -- split 6 + 2
    rw [mem_valueSet_six] at hx
    rw [mem_valueSet_two] at hy
    have hx' : x ∈ L6 := by simp [L6]; tauto
    have hy' : y ∈ L2 := by simp [L2, hy]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_left _ (mem_block hx' hy'))))))
  · -- split 7 + 1
    rw [mem_valueSet_one] at hy
    subst hy
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _
          (mem_block (hmem7 hx) (by simp [L1])))))))

/-- The level-8 value set is finite. -/
theorem a198683ValueSet_eight_finite : (a198683ValueSet 8).Finite := by
  classical
  refine Set.Finite.subset (a198683EightCandidates.toFinset.finite_toSet) ?_
  intro z hz
  simpa using a198683ValueSet_eight_subset hz

/-- **First unconditional upper bound at `n = 8`**: the recurrence pool. -/
theorem a198683_eight_le : a198683 8 ≤ 135 := by
  classical
  rw [a198683_eq_valueSet_ncard]
  have hsub : a198683ValueSet 8 ⊆ (a198683EightCandidates.toFinset : Set ℂ) := by
    intro z hz
    simpa using a198683ValueSet_eight_subset hz
  calc (a198683ValueSet 8).ncard
      ≤ (a198683EightCandidates.toFinset : Set ℂ).ncard :=
        Set.ncard_le_ncard hsub (a198683EightCandidates.toFinset.finite_toSet)
    _ = a198683EightCandidates.toFinset.card := Set.ncard_coe_finset _
    _ ≤ a198683EightCandidates.length := a198683EightCandidates.toFinset_card_le
    _ = 135 := a198683EightCandidates_length

/-- The level-8 value set is inhabited (by `p4A ^ p4A`). -/
theorem a198683ValueSet_eight_nonempty : (a198683ValueSet 8).Nonempty := by
  refine ⟨principalPow p4A p4A, ?_⟩
  simp only [a198683ValueSet]
  exact ⟨⟨3, by norm_num⟩, p4A, mem_valueSet_four.2 (Or.inl rfl),
    p4A, mem_valueSet_four.2 (Or.inl rfl), rfl⟩

/-- **Unconditional lower bound at `n = 8`.** -/
theorem a198683_eight_pos : 1 ≤ a198683 8 := by
  rw [a198683_eq_valueSet_ncard]
  have := (a198683ValueSet_eight_nonempty).ncard_pos a198683ValueSet_eight_finite
  omega

end LeanProofs
