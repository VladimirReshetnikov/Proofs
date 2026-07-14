import A158415.Certificates.N14.Order
import A158415.Certificates.N14.Range

/-!
# Size-fourteen certificate for OEIS A158415

This module combines the split size-14 table, order, and range certificates
and proves `a158415 14 = 455`.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private theorem values9_mem_recursiveValueSet_nine (i : Fin 33) :
    values9 i ∈ recursiveValueSet 9 := by
  rw [recursiveValueSet_nine]
  exact ⟨i, rfl⟩

theorem recursiveValueSet_fourteen_unary_subset_range :
    ((fun x : ℝ => Real.sqrt x) '' recursiveValueSet 13) ⊆ Set.range values14 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_thirteen] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values13_mem_range_values14 i

theorem one_add_mem_range_values14_of_mem_recursiveValueSet_twelve {x : Real}
    (hx : x ∈ recursiveValueSet 12) : (Set.range values14) (1 + x) := by
  rw [recursiveValueSet_twelve] at hx
  rcases hx with ⟨i, rfl⟩
  exact one_add_values12_mem_range_values14 i

theorem one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve {n : Nat}
    (hn : n ≤ 12) {x : Real} (hx : x ∈ recursiveValueSet n) :
    (Set.range values14) (1 + x) :=
  one_add_mem_range_values14_of_mem_recursiveValueSet_twelve
    (recursiveValueSet_subset_of_le hn hx)

theorem succ_natCast_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
    {m n : Nat} (hnpos : 0 < n) (hn : n + 2 * m ≤ 12) {x : Real}
    (hx : x ∈ recursiveValueSet n) :
    (Set.range values14) (((m + 1 : Nat) : Real) + x) := by
  have hxpad : (m : Real) + x ∈ recursiveValueSet (n + 2 * m) :=
    natCast_add_mem_recursiveValueSet_add_two_mul (m := m) hnpos hx
  have hrange : (Set.range values14) (1 + ((m : Real) + x)) :=
    one_add_mem_range_values14_of_mem_recursiveValueSet_twelve
      (recursiveValueSet_subset_of_le hn hxpad)
  have heq : (((m + 1 : Nat) : Real) + x) = 1 + ((m : Real) + x) := by
    simp [Nat.cast_add, add_assoc, add_comm]
  rwa [heq]

theorem two_add_mem_range_values14_of_mem_recursiveValueSet_le_ten {n : Nat}
    (hnpos : 0 < n) (hn : n + 2 ≤ 12) {x : Real}
    (hx : x ∈ recursiveValueSet n) : (Set.range values14) (2 + x) := by
  simpa using
    succ_natCast_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
      (m := 1) (n := n) hnpos (by simpa using hn) hx

set_option maxHeartbeats 2000000 in
theorem recursiveValueSet_fourteen_subset_range :
    recursiveValueSet 14 ⊆ Set.range values14 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with hsqrt | hadd
  · exact recursiveValueSet_fourteen_unary_subset_range hsqrt
  · rcases hadd with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 12 := by simpa using hb
      rw [recursiveValueSet_twelve] at hb'
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values12_mem_range_values14 i
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 11 := by simpa using hb
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      exact one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
        (by norm_num) hb'
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 10 := by simpa using hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
          (by norm_num) hb'
      · exact two_add_mem_range_values14_of_mem_recursiveValueSet_le_ten
          (by norm_num) (by norm_num) hb'
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rw [recursiveValueSet_nine] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
          (by norm_num) (values9_mem_recursiveValueSet_nine i)
      · exact sqrt_two_add_values9_mem_range_values14 i
      · exact two_add_mem_range_values14_of_mem_recursiveValueSet_le_ten
          (by norm_num) (by norm_num) (values9_mem_recursiveValueSet_nine i)
    · rw [recursiveValueSet_five_eq_range_values5] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values5_add_values8_mem_range_values14 i j
    · rw [recursiveValueSet_six_eq_range_values6] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values6_add_values7_mem_range_values14 i j
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six_eq_range_values6] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      change (Set.range values14) (values7 i + values6 j)
      simpa [add_comm] using values6_add_values7_mem_range_values14 j i
    · rw [recursiveValueSet_eight] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five_eq_range_values5] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      change (Set.range values14) (values8 i + values5 j)
      simpa [add_comm] using values5_add_values8_mem_range_values14 j i
    · rw [recursiveValueSet_nine] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl | rfl
      · change (Set.range values14) (values9 i + 1)
        simpa [add_comm] using
          one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
            (by norm_num) (values9_mem_recursiveValueSet_nine i)
      · change (Set.range values14) (values9 i + Real.sqrt 2)
        simpa [add_comm] using sqrt_two_add_values9_mem_range_values14 i
      · change (Set.range values14) (values9 i + 2)
        simpa [add_comm] using
          two_add_mem_range_values14_of_mem_recursiveValueSet_le_ten
            (by norm_num) (by norm_num) (values9_mem_recursiveValueSet_nine i)
    · rw [recursiveValueSet_ten] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · change (Set.range values14) (values10 i + 1)
        simpa [add_comm] using
          one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
            (by norm_num) (values10_mem_recursiveValueSet i)
      · change (Set.range values14) (values10 i + 2)
        simpa [add_comm] using
          two_add_mem_range_values14_of_mem_recursiveValueSet_le_ten
            (by norm_num) (by norm_num) (values10_mem_recursiveValueSet i)
    · rw [recursiveValueSet_eleven] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      change (Set.range values14) (values11 i + 1)
      simpa [add_comm] using
        one_add_mem_range_values14_of_mem_recursiveValueSet_le_twelve
          (by norm_num) (values11_mem_recursiveValueSet i)
    · rw [recursiveValueSet_twelve] at ha
      simp [recursiveValueSet] at hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with rfl
      change (Set.range values14) (values12 i + 1)
      simpa [add_comm] using one_add_values12_mem_range_values14 i

theorem recursiveValueSet_fourteen :
    recursiveValueSet 14 = Set.range values14 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_fourteen_subset_range
  · exact values14_range_subset_recursiveValueSet_fourteen

theorem recursiveValueSet_fourteen_ncard :
    (recursiveValueSet 14).ncard = 455 := by
  rw [recursiveValueSet_fourteen, values14_range_ncard]

theorem a158415_fourteen : a158415 14 = 455 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_fourteen_ncard


end Expr

end A158415

end LeanProofs
