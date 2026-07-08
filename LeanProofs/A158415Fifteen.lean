import LeanProofs.A158415FifteenOrder
import LeanProofs.A158415FifteenRangeA
import LeanProofs.A158415FifteenRangeB
import LeanProofs.A158415FifteenRangeC

/-!
# The fifteenth value of OEIS A158415

This module combines the size-15 table, order certificate, and range
inclusion certificates to prove `a158415 15 = 791`.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem recursiveValueSet_fifteen_unary_subset_range :
    ((fun x : Real => Real.sqrt x) '' recursiveValueSet 14) ⊆ Set.range values15 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_fourteen] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values14_mem_range_values15 i

set_option maxHeartbeats 3000000 in
theorem recursiveValueSet_fifteen_subset_range :
    recursiveValueSet 15 ⊆ Set.range values15 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with hsqrt | hadd
  · exact recursiveValueSet_fifteen_unary_subset_range hsqrt
  · rcases hadd with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 13 := by simpa using hb
      rw [recursiveValueSet_thirteen] at hb'
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values13_mem_range_values15 i
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 12 := by simpa using hb
      rw [recursiveValueSet_twelve] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values12_mem_range_values15 i
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 11 := by simpa using hb
      rw [recursiveValueSet_eleven] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl
      · exact one_add_values11_mem_range_values15 i
      · exact two_add_values11_mem_range_values15 i
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 10 := by simpa using hb
      rw [recursiveValueSet_ten] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_values10_mem_range_values15 i
      · exact sqrt_two_add_values10_mem_range_values15 i
      · exact two_add_values10_mem_range_values15 i
    · rw [recursiveValueSet_five_eq_range_values5] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rw [recursiveValueSet_nine] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values5_add_values9_mem_range_values15 i j
    · rw [recursiveValueSet_six_eq_range_values6] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values6_add_values8_mem_range_values15 i j
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values7_add_values7_mem_range_values15 i j
    · rw [recursiveValueSet_eight] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six_eq_range_values6] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      change (Set.range values15) (values8 i + values6 j)
      simpa [add_comm] using values6_add_values8_mem_range_values15 j i
    · rw [recursiveValueSet_nine] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five_eq_range_values5] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      change (Set.range values15) (values9 i + values5 j)
      simpa [add_comm] using values5_add_values9_mem_range_values15 j i
    · rw [recursiveValueSet_ten] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl | rfl
      · change (Set.range values15) (values10 i + 1)
        simpa [add_comm] using one_add_values10_mem_range_values15 i
      · change (Set.range values15) (values10 i + Real.sqrt 2)
        simpa [add_comm] using sqrt_two_add_values10_mem_range_values15 i
      · change (Set.range values15) (values10 i + 2)
        simpa [add_comm] using two_add_values10_mem_range_values15 i
    · rw [recursiveValueSet_eleven] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · change (Set.range values15) (values11 i + 1)
        simpa [add_comm] using one_add_values11_mem_range_values15 i
      · change (Set.range values15) (values11 i + 2)
        simpa [add_comm] using two_add_values11_mem_range_values15 i
    · rw [recursiveValueSet_twelve] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      change (Set.range values15) (values12 i + 1)
      simpa [add_comm] using one_add_values12_mem_range_values15 i
    · rw [recursiveValueSet_thirteen] at ha
      simp [recursiveValueSet] at hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with rfl
      change (Set.range values15) (values13 i + 1)
      simpa [add_comm] using one_add_values13_mem_range_values15 i

theorem recursiveValueSet_fifteen :
    recursiveValueSet 15 = Set.range values15 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_fifteen_subset_range
  · exact values15_range_subset_recursiveValueSet_fifteen

theorem recursiveValueSet_fifteen_ncard :
    (recursiveValueSet 15).ncard = 791 := by
  rw [recursiveValueSet_fifteen, values15_range_ncard]

theorem a158415_fifteen : a158415 15 = 791 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_fifteen_ncard

end Expr
end A158415
end LeanProofs
