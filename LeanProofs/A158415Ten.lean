import LeanProofs.A158415

/-!
# The tenth value of OEIS A158415

This module continues `LeanProofs.A158415` with the next exact finite
certificate.  It is kept separate because the size-10 certificate is large
enough to deserve its own file.
-/

namespace LeanProofs

namespace A158415

namespace Expr

open Set

noncomputable def values10Nat : Nat → ℝ
  | 0 => Real.sqrt (values9 ⟨0, by decide⟩)
  | 1 => Real.sqrt (values9 ⟨1, by decide⟩)
  | 2 => Real.sqrt (values9 ⟨2, by decide⟩)
  | 3 => Real.sqrt (values9 ⟨3, by decide⟩)
  | 4 => Real.sqrt (values9 ⟨4, by decide⟩)
  | 5 => Real.sqrt (values9 ⟨5, by decide⟩)
  | 6 => Real.sqrt (values9 ⟨6, by decide⟩)
  | 7 => Real.sqrt (values9 ⟨7, by decide⟩)
  | 8 => Real.sqrt (values9 ⟨8, by decide⟩)
  | 9 => Real.sqrt (values9 ⟨9, by decide⟩)
  | 10 => Real.sqrt (values9 ⟨10, by decide⟩)
  | 11 => Real.sqrt (values9 ⟨11, by decide⟩)
  | 12 => Real.sqrt (values9 ⟨12, by decide⟩)
  | 13 => Real.sqrt (values9 ⟨13, by decide⟩)
  | 14 => Real.sqrt (values9 ⟨14, by decide⟩)
  | 15 => Real.sqrt (values9 ⟨15, by decide⟩)
  | 16 => Real.sqrt (values9 ⟨16, by decide⟩)
  | 17 => Real.sqrt (values9 ⟨17, by decide⟩)
  | 18 => Real.sqrt (values9 ⟨18, by decide⟩)
  | 19 => Real.sqrt (values9 ⟨19, by decide⟩)
  | 20 => Real.sqrt (values9 ⟨20, by decide⟩)
  | 21 => Real.sqrt (values9 ⟨21, by decide⟩)
  | 22 => Real.sqrt (values9 ⟨22, by decide⟩)
  | 23 => Real.sqrt (values9 ⟨23, by decide⟩)
  | 24 => Real.sqrt (values9 ⟨24, by decide⟩)
  | 25 => Real.sqrt (values9 ⟨25, by decide⟩)
  | 26 => Real.sqrt (values9 ⟨26, by decide⟩)
  | 27 => Real.sqrt (values9 ⟨27, by decide⟩)
  | 28 => Real.sqrt (values9 ⟨28, by decide⟩)
  | 29 => Real.sqrt (values9 ⟨29, by decide⟩)
  | 30 => Real.sqrt (values9 ⟨30, by decide⟩)
  | 31 => Real.sqrt (values9 ⟨31, by decide⟩)
  | 32 => 1 + values8 ⟨1, by decide⟩
  | 33 => 1 + values8 ⟨2, by decide⟩
  | 34 => 1 + values8 ⟨3, by decide⟩
  | 35 => 1 + values8 ⟨4, by decide⟩
  | 36 => 1 + values8 ⟨5, by decide⟩
  | 37 => Real.sqrt (values9 ⟨32, by decide⟩)
  | 38 => 1 + values8 ⟨6, by decide⟩
  | 39 => 1 + values8 ⟨7, by decide⟩
  | 40 => 1 + values8 ⟨8, by decide⟩
  | 41 => 1 + values8 ⟨9, by decide⟩
  | 42 => 1 + values8 ⟨10, by decide⟩
  | 43 => Real.sqrt 2 + rt2_4
  | 44 => 1 + values8 ⟨11, by decide⟩
  | 45 => Real.sqrt 2 + Real.sqrt 2
  | 46 => 1 + values8 ⟨12, by decide⟩
  | 47 => 1 + values8 ⟨13, by decide⟩
  | 48 => 1 + values8 ⟨14, by decide⟩
  | 49 => 1 + values8 ⟨15, by decide⟩
  | 50 => 1 + values8 ⟨16, by decide⟩
  | 51 => 1 + values8 ⟨17, by decide⟩
  | 52 => 1 + values8 ⟨18, by decide⟩
  | 53 => 1 + values8 ⟨19, by decide⟩
  | _ => 0

noncomputable def values10 (i : Fin 54) : ℝ :=
  values10Nat i.1

theorem rt2_4_lt_six_fifths : rt2_4 < (6 / 5 : ℝ) := by
  rw [rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 6 / 5)]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (6 / 5) ^ 2)]
  norm_num

theorem twenty_nine_twentyfifths_lt_rt2_4 : (29 / 25 : ℝ) < rt2_4 := by
  rw [rt2_4]
  apply Real.lt_sqrt_of_sq_lt
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem sqrt_two_lt_143_100 : Real.sqrt 2 < (143 / 100 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 143 / 100)]
  norm_num

theorem sqrt_two_lt_71_50 : Real.sqrt 2 < (71 / 50 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 71 / 50)]
  norm_num

theorem rt2_4_lt_119_100 : rt2_4 < (119 / 100 : ℝ) := by
  rw [rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 119 / 100)]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (119 / 100) ^ 2)]
  norm_num

theorem seventeen_tenths_lt_sqrt_three : (17 / 10 : ℝ) < Real.sqrt 3 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem one_add_rt2_4_lt_sqrt_five : 1 + rt2_4 < Real.sqrt 5 := by
  have h : (11 / 5 : ℝ) < Real.sqrt 5 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  linarith [rt2_4_lt_six_fifths]

theorem sqrt_five_lt_one_add_sqrt_sqrt_one_add_sqrt_two :
    Real.sqrt 5 < 1 + sqrt_sqrt_one_add_sqrt_two := by
  have h5 : Real.sqrt 5 < (56 / 25 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 56 / 25)]
    norm_num
  have hs2 : (7 / 5 : ℝ) < Real.sqrt 2 := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  have hinner : ((31 / 25 : ℝ) ^ 2) < sqrt_one_add_sqrt_two := by
    rw [sqrt_one_add_sqrt_two]
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hss : (31 / 25 : ℝ) < sqrt_sqrt_one_add_sqrt_two := by
    rw [sqrt_sqrt_one_add_sqrt_two]
    exact Real.lt_sqrt_of_sq_lt hinner
  linarith

theorem one_add_sqrt_one_add_sqrt_two_lt_sqrt_two_add_rt2_4 :
    1 + sqrt_one_add_sqrt_two < Real.sqrt 2 + rt2_4 := by
  have hupper : sqrt_one_add_sqrt_two < (39 / 25 : ℝ) := by
    rw [sqrt_one_add_sqrt_two, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 39 / 25)]
    nlinarith [sqrt_two_lt_143_100]
  have hlower : (64 / 25 : ℝ) < Real.sqrt 2 + rt2_4 := by
    have hs2 : (7 / 5 : ℝ) < Real.sqrt 2 := by
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith [hs2, twenty_nine_twentyfifths_lt_rt2_4]
  linarith

theorem sqrt_two_add_rt2_4_lt_one_add_sqrt_three :
    Real.sqrt 2 + rt2_4 < 1 + Real.sqrt 3 := by
  have hleft : Real.sqrt 2 + rt2_4 < (261 / 100 : ℝ) := by
    linarith [sqrt_two_lt_71_50, rt2_4_lt_119_100]
  have hright : (261 / 100 : ℝ) < 1 + Real.sqrt 3 := by
    linarith [seventeen_tenths_lt_sqrt_three]
  linarith

theorem values9_nonneg (i : Fin 33) : (0 : ℝ) ≤ values9 i := by
  have h0 : (0 : ℝ) ≤ values9 ⟨0, by decide⟩ := by
    norm_num [values9, values9List]
  exact h0.trans (values9_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values9_strictMono :
    StrictMono fun i : Fin 33 => Real.sqrt (values9 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values9_nonneg i) (values9_strictMono hij)

set_option maxHeartbeats 1000000 in
theorem values10_strictMono : StrictMono values10 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · exact sqrt_values9_strictMono (by decide)
  · simp [values10, values10Nat, values9, values9List, values8, values8List, sqrt_four]
    linarith [one_lt_rt2_32]
  · change 1 + values8 (1 : Fin 20) < 1 + values8 (2 : Fin 20)
    linarith [values8_strictMono (by native_decide : (1 : Fin 20) < 2)]
  · change 1 + values8 (2 : Fin 20) < 1 + values8 (3 : Fin 20)
    linarith [values8_strictMono (by native_decide : (2 : Fin 20) < 3)]
  · change 1 + values8 (3 : Fin 20) < 1 + values8 (4 : Fin 20)
    linarith [values8_strictMono (by native_decide : (3 : Fin 20) < 4)]
  · change 1 + values8 (4 : Fin 20) < 1 + values8 (5 : Fin 20)
    linarith [values8_strictMono (by native_decide : (4 : Fin 20) < 5)]
  · simp [values10, values10Nat, values8, values8List, values9, values9List]
    exact one_add_rt2_4_lt_sqrt_five
  · simp [values10, values10Nat, values8, values8List, values9, values9List]
    exact sqrt_five_lt_one_add_sqrt_sqrt_one_add_sqrt_two
  · change 1 + values8 (6 : Fin 20) < 1 + values8 (7 : Fin 20)
    linarith [values8_strictMono (by native_decide : (6 : Fin 20) < 7)]
  · change 1 + values8 (7 : Fin 20) < 1 + values8 (8 : Fin 20)
    linarith [values8_strictMono (by native_decide : (7 : Fin 20) < 8)]
  · change 1 + values8 (8 : Fin 20) < 1 + values8 (9 : Fin 20)
    linarith [values8_strictMono (by native_decide : (8 : Fin 20) < 9)]
  · change 1 + values8 (9 : Fin 20) < 1 + values8 (10 : Fin 20)
    linarith [values8_strictMono (by native_decide : (9 : Fin 20) < 10)]
  · simp [values10, values10Nat, values8, values8List]
    exact one_add_sqrt_one_add_sqrt_two_lt_sqrt_two_add_rt2_4
  · simp [values10, values10Nat, values8, values8List]
    exact sqrt_two_add_rt2_4_lt_one_add_sqrt_three
  · simp [values10, values10Nat, values8, values8List]
    linarith [one_add_sqrt_three_lt_two_mul_sqrt_two]
  · simp [values10, values10Nat, values8, values8List]
    linarith [two_mul_sqrt_two_lt_three]
  · change 1 + values8 (12 : Fin 20) < 1 + values8 (13 : Fin 20)
    linarith [values8_strictMono (by native_decide : (12 : Fin 20) < 13)]
  · change 1 + values8 (13 : Fin 20) < 1 + values8 (14 : Fin 20)
    linarith [values8_strictMono (by native_decide : (13 : Fin 20) < 14)]
  · change 1 + values8 (14 : Fin 20) < 1 + values8 (15 : Fin 20)
    linarith [values8_strictMono (by native_decide : (14 : Fin 20) < 15)]
  · change 1 + values8 (15 : Fin 20) < 1 + values8 (16 : Fin 20)
    linarith [values8_strictMono (by native_decide : (15 : Fin 20) < 16)]
  · change 1 + values8 (16 : Fin 20) < 1 + values8 (17 : Fin 20)
    linarith [values8_strictMono (by native_decide : (16 : Fin 20) < 17)]
  · change 1 + values8 (17 : Fin 20) < 1 + values8 (18 : Fin 20)
    linarith [values8_strictMono (by native_decide : (17 : Fin 20) < 18)]
  · change 1 + values8 (18 : Fin 20) < 1 + values8 (19 : Fin 20)
    linarith [values8_strictMono (by native_decide : (18 : Fin 20) < 19)]

theorem sqrt_values9_mem_range_values10 (i : Fin 33) :
    Real.sqrt (values9 i) ∈ Set.range values10 := by
  fin_cases i
  · exact ⟨(0 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(1 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(2 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(3 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(4 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(5 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(6 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(7 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(8 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(9 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(10 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(11 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(12 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(13 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(14 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(15 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(16 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(17 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(18 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(19 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(20 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(21 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(22 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(23 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(24 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(25 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(26 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(27 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(28 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(29 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(30 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(31 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(37 : Fin 54), by simp [values10, values10Nat]⟩

theorem one_add_values8_mem_range_values10 (i : Fin 20) :
    1 + values8 i ∈ Set.range values10 := by
  fin_cases i
  · exact ⟨(31 : Fin 54), by norm_num [values10, values10Nat, values9, values9List, values8, values8List, sqrt_four]⟩
  · exact ⟨(32 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(33 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(34 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(35 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(36 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(38 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(39 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(40 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(41 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(42 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(44 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(46 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(47 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(48 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(49 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(50 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(51 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(52 : Fin 54), by simp [values10, values10Nat]⟩
  · exact ⟨(53 : Fin 54), by simp [values10, values10Nat]⟩

theorem sqrt_two_add_rt2_4_mem_range_values10 :
    Real.sqrt 2 + rt2_4 ∈ Set.range values10 := by
  exact ⟨(43 : Fin 54), by simp [values10, values10Nat]⟩

theorem sqrt_two_add_sqrt_two_mem_range_values10 :
    Real.sqrt 2 + Real.sqrt 2 ∈ Set.range values10 := by
  exact ⟨(45 : Fin 54), by simp [values10, values10Nat]⟩

theorem sqrt_values9_mem_recursiveValueSet_ten (i : Fin 33) :
    Real.sqrt (values9 i) ∈ recursiveValueSet 10 := by
  rw [recursiveValueSet]
  left
  refine ⟨values9 i, ?_, rfl⟩
  rw [recursiveValueSet_nine]
  exact ⟨i, rfl⟩

theorem one_add_values8_mem_recursiveValueSet_ten (i : Fin 20) :
    1 + values8 i ∈ recursiveValueSet 10 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨0, by decide⟩, 1, ?_, values8 i, ?_, rfl⟩
  · simp [recursiveValueSet]
  · change values8 i ∈ recursiveValueSet 8
    rw [recursiveValueSet_eight]
    exact ⟨i, rfl⟩

theorem sqrt_two_add_rt2_4_mem_recursiveValueSet_ten :
    Real.sqrt 2 + rt2_4 ∈ recursiveValueSet 10 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, rt2_4, ?_, rfl⟩
  · change Real.sqrt 2 ∈ recursiveValueSet 4
    rw [recursiveValueSet_four]
    simp
  · change rt2_4 ∈ recursiveValueSet 5
    rw [recursiveValueSet_five]
    simp [rt2_4]

theorem sqrt_two_add_sqrt_two_mem_recursiveValueSet_ten :
    Real.sqrt 2 + Real.sqrt 2 ∈ recursiveValueSet 10 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, Real.sqrt 2, ?_, rfl⟩
  · change Real.sqrt 2 ∈ recursiveValueSet 4
    rw [recursiveValueSet_four]
    simp
  · change Real.sqrt 2 ∈ recursiveValueSet 5
    rw [recursiveValueSet_five]
    simp

theorem values10_mem_recursiveValueSet (i : Fin 54) :
    values10 i ∈ recursiveValueSet 10 := by
  fin_cases i
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (0 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (1 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (2 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (3 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (4 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (5 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (6 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (7 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (8 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (9 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (10 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (11 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (12 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (13 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (14 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (15 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (16 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (17 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (18 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (19 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (20 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (21 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (22 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (23 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (24 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (25 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (26 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (27 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (28 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (29 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (30 : Fin 33)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (31 : Fin 33)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (1 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (2 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (3 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (4 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (5 : Fin 20)
  · simpa [values10, values10Nat] using sqrt_values9_mem_recursiveValueSet_ten (32 : Fin 33)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (6 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (7 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (8 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (9 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (10 : Fin 20)
  · simpa [values10, values10Nat] using sqrt_two_add_rt2_4_mem_recursiveValueSet_ten
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (11 : Fin 20)
  · simpa [values10, values10Nat] using sqrt_two_add_sqrt_two_mem_recursiveValueSet_ten
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (12 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (13 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (14 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (15 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (16 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (17 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (18 : Fin 20)
  · simpa [values10, values10Nat] using one_add_values8_mem_recursiveValueSet_ten (19 : Fin 20)


set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem recursiveValueSet_ten_subset_range :
    recursiveValueSet 10 ⊆ Set.range values10 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with h | h
  · rcases h with ⟨y, hy, rfl⟩
    rw [recursiveValueSet_nine] at hy
    rcases hy with ⟨i, rfl⟩
    exact sqrt_values9_mem_range_values10 i
  · rcases h with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values8_mem_range_values10 i
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      fin_cases i
      · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (2 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (3 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (7 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (10 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (11 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl
      · rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (3 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (11 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (13 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (16 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (18 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl | rfl
      · rcases hb' with rfl | rfl | rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert sqrt_two_add_rt2_4_mem_range_values10 using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert sqrt_two_add_sqrt_two_mem_range_values10 using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (18 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
    · rw [recursiveValueSet_five] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl | rfl | rfl | rfl
      · rcases hb' with rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert sqrt_two_add_rt2_4_mem_range_values10 using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert sqrt_two_add_sqrt_two_mem_range_values10 using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl | rfl
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (18 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
    · rw [recursiveValueSet_six] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (3 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (13 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (11 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (16 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (18 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
      · rcases hb' with rfl | rfl
        · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
        · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
          simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
          ring_nf
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      fin_cases i
      · convert one_add_values8_mem_range_values10 (0 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (2 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (3 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (5 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (7 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (8 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (10 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (11 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (12 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (14 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (15 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (17 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
      · convert one_add_values8_mem_range_values10 (19 : Fin 20) using 1 <;>
        simp [values8, values8List, values7, values7List, rt2_4, add_comm, two_mul, sqrt_four] <;>
        ring_nf
    · rw [recursiveValueSet_eight] at ha
      simp [recursiveValueSet] at hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with rfl
      simpa [add_comm] using one_add_values8_mem_range_values10 i
theorem recursiveValueSet_ten :
    recursiveValueSet 10 = Set.range values10 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_ten_subset_range
  · intro x hx
    rcases hx with ⟨i, rfl⟩
    exact values10_mem_recursiveValueSet i

theorem recursiveValueSet_ten_ncard :
    (recursiveValueSet 10).ncard = 54 := by
  rw [recursiveValueSet_ten]
  rw [Set.ncard_range_of_injective values10_strictMono.injective]
  norm_num

/-- OEIS A158415 has value `54` at `n = 10`. -/
theorem a158415_ten : a158415 10 = 54 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_ten_ncard

end Expr

export Expr (a158415_ten)

end A158415

end LeanProofs
