import LeanProofs.A158415Ten

/-!
# Size-eleven certificate for OEIS A158415

This module records the 91 exact representatives discovered for size 11 and
proves that this table is exactly the split-recursive value set, yielding
`a158415 11 = 91`.
-/

namespace LeanProofs

namespace A158415

namespace Expr

open Set

noncomputable def values11Nat : Nat → ℝ
  | 0 => Real.sqrt (values10 ⟨0, by decide⟩)
  | 1 => Real.sqrt (values10 ⟨1, by decide⟩)
  | 2 => Real.sqrt (values10 ⟨2, by decide⟩)
  | 3 => Real.sqrt (values10 ⟨3, by decide⟩)
  | 4 => Real.sqrt (values10 ⟨4, by decide⟩)
  | 5 => Real.sqrt (values10 ⟨5, by decide⟩)
  | 6 => Real.sqrt (values10 ⟨6, by decide⟩)
  | 7 => Real.sqrt (values10 ⟨7, by decide⟩)
  | 8 => Real.sqrt (values10 ⟨8, by decide⟩)
  | 9 => Real.sqrt (values10 ⟨9, by decide⟩)
  | 10 => Real.sqrt (values10 ⟨10, by decide⟩)
  | 11 => Real.sqrt (values10 ⟨11, by decide⟩)
  | 12 => Real.sqrt (values10 ⟨12, by decide⟩)
  | 13 => Real.sqrt (values10 ⟨13, by decide⟩)
  | 14 => Real.sqrt (values10 ⟨14, by decide⟩)
  | 15 => Real.sqrt (values10 ⟨15, by decide⟩)
  | 16 => Real.sqrt (values10 ⟨16, by decide⟩)
  | 17 => Real.sqrt (values10 ⟨17, by decide⟩)
  | 18 => Real.sqrt (values10 ⟨18, by decide⟩)
  | 19 => Real.sqrt (values10 ⟨19, by decide⟩)
  | 20 => Real.sqrt (values10 ⟨20, by decide⟩)
  | 21 => Real.sqrt (values10 ⟨21, by decide⟩)
  | 22 => Real.sqrt (values10 ⟨22, by decide⟩)
  | 23 => Real.sqrt (values10 ⟨23, by decide⟩)
  | 24 => Real.sqrt (values10 ⟨24, by decide⟩)
  | 25 => Real.sqrt (values10 ⟨25, by decide⟩)
  | 26 => Real.sqrt (values10 ⟨26, by decide⟩)
  | 27 => Real.sqrt (values10 ⟨27, by decide⟩)
  | 28 => Real.sqrt (values10 ⟨28, by decide⟩)
  | 29 => Real.sqrt (values10 ⟨29, by decide⟩)
  | 30 => Real.sqrt (values10 ⟨30, by decide⟩)
  | 31 => Real.sqrt (values10 ⟨31, by decide⟩)
  | 32 => Real.sqrt (values10 ⟨32, by decide⟩)
  | 33 => Real.sqrt (values10 ⟨33, by decide⟩)
  | 34 => Real.sqrt (values10 ⟨34, by decide⟩)
  | 35 => Real.sqrt (values10 ⟨35, by decide⟩)
  | 36 => Real.sqrt (values10 ⟨36, by decide⟩)
  | 37 => Real.sqrt (values10 ⟨37, by decide⟩)
  | 38 => Real.sqrt (values10 ⟨38, by decide⟩)
  | 39 => Real.sqrt (values10 ⟨39, by decide⟩)
  | 40 => Real.sqrt (values10 ⟨40, by decide⟩)
  | 41 => Real.sqrt (values10 ⟨41, by decide⟩)
  | 42 => Real.sqrt (values10 ⟨42, by decide⟩)
  | 43 => Real.sqrt (values10 ⟨43, by decide⟩)
  | 44 => Real.sqrt (values10 ⟨44, by decide⟩)
  | 45 => Real.sqrt (values10 ⟨45, by decide⟩)
  | 46 => Real.sqrt (values10 ⟨46, by decide⟩)
  | 47 => Real.sqrt (values10 ⟨47, by decide⟩)
  | 48 => Real.sqrt (values10 ⟨48, by decide⟩)
  | 49 => Real.sqrt (values10 ⟨49, by decide⟩)
  | 50 => Real.sqrt (values10 ⟨50, by decide⟩)
  | 51 => Real.sqrt (values10 ⟨51, by decide⟩)
  | 52 => 1 + values9 ⟨1, by decide⟩
  | 53 => 1 + values9 ⟨2, by decide⟩
  | 54 => 1 + values9 ⟨3, by decide⟩
  | 55 => 1 + values9 ⟨4, by decide⟩
  | 56 => 1 + values9 ⟨5, by decide⟩
  | 57 => Real.sqrt (values10 ⟨52, by decide⟩)
  | 58 => 1 + values9 ⟨6, by decide⟩
  | 59 => 1 + values9 ⟨7, by decide⟩
  | 60 => 1 + values9 ⟨8, by decide⟩
  | 61 => 1 + values9 ⟨9, by decide⟩
  | 62 => Real.sqrt (values10 ⟨53, by decide⟩)
  | 63 => 1 + values9 ⟨10, by decide⟩
  | 64 => 1 + values9 ⟨11, by decide⟩
  | 65 => rt2_4 + rt2_4
  | 66 => 1 + values9 ⟨12, by decide⟩
  | 67 => 1 + values9 ⟨13, by decide⟩
  | 68 => 1 + values9 ⟨14, by decide⟩
  | 69 => Real.sqrt 2 + rt2_8
  | 70 => 1 + values9 ⟨15, by decide⟩
  | 71 => Real.sqrt 2 + rt2_4
  | 72 => 1 + values9 ⟨16, by decide⟩
  | 73 => 1 + values9 ⟨17, by decide⟩
  | 74 => Real.sqrt 2 + Real.sqrt 2
  | 75 => 1 + values9 ⟨18, by decide⟩
  | 76 => 1 + values9 ⟨19, by decide⟩
  | 77 => 1 + values9 ⟨20, by decide⟩
  | 78 => 1 + values9 ⟨21, by decide⟩
  | 79 => Real.sqrt 2 + Real.sqrt 3
  | 80 => 1 + values9 ⟨22, by decide⟩
  | 81 => 1 + values9 ⟨23, by decide⟩
  | 82 => 1 + values9 ⟨24, by decide⟩
  | 83 => 1 + values9 ⟨25, by decide⟩
  | 84 => 1 + values9 ⟨26, by decide⟩
  | 85 => 1 + values9 ⟨27, by decide⟩
  | 86 => 1 + values9 ⟨28, by decide⟩
  | 87 => 1 + values9 ⟨29, by decide⟩
  | 88 => 1 + values9 ⟨30, by decide⟩
  | 89 => 1 + values9 ⟨31, by decide⟩
  | 90 => 1 + values9 ⟨32, by decide⟩
  | _ => 0

noncomputable def values11 (i : Fin 91) : ℝ :=
  values11Nat i.1

noncomputable def values5Nat : Nat → ℝ
  | 0 => 1
  | 1 => rt2_4
  | 2 => Real.sqrt 2
  | 3 => 2
  | 4 => 3
  | _ => 0

noncomputable def values5 (i : Fin 5) : ℝ :=
  values5Nat i.1

noncomputable def values6Nat : Nat → ℝ
  | 0 => 1
  | 1 => rt2_8
  | 2 => rt2_4
  | 3 => Real.sqrt 2
  | 4 => Real.sqrt 3
  | 5 => 2
  | 6 => 1 + Real.sqrt 2
  | 7 => 3
  | _ => 0

noncomputable def values6 (i : Fin 8) : ℝ :=
  values6Nat i.1

theorem sqrt_values10_51_eq_two :
    Real.sqrt (values10 (51 : Fin 54)) = (2 : ℝ) := by
  simp [values10, values10Nat, values8, values8List]
  rw [show (1 + (3 : ℝ)) = 4 by norm_num, sqrt_four]

macro "a158415_table" : tactic =>
  `(tactic|
    (simp [values11, values11Nat, values9, values9List, values8, values8List,
      values7, values7List, values6, values6Nat, values5, values5Nat, rt2_4,
      rt2_8, sqrt_values10_51_eq_two, sqrt_four, add_comm, add_assoc,
      add_left_comm, two_mul] <;> ring_nf))

theorem values10_nonneg (i : Fin 54) : (0 : ℝ) ≤ values10 i := by
  have h0 : (0 : ℝ) ≤ values10 ⟨0, by decide⟩ := by
    norm_num [values10, values10Nat]
  exact h0.trans (values10_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values10_strictMono :
    StrictMono fun i : Fin 54 => Real.sqrt (values10 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values10_nonneg i) (values10_strictMono hij)

theorem seven_fifths_lt_sqrt_two : (7 / 5 : ℝ) < Real.sqrt 2 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem one_hundred_fortyone_hundred_lt_sqrt_two : (141 / 100 : ℝ) < Real.sqrt 2 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem one_hundred_thirtyone_hundred_lt_sqrt_two : (131 / 100 : ℝ) < Real.sqrt 2 := by
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem sqrt_three_lt_eightyseven_fiftieths : Real.sqrt 3 < (87 / 50 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 87 / 50)]
  norm_num

theorem rt2_8_lt_eleven_tenths : rt2_8 < (11 / 10 : ℝ) := by
  rw [rt2_8, rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 11 / 10)]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11 / 10 : ℝ) ^ 2)]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < ((11 / 10 : ℝ) ^ 2) ^ 2)]
  norm_num

theorem one_hundred_nine_hundred_lt_rt2_8 : (109 / 100 : ℝ) < rt2_8 := by
  rw [rt2_8, rt2_4]
  apply Real.lt_sqrt_of_sq_lt
  apply Real.lt_sqrt_of_sq_lt
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem fortyseven_fortieths_lt_rt2_4 : (47 / 40 : ℝ) < rt2_4 := by
  rw [rt2_4]
  apply Real.lt_sqrt_of_sq_lt
  apply Real.lt_sqrt_of_sq_lt
  norm_num

theorem rt3_4_lt_twentyseven_twentieths : rt3_4 < (27 / 20 : ℝ) := by
  rw [rt3_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 27 / 20)]
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (27 / 20 : ℝ) ^ 2)]
  norm_num

theorem sqrt_sqrt_one_add_rt2_4_lt_sixtyone_fiftieths :
    sqrt_sqrt_one_add_rt2_4 < (61 / 50 : ℝ) := by
  rw [sqrt_sqrt_one_add_rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 61 / 50)]
  rw [sqrt_one_add_rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < (61 / 50 : ℝ) ^ 2)]
  nlinarith [rt2_4_lt_119_100]

theorem one_hundred_eleven_hundred_lt_sqrt_sqrt_sqrt_one_add_sqrt_two :
    (111 / 100 : ℝ) < sqrt_sqrt_sqrt_one_add_sqrt_two := by
  rw [sqrt_sqrt_sqrt_one_add_sqrt_two]
  apply Real.lt_sqrt_of_sq_lt
  rw [sqrt_sqrt_one_add_sqrt_two]
  apply Real.lt_sqrt_of_sq_lt
  rw [sqrt_one_add_sqrt_two]
  apply Real.lt_sqrt_of_sq_lt
  nlinarith [one_hundred_thirtyone_hundred_lt_sqrt_two]

theorem one_add_rt2_8_lt_sqrt_values10_52 :
    1 + rt2_8 < Real.sqrt (values10 (52 : Fin 54)) := by
  have hleft : 1 + rt2_8 < (21 / 10 : ℝ) := by
    linarith [rt2_8_lt_eleven_tenths]
  have hright : (21 / 10 : ℝ) < Real.sqrt (1 + (2 + Real.sqrt 2)) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith [one_hundred_fortyone_hundred_lt_sqrt_two]
  simpa [values10, values10Nat, values8, values8List] using hleft.trans hright

theorem sqrt_values10_52_lt_one_add_values9_6 :
    Real.sqrt (values10 (52 : Fin 54)) < 1 + values9 (6 : Fin 33) := by
  have hleft : Real.sqrt (1 + (2 + Real.sqrt 2)) < (211 / 100 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 211 / 100)]
    nlinarith [sqrt_two_lt_143_100]
  have hright : (211 / 100 : ℝ) < 1 + sqrt_sqrt_sqrt_one_add_sqrt_two := by
    linarith [one_hundred_eleven_hundred_lt_sqrt_sqrt_sqrt_one_add_sqrt_two]
  simpa [values10, values10Nat, values8, values8List, values9, values9List]
    using hleft.trans hright

theorem one_add_values9_9_lt_sqrt_values10_53 :
    1 + values9 (9 : Fin 33) < Real.sqrt (values10 (53 : Fin 54)) := by
  have hleft : 1 + sqrt_sqrt_one_add_rt2_4 < (111 / 50 : ℝ) := by
    linarith [sqrt_sqrt_one_add_rt2_4_lt_sixtyone_fiftieths]
  have hright : (111 / 50 : ℝ) < Real.sqrt (1 + 4) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num
  simpa [values10, values10Nat, values8, values8List, values9, values9List]
    using hleft.trans hright

theorem one_add_values9_11_lt_rt2_4_add_rt2_4 :
    1 + values9 (11 : Fin 33) < rt2_4 + rt2_4 := by
  have hleft : 1 + rt3_4 < (47 / 20 : ℝ) := by
    linarith [rt3_4_lt_twentyseven_twentieths]
  have hright : (47 / 20 : ℝ) < rt2_4 + rt2_4 := by
    linarith [fortyseven_fortieths_lt_rt2_4]
  simp [values9, values9List]
  exact hleft.trans hright

theorem rt2_4_add_rt2_4_lt_one_add_values9_12 :
    rt2_4 + rt2_4 < 1 + values9 (12 : Fin 33) := by
  have hleft : rt2_4 + rt2_4 < (12 / 5 : ℝ) := by
    linarith [rt2_4_lt_six_fifths]
  have hright : (12 / 5 : ℝ) < 1 + Real.sqrt 2 := by
    linarith [seven_fifths_lt_sqrt_two]
  simp [values9, values9List]
  exact hleft.trans hright

theorem one_add_values9_14_lt_sqrt_two_add_rt2_8 :
    1 + values9 (14 : Fin 33) < Real.sqrt 2 + rt2_8 := by
  have hleft : 1 + sqrt_one_add_rt2_4 < (249 / 100 : ℝ) := by
    have hs : sqrt_one_add_rt2_4 < (149 / 100 : ℝ) := by
      rw [sqrt_one_add_rt2_4, Real.sqrt_lt' (by norm_num : (0 : ℝ) < 149 / 100)]
      nlinarith [rt2_4_lt_119_100]
    linarith
  have hright : (249 / 100 : ℝ) < Real.sqrt 2 + rt2_8 := by
    linarith [seven_fifths_lt_sqrt_two, one_hundred_nine_hundred_lt_rt2_8]
  simp [values9, values9List]
  exact hleft.trans hright

theorem sqrt_two_add_rt2_8_lt_one_add_values9_15 :
    Real.sqrt 2 + rt2_8 < 1 + values9 (15 : Fin 33) := by
  have hleft : Real.sqrt 2 + rt2_8 < (253 / 100 : ℝ) := by
    linarith [sqrt_two_lt_143_100, rt2_8_lt_eleven_tenths]
  have hright : (253 / 100 : ℝ) < 1 + sqrt_one_add_sqrt_two := by
    have h : (153 / 100 : ℝ) < sqrt_one_add_sqrt_two := by
      rw [sqrt_one_add_sqrt_two]
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  simp [values9, values9List]
  exact hleft.trans hright

theorem sqrt_two_add_rt2_4_lt_one_add_values9_16 :
    Real.sqrt 2 + rt2_4 < 1 + values9 (16 : Fin 33) := by
  have hleft : Real.sqrt 2 + rt2_4 < (263 / 100 : ℝ) := by
    linarith [sqrt_two_lt_143_100, rt2_4_lt_six_fifths]
  have hright : (263 / 100 : ℝ) < 1 + sqrt_one_add_sqrt_three := by
    have h : (163 / 100 : ℝ) < sqrt_one_add_sqrt_three := by
      rw [sqrt_one_add_sqrt_three]
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [seventeen_tenths_lt_sqrt_three]
    linarith
  simp [values9, values9List]
  exact hleft.trans hright

theorem sqrt_two_add_sqrt_two_lt_one_add_values9_18 :
    Real.sqrt 2 + Real.sqrt 2 < 1 + values9 (18 : Fin 33) := by
  have hs2 : Real.sqrt 2 < (17 / 12 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 17 / 12)]
    norm_num
  have hleft : Real.sqrt 2 + Real.sqrt 2 < (17 / 6 : ℝ) := by
    linarith
  have hright : (17 / 6 : ℝ) < 1 + sqrt_two_add_sqrt_two := by
    have h : (11 / 6 : ℝ) < sqrt_two_add_sqrt_two := by
      rw [sqrt_two_add_sqrt_two]
      apply Real.lt_sqrt_of_sq_lt
      nlinarith [seven_fifths_lt_sqrt_two]
    linarith
  simp [values9, values9List]
  exact hleft.trans hright

theorem one_add_values9_21_lt_sqrt_two_add_sqrt_three :
    1 + values9 (21 : Fin 33) < Real.sqrt 2 + Real.sqrt 3 := by
  have hleft : 1 + (1 + rt2_8) < (31 / 10 : ℝ) := by
    linarith [rt2_8_lt_eleven_tenths]
  have hright : (31 / 10 : ℝ) < Real.sqrt 2 + Real.sqrt 3 := by
    linarith [seven_fifths_lt_sqrt_two, seventeen_tenths_lt_sqrt_three]
  simp [values9, values9List]
  exact hleft.trans hright

theorem sqrt_two_add_sqrt_three_lt_one_add_values9_22 :
    Real.sqrt 2 + Real.sqrt 3 < 1 + values9 (22 : Fin 33) := by
  have hleft : Real.sqrt 2 + Real.sqrt 3 < (79 / 25 : ℝ) := by
    linarith [sqrt_two_lt_71_50, sqrt_three_lt_eightyseven_fiftieths]
  have hright : (79 / 25 : ℝ) < 1 + (1 + rt2_4) := by
    linarith [twenty_nine_twentyfifths_lt_rt2_4]
  simp [values9, values9List]
  exact hleft.trans hright

theorem sqrt_values10_51_lt_one_add_values9_1 :
    Real.sqrt (values10 (51 : Fin 54)) < 1 + values9 (1 : Fin 33) := by
  simp [values10, values10Nat, values9, values9List, values8, values8List]
  rw [show (1 + (3 : ℝ)) = 4 by norm_num, sqrt_four]
  linarith [one_lt_rt2_64]

theorem sqrt_values10_53_lt_one_add_values9_10 :
    Real.sqrt (values10 (53 : Fin 54)) < 1 + values9 (10 : Fin 33) := by
  have h : Real.sqrt (1 + (4 : ℝ)) < 1 + sqrt_sqrt_one_add_sqrt_two := by
    rw [show (1 + (4 : ℝ)) = 5 by norm_num]
    exact sqrt_five_lt_one_add_sqrt_sqrt_one_add_sqrt_two
  simpa [values10, values10Nat, values8, values8List, values9, values9List] using h

theorem one_add_values9_15_lt_sqrt_two_add_rt2_4 :
    1 + values9 (15 : Fin 33) < Real.sqrt 2 + rt2_4 := by
  simpa [values9, values9List] using
    one_add_sqrt_one_add_sqrt_two_lt_sqrt_two_add_rt2_4

theorem one_add_values9_17_lt_sqrt_two_add_sqrt_two :
    1 + values9 (17 : Fin 33) < Real.sqrt 2 + Real.sqrt 2 := by
  simp [values9, values9List]
  linarith [one_add_sqrt_three_lt_two_mul_sqrt_two]

set_option maxHeartbeats 1000000 in
theorem values11_strictMono : StrictMono values11 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_strictMono (by decide)
  · exact sqrt_values10_51_lt_one_add_values9_1
  · change 1 + values9 (1 : Fin 33) < 1 + values9 (2 : Fin 33)
    linarith [values9_strictMono (by native_decide : (1 : Fin 33) < 2)]
  · change 1 + values9 (2 : Fin 33) < 1 + values9 (3 : Fin 33)
    linarith [values9_strictMono (by native_decide : (2 : Fin 33) < 3)]
  · change 1 + values9 (3 : Fin 33) < 1 + values9 (4 : Fin 33)
    linarith [values9_strictMono (by native_decide : (3 : Fin 33) < 4)]
  · change 1 + values9 (4 : Fin 33) < 1 + values9 (5 : Fin 33)
    linarith [values9_strictMono (by native_decide : (4 : Fin 33) < 5)]
  · exact one_add_rt2_8_lt_sqrt_values10_52
  · exact sqrt_values10_52_lt_one_add_values9_6
  · change 1 + values9 (6 : Fin 33) < 1 + values9 (7 : Fin 33)
    linarith [values9_strictMono (by native_decide : (6 : Fin 33) < 7)]
  · change 1 + values9 (7 : Fin 33) < 1 + values9 (8 : Fin 33)
    linarith [values9_strictMono (by native_decide : (7 : Fin 33) < 8)]
  · change 1 + values9 (8 : Fin 33) < 1 + values9 (9 : Fin 33)
    linarith [values9_strictMono (by native_decide : (8 : Fin 33) < 9)]
  · exact one_add_values9_9_lt_sqrt_values10_53
  · exact sqrt_values10_53_lt_one_add_values9_10
  · change 1 + values9 (10 : Fin 33) < 1 + values9 (11 : Fin 33)
    linarith [values9_strictMono (by native_decide : (10 : Fin 33) < 11)]
  · exact one_add_values9_11_lt_rt2_4_add_rt2_4
  · exact rt2_4_add_rt2_4_lt_one_add_values9_12
  · change 1 + values9 (12 : Fin 33) < 1 + values9 (13 : Fin 33)
    linarith [values9_strictMono (by native_decide : (12 : Fin 33) < 13)]
  · change 1 + values9 (13 : Fin 33) < 1 + values9 (14 : Fin 33)
    linarith [values9_strictMono (by native_decide : (13 : Fin 33) < 14)]
  · exact one_add_values9_14_lt_sqrt_two_add_rt2_8
  · exact sqrt_two_add_rt2_8_lt_one_add_values9_15
  · exact one_add_values9_15_lt_sqrt_two_add_rt2_4
  · exact sqrt_two_add_rt2_4_lt_one_add_values9_16
  · change 1 + values9 (16 : Fin 33) < 1 + values9 (17 : Fin 33)
    linarith [values9_strictMono (by native_decide : (16 : Fin 33) < 17)]
  · exact one_add_values9_17_lt_sqrt_two_add_sqrt_two
  · exact sqrt_two_add_sqrt_two_lt_one_add_values9_18
  · change 1 + values9 (18 : Fin 33) < 1 + values9 (19 : Fin 33)
    linarith [values9_strictMono (by native_decide : (18 : Fin 33) < 19)]
  · change 1 + values9 (19 : Fin 33) < 1 + values9 (20 : Fin 33)
    linarith [values9_strictMono (by native_decide : (19 : Fin 33) < 20)]
  · change 1 + values9 (20 : Fin 33) < 1 + values9 (21 : Fin 33)
    linarith [values9_strictMono (by native_decide : (20 : Fin 33) < 21)]
  · exact one_add_values9_21_lt_sqrt_two_add_sqrt_three
  · exact sqrt_two_add_sqrt_three_lt_one_add_values9_22
  · change 1 + values9 (22 : Fin 33) < 1 + values9 (23 : Fin 33)
    linarith [values9_strictMono (by native_decide : (22 : Fin 33) < 23)]
  · change 1 + values9 (23 : Fin 33) < 1 + values9 (24 : Fin 33)
    linarith [values9_strictMono (by native_decide : (23 : Fin 33) < 24)]
  · change 1 + values9 (24 : Fin 33) < 1 + values9 (25 : Fin 33)
    linarith [values9_strictMono (by native_decide : (24 : Fin 33) < 25)]
  · change 1 + values9 (25 : Fin 33) < 1 + values9 (26 : Fin 33)
    linarith [values9_strictMono (by native_decide : (25 : Fin 33) < 26)]
  · change 1 + values9 (26 : Fin 33) < 1 + values9 (27 : Fin 33)
    linarith [values9_strictMono (by native_decide : (26 : Fin 33) < 27)]
  · change 1 + values9 (27 : Fin 33) < 1 + values9 (28 : Fin 33)
    linarith [values9_strictMono (by native_decide : (27 : Fin 33) < 28)]
  · change 1 + values9 (28 : Fin 33) < 1 + values9 (29 : Fin 33)
    linarith [values9_strictMono (by native_decide : (28 : Fin 33) < 29)]
  · change 1 + values9 (29 : Fin 33) < 1 + values9 (30 : Fin 33)
    linarith [values9_strictMono (by native_decide : (29 : Fin 33) < 30)]
  · change 1 + values9 (30 : Fin 33) < 1 + values9 (31 : Fin 33)
    linarith [values9_strictMono (by native_decide : (30 : Fin 33) < 31)]
  · change 1 + values9 (31 : Fin 33) < 1 + values9 (32 : Fin 33)
    linarith [values9_strictMono (by native_decide : (31 : Fin 33) < 32)]

set_option maxHeartbeats 2000000 in
theorem sqrt_values10_mem_range_values11 (i : Fin 54) :
    Real.sqrt (values10 i) ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(0 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(1 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(2 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(3 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(4 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(5 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(6 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(7 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(8 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(9 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(10 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(11 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(12 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(13 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(14 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(15 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(16 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(17 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(18 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(19 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(20 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(21 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(22 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(23 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(24 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(25 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(26 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(27 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(28 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(29 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(30 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(31 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(32 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(33 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(34 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(35 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(36 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(37 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(38 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(39 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(40 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(41 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(42 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(43 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(44 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(45 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(46 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(47 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(48 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(49 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(50 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(51 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(57 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(62 : Fin 91), by simp [values11, values11Nat]⟩

set_option maxHeartbeats 2000000 in
theorem one_add_values9_mem_range_values11 (i : Fin 33) :
    1 + values9 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(51 : Fin 91), by
      norm_num [values11, values11Nat, values10, values10Nat, values9,
        values9List, values8, values8List, sqrt_four]⟩
  · exact ⟨(52 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(53 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(54 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(55 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(56 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(58 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(59 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(60 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(61 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(63 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(64 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(66 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(67 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(68 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(70 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(72 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(73 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(75 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(76 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(77 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(78 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(80 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(81 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(82 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(83 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(84 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(85 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(86 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(87 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(88 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(89 : Fin 91), by simp [values11, values11Nat]⟩
  · exact ⟨(90 : Fin 91), by simp [values11, values11Nat]⟩

theorem rt2_4_add_rt2_4_mem_range_values11 :
    rt2_4 + rt2_4 ∈ Set.range values11 :=
  ⟨(65 : Fin 91), by simp [values11, values11Nat]⟩

theorem sqrt_two_add_rt2_8_mem_range_values11 :
    Real.sqrt 2 + rt2_8 ∈ Set.range values11 :=
  ⟨(69 : Fin 91), by simp [values11, values11Nat]⟩

theorem sqrt_two_add_rt2_4_mem_range_values11 :
    Real.sqrt 2 + rt2_4 ∈ Set.range values11 :=
  ⟨(71 : Fin 91), by simp [values11, values11Nat]⟩

theorem sqrt_two_add_sqrt_two_mem_range_values11 :
    Real.sqrt 2 + Real.sqrt 2 ∈ Set.range values11 :=
  ⟨(74 : Fin 91), by simp [values11, values11Nat]⟩

theorem sqrt_two_add_sqrt_three_mem_range_values11 :
    Real.sqrt 2 + Real.sqrt 3 ∈ Set.range values11 :=
  ⟨(79 : Fin 91), by simp [values11, values11Nat]⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem one_add_values8_mem_range_values11 (i : Fin 20) :
    1 + values8 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(51 : Fin 91), by a158415_table⟩
  · exact ⟨(53 : Fin 91), by a158415_table⟩
  · exact ⟨(54 : Fin 91), by a158415_table⟩
  · exact ⟨(56 : Fin 91), by a158415_table⟩
  · exact ⟨(59 : Fin 91), by a158415_table⟩
  · exact ⟨(60 : Fin 91), by a158415_table⟩
  · exact ⟨(63 : Fin 91), by a158415_table⟩
  · exact ⟨(64 : Fin 91), by a158415_table⟩
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(68 : Fin 91), by a158415_table⟩
  · exact ⟨(70 : Fin 91), by a158415_table⟩
  · exact ⟨(73 : Fin 91), by a158415_table⟩
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(78 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(84 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem one_add_values7_mem_range_values11 (i : Fin 13) :
    1 + values7 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(51 : Fin 91), by a158415_table⟩
  · exact ⟨(54 : Fin 91), by a158415_table⟩
  · exact ⟨(56 : Fin 91), by a158415_table⟩
  · exact ⟨(60 : Fin 91), by a158415_table⟩
  · exact ⟨(64 : Fin 91), by a158415_table⟩
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(70 : Fin 91), by a158415_table⟩
  · exact ⟨(73 : Fin 91), by a158415_table⟩
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem two_add_values7_mem_range_values11 (i : Fin 13) :
    2 + values7 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(77 : Fin 91), by a158415_table⟩
  · exact ⟨(78 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(81 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(83 : Fin 91), by a158415_table⟩
  · exact ⟨(84 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(87 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩
  · exact ⟨(90 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem one_add_values6_mem_range_values11 (i : Fin 8) :
    1 + values6 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(51 : Fin 91), by a158415_table⟩
  · exact ⟨(56 : Fin 91), by a158415_table⟩
  · exact ⟨(60 : Fin 91), by a158415_table⟩
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(73 : Fin 91), by a158415_table⟩
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem sqrt_two_add_values6_mem_range_values11 (i : Fin 8) :
    Real.sqrt 2 + values6 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(69 : Fin 91), by a158415_table⟩
  · exact ⟨(71 : Fin 91), by a158415_table⟩
  · exact ⟨(74 : Fin 91), by a158415_table⟩
  · exact ⟨(79 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(85 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
theorem two_add_values6_mem_range_values11 (i : Fin 8) :
    2 + values6 i ∈ Set.range values11 := by
  fin_cases i
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(78 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(84 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 4000000 in
theorem values5_add_values5_mem_range_values11 (i : Fin 5) (j : Fin 5) :
    values5 i + values5 j ∈ Set.range values11 := by
  fin_cases i <;> fin_cases j
  · exact ⟨(51 : Fin 91), by a158415_table⟩
  · exact ⟨(60 : Fin 91), by a158415_table⟩
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(60 : Fin 91), by a158415_table⟩
  · exact ⟨(65 : Fin 91), by a158415_table⟩
  · exact ⟨(71 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(87 : Fin 91), by a158415_table⟩
  · exact ⟨(66 : Fin 91), by a158415_table⟩
  · exact ⟨(71 : Fin 91), by a158415_table⟩
  · exact ⟨(74 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩
  · exact ⟨(76 : Fin 91), by a158415_table⟩
  · exact ⟨(80 : Fin 91), by a158415_table⟩
  · exact ⟨(82 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩
  · exact ⟨(86 : Fin 91), by a158415_table⟩
  · exact ⟨(87 : Fin 91), by a158415_table⟩
  · exact ⟨(88 : Fin 91), by a158415_table⟩
  · exact ⟨(89 : Fin 91), by a158415_table⟩
  · exact ⟨(90 : Fin 91), by a158415_table⟩

theorem sqrt_values10_mem_recursiveValueSet_eleven (i : Fin 54) :
    Real.sqrt (values10 i) ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  exact Or.inl ⟨values10 i, values10_mem_recursiveValueSet i, rfl⟩

theorem one_add_values9_mem_recursiveValueSet_eleven (i : Fin 33) :
    1 + values9 i ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨0, by decide⟩, 1, ?_, values9 i, ?_, rfl⟩
  · simp [recursiveValueSet]
  · change values9 i ∈ recursiveValueSet 9
    rw [recursiveValueSet_nine]
    exact ⟨i, rfl⟩

theorem rt2_4_add_rt2_4_mem_recursiveValueSet_eleven :
    rt2_4 + rt2_4 ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨4, by decide⟩, rt2_4, ?_, rt2_4, ?_, rfl⟩
  · rw [recursiveValueSet_five]
    simp [rt2_4]
  · change rt2_4 ∈ recursiveValueSet 5
    rw [recursiveValueSet_five]
    simp [rt2_4]

theorem sqrt_two_add_rt2_8_mem_recursiveValueSet_eleven :
    Real.sqrt 2 + rt2_8 ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, rt2_8, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change rt2_8 ∈ recursiveValueSet 6
    rw [recursiveValueSet_six]
    simp [rt2_8]

theorem sqrt_two_add_rt2_4_mem_recursiveValueSet_eleven :
    Real.sqrt 2 + rt2_4 ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, rt2_4, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change rt2_4 ∈ recursiveValueSet 6
    rw [recursiveValueSet_six]
    simp [rt2_4]

theorem sqrt_two_add_sqrt_two_mem_recursiveValueSet_eleven :
    Real.sqrt 2 + Real.sqrt 2 ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, Real.sqrt 2, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change Real.sqrt 2 ∈ recursiveValueSet 6
    rw [recursiveValueSet_six]
    simp

theorem sqrt_two_add_sqrt_three_mem_recursiveValueSet_eleven :
    Real.sqrt 2 + Real.sqrt 3 ∈ recursiveValueSet 11 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, Real.sqrt 3, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change Real.sqrt 3 ∈ recursiveValueSet 6
    rw [recursiveValueSet_six]
    simp

set_option maxHeartbeats 2000000 in
theorem values11_mem_recursiveValueSet (i : Fin 91) :
    values11 i ∈ recursiveValueSet 11 := by
  fin_cases i
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (0 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (1 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (2 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (3 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (4 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (5 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (6 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (7 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (8 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (9 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (10 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (11 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (12 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (13 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (14 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (15 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (16 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (17 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (18 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (19 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (20 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (21 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (22 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (23 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (24 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (25 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (26 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (27 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (28 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (29 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (30 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (31 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (32 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (33 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (34 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (35 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (36 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (37 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (38 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (39 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (40 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (41 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (42 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (43 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (44 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (45 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (46 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (47 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (48 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (49 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (50 : Fin 54)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (51 : Fin 54)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (1 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (2 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (3 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (4 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (5 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (52 : Fin 54)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (6 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (7 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (8 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (9 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_values10_mem_recursiveValueSet_eleven (53 : Fin 54)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (10 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (11 : Fin 33)
  · simpa [values11, values11Nat] using rt2_4_add_rt2_4_mem_recursiveValueSet_eleven
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (12 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (13 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (14 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_two_add_rt2_8_mem_recursiveValueSet_eleven
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (15 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_two_add_rt2_4_mem_recursiveValueSet_eleven
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (16 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (17 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_two_add_sqrt_two_mem_recursiveValueSet_eleven
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (18 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (19 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (20 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (21 : Fin 33)
  · simpa [values11, values11Nat] using sqrt_two_add_sqrt_three_mem_recursiveValueSet_eleven
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (22 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (23 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (24 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (25 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (26 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (27 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (28 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (29 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (30 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (31 : Fin 33)
  · simpa [values11, values11Nat] using one_add_values9_mem_recursiveValueSet_eleven (32 : Fin 33)

theorem values11_range_subset_recursiveValueSet_eleven :
    Set.range values11 ⊆ recursiveValueSet 11 := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact values11_mem_recursiveValueSet i

theorem values11_range_ncard :
    (Set.range values11).ncard = 91 := by
  rw [Set.ncard_range_of_injective values11_strictMono.injective]
  norm_num

theorem recursiveValueSet_eleven_unary_subset_range :
    ((fun x : ℝ => Real.sqrt x) '' recursiveValueSet 10) ⊆ Set.range values11 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_ten] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values10_mem_range_values11 i

theorem one_add_recursiveValueSet_nine_subset_range :
    {v | ∃ y ∈ recursiveValueSet 9, v = 1 + y} ⊆ Set.range values11 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_nine] at hy
  rcases hy with ⟨i, rfl⟩
  exact one_add_values9_mem_range_values11 i

theorem recursiveValueSet_nine_add_one_subset_range :
    {v | ∃ y ∈ recursiveValueSet 9, v = y + 1} ⊆ Set.range values11 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [add_comm]
  exact one_add_recursiveValueSet_nine_subset_range ⟨y, hy, rfl⟩

theorem recursiveValueSet_five_eq_range_values5 :
    recursiveValueSet 5 = Set.range values5 := by
  ext x
  rw [recursiveValueSet_five]
  constructor
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0 : Fin 5), by simp [values5, values5Nat]⟩
    · exact ⟨(1 : Fin 5), by simp [values5, values5Nat, rt2_4]⟩
    · exact ⟨(2 : Fin 5), by simp [values5, values5Nat]⟩
    · exact ⟨(3 : Fin 5), by simp [values5, values5Nat]⟩
    · exact ⟨(4 : Fin 5), by simp [values5, values5Nat]⟩
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp [values5, values5Nat, rt2_4]

theorem recursiveValueSet_six_eq_range_values6 :
    recursiveValueSet 6 = Set.range values6 := by
  ext x
  rw [recursiveValueSet_six]
  constructor
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(0 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(1 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(2 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(3 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(4 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(5 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(6 : Fin 8), by simp [values6, values6Nat]⟩
    · exact ⟨(7 : Fin 8), by simp [values6, values6Nat]⟩
  · intro hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i <;> simp [values6, values6Nat]

set_option maxHeartbeats 2000000 in
theorem recursiveValueSet_eleven_subset_range :
    recursiveValueSet 11 ⊆ Set.range values11 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with hsqrt | hadd
  · exact recursiveValueSet_eleven_unary_subset_range hsqrt
  · rcases hadd with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rcases ha with rfl
      exact one_add_recursiveValueSet_nine_subset_range ⟨b, hb', rfl⟩
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values8_mem_range_values11 i
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl
      · exact one_add_values7_mem_range_values11 i
      · exact two_add_values7_mem_range_values11 i
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six_eq_range_values6] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_values6_mem_range_values11 i
      · exact sqrt_two_add_values6_mem_range_values11 i
      · exact two_add_values6_mem_range_values11 i
    · rw [recursiveValueSet_five_eq_range_values5] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five_eq_range_values5] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values5_add_values5_mem_range_values11 i j
    · rw [recursiveValueSet_six_eq_range_values6] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl | rfl
      · simpa [add_comm] using one_add_values6_mem_range_values11 i
      · simpa [add_comm] using sqrt_two_add_values6_mem_range_values11 i
      · simpa [add_comm] using two_add_values6_mem_range_values11 i
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · simpa [add_comm] using one_add_values7_mem_range_values11 i
      · simpa [add_comm] using two_add_values7_mem_range_values11 i
    · rw [recursiveValueSet_eight] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      simpa [add_comm] using one_add_values8_mem_range_values11 i
    · have ha' : a ∈ recursiveValueSet 9 := by simpa using ha
      simp [recursiveValueSet] at hb
      rcases hb with rfl
      exact recursiveValueSet_nine_add_one_subset_range ⟨a, ha', rfl⟩

theorem recursiveValueSet_eleven :
    recursiveValueSet 11 = Set.range values11 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_eleven_subset_range
  · exact values11_range_subset_recursiveValueSet_eleven

theorem recursiveValueSet_eleven_ncard :
    (recursiveValueSet 11).ncard = 91 := by
  rw [recursiveValueSet_eleven, values11_range_ncard]

/-- OEIS A158415 has value `91` at `n = 11`. -/
theorem a158415_eleven : a158415 11 = 91 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_eleven_ncard

end Expr

export Expr (a158415_eleven)

end A158415

end LeanProofs
