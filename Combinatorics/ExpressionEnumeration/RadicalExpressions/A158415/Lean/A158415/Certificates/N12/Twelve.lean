import A158415.Certificates.N11.Eleven

/-!
# Size-twelve certificate for OEIS A158415

This module records the 154 exact representatives discovered for size 12 and
proves that this table is exactly the split-recursive value set, yielding
`a158415 12 = 154`.
-/

namespace LeanProofs

namespace A158415

namespace Expr

open Set

noncomputable def values12Nat : Nat → ℝ
  | 0 => Real.sqrt (values11 (0 : Fin 91))
  | 1 => Real.sqrt (values11 (1 : Fin 91))
  | 2 => Real.sqrt (values11 (2 : Fin 91))
  | 3 => Real.sqrt (values11 (3 : Fin 91))
  | 4 => Real.sqrt (values11 (4 : Fin 91))
  | 5 => Real.sqrt (values11 (5 : Fin 91))
  | 6 => Real.sqrt (values11 (6 : Fin 91))
  | 7 => Real.sqrt (values11 (7 : Fin 91))
  | 8 => Real.sqrt (values11 (8 : Fin 91))
  | 9 => Real.sqrt (values11 (9 : Fin 91))
  | 10 => Real.sqrt (values11 (10 : Fin 91))
  | 11 => Real.sqrt (values11 (11 : Fin 91))
  | 12 => Real.sqrt (values11 (12 : Fin 91))
  | 13 => Real.sqrt (values11 (13 : Fin 91))
  | 14 => Real.sqrt (values11 (14 : Fin 91))
  | 15 => Real.sqrt (values11 (15 : Fin 91))
  | 16 => Real.sqrt (values11 (16 : Fin 91))
  | 17 => Real.sqrt (values11 (17 : Fin 91))
  | 18 => Real.sqrt (values11 (18 : Fin 91))
  | 19 => Real.sqrt (values11 (19 : Fin 91))
  | 20 => Real.sqrt (values11 (20 : Fin 91))
  | 21 => Real.sqrt (values11 (21 : Fin 91))
  | 22 => Real.sqrt (values11 (22 : Fin 91))
  | 23 => Real.sqrt (values11 (23 : Fin 91))
  | 24 => Real.sqrt (values11 (24 : Fin 91))
  | 25 => Real.sqrt (values11 (25 : Fin 91))
  | 26 => Real.sqrt (values11 (26 : Fin 91))
  | 27 => Real.sqrt (values11 (27 : Fin 91))
  | 28 => Real.sqrt (values11 (28 : Fin 91))
  | 29 => Real.sqrt (values11 (29 : Fin 91))
  | 30 => Real.sqrt (values11 (30 : Fin 91))
  | 31 => Real.sqrt (values11 (31 : Fin 91))
  | 32 => Real.sqrt (values11 (32 : Fin 91))
  | 33 => Real.sqrt (values11 (33 : Fin 91))
  | 34 => Real.sqrt (values11 (34 : Fin 91))
  | 35 => Real.sqrt (values11 (35 : Fin 91))
  | 36 => Real.sqrt (values11 (36 : Fin 91))
  | 37 => Real.sqrt (values11 (37 : Fin 91))
  | 38 => Real.sqrt (values11 (38 : Fin 91))
  | 39 => Real.sqrt (values11 (39 : Fin 91))
  | 40 => Real.sqrt (values11 (40 : Fin 91))
  | 41 => Real.sqrt (values11 (41 : Fin 91))
  | 42 => Real.sqrt (values11 (42 : Fin 91))
  | 43 => Real.sqrt (values11 (43 : Fin 91))
  | 44 => Real.sqrt (values11 (44 : Fin 91))
  | 45 => Real.sqrt (values11 (45 : Fin 91))
  | 46 => Real.sqrt (values11 (46 : Fin 91))
  | 47 => Real.sqrt (values11 (47 : Fin 91))
  | 48 => Real.sqrt (values11 (48 : Fin 91))
  | 49 => Real.sqrt (values11 (49 : Fin 91))
  | 50 => Real.sqrt (values11 (50 : Fin 91))
  | 51 => Real.sqrt (values11 (51 : Fin 91))
  | 52 => Real.sqrt (values11 (52 : Fin 91))
  | 53 => Real.sqrt (values11 (53 : Fin 91))
  | 54 => Real.sqrt (values11 (54 : Fin 91))
  | 55 => Real.sqrt (values11 (55 : Fin 91))
  | 56 => Real.sqrt (values11 (56 : Fin 91))
  | 57 => Real.sqrt (values11 (57 : Fin 91))
  | 58 => Real.sqrt (values11 (58 : Fin 91))
  | 59 => Real.sqrt (values11 (59 : Fin 91))
  | 60 => Real.sqrt (values11 (60 : Fin 91))
  | 61 => Real.sqrt (values11 (61 : Fin 91))
  | 62 => Real.sqrt (values11 (62 : Fin 91))
  | 63 => Real.sqrt (values11 (63 : Fin 91))
  | 64 => Real.sqrt (values11 (64 : Fin 91))
  | 65 => Real.sqrt (values11 (65 : Fin 91))
  | 66 => Real.sqrt (values11 (66 : Fin 91))
  | 67 => Real.sqrt (values11 (67 : Fin 91))
  | 68 => Real.sqrt (values11 (68 : Fin 91))
  | 69 => Real.sqrt (values11 (69 : Fin 91))
  | 70 => Real.sqrt (values11 (70 : Fin 91))
  | 71 => Real.sqrt (values11 (71 : Fin 91))
  | 72 => Real.sqrt (values11 (72 : Fin 91))
  | 73 => Real.sqrt (values11 (73 : Fin 91))
  | 74 => Real.sqrt (values11 (74 : Fin 91))
  | 75 => Real.sqrt (values11 (75 : Fin 91))
  | 76 => Real.sqrt (values11 (76 : Fin 91))
  | 77 => Real.sqrt (values11 (77 : Fin 91))
  | 78 => Real.sqrt (values11 (78 : Fin 91))
  | 79 => Real.sqrt (values11 (79 : Fin 91))
  | 80 => Real.sqrt (values11 (80 : Fin 91))
  | 81 => Real.sqrt (values11 (81 : Fin 91))
  | 82 => Real.sqrt (values11 (82 : Fin 91))
  | 83 => Real.sqrt (values11 (83 : Fin 91))
  | 84 => Real.sqrt (values11 (84 : Fin 91))
  | 85 => Real.sqrt (values11 (85 : Fin 91))
  | 86 => Real.sqrt (values11 (86 : Fin 91))
  | 87 => 1 + values10 (1 : Fin 54)
  | 88 => 1 + values10 (2 : Fin 54)
  | 89 => 1 + values10 (3 : Fin 54)
  | 90 => 1 + values10 (4 : Fin 54)
  | 91 => 1 + values10 (5 : Fin 54)
  | 92 => Real.sqrt (values11 (87 : Fin 91))
  | 93 => 1 + values10 (6 : Fin 54)
  | 94 => 1 + values10 (7 : Fin 54)
  | 95 => 1 + values10 (8 : Fin 54)
  | 96 => Real.sqrt (values11 (88 : Fin 91))
  | 97 => 1 + values10 (9 : Fin 54)
  | 98 => 1 + values10 (10 : Fin 54)
  | 99 => 1 + values10 (11 : Fin 54)
  | 100 => 1 + values10 (12 : Fin 54)
  | 101 => 1 + values10 (13 : Fin 54)
  | 102 => 1 + values10 (14 : Fin 54)
  | 103 => Real.sqrt (values11 (89 : Fin 91))
  | 104 => 1 + values10 (15 : Fin 54)
  | 105 => values5 (1 : Fin 5) + values6 (1 : Fin 8)
  | 106 => 1 + values10 (16 : Fin 54)
  | 107 => 1 + values10 (17 : Fin 54)
  | 108 => 1 + values10 (18 : Fin 54)
  | 109 => values5 (1 : Fin 5) + values6 (2 : Fin 8)
  | 110 => 1 + values10 (19 : Fin 54)
  | 111 => 1 + values10 (20 : Fin 54)
  | 112 => 1 + values10 (21 : Fin 54)
  | 113 => Real.sqrt (values11 (90 : Fin 91))
  | 114 => Real.sqrt 2 + values7 (1 : Fin 13)
  | 115 => 1 + values10 (22 : Fin 54)
  | 116 => Real.sqrt 2 + values7 (2 : Fin 13)
  | 117 => 1 + values10 (23 : Fin 54)
  | 118 => 1 + values10 (24 : Fin 54)
  | 119 => 1 + values10 (25 : Fin 54)
  | 120 => Real.sqrt 2 + values7 (3 : Fin 13)
  | 121 => 1 + values10 (26 : Fin 54)
  | 122 => 1 + values10 (27 : Fin 54)
  | 123 => Real.sqrt 2 + values7 (4 : Fin 13)
  | 124 => 1 + values10 (28 : Fin 54)
  | 125 => 1 + values10 (29 : Fin 54)
  | 126 => Real.sqrt 2 + values7 (5 : Fin 13)
  | 127 => 1 + values10 (30 : Fin 54)
  | 128 => values5 (1 : Fin 5) + values6 (4 : Fin 8)
  | 129 => Real.sqrt 2 + values7 (6 : Fin 13)
  | 130 => 1 + values10 (31 : Fin 54)
  | 131 => 1 + values10 (32 : Fin 54)
  | 132 => 1 + values10 (33 : Fin 54)
  | 133 => 1 + values10 (34 : Fin 54)
  | 134 => Real.sqrt 2 + values7 (7 : Fin 13)
  | 135 => 1 + values10 (35 : Fin 54)
  | 136 => 1 + values10 (36 : Fin 54)
  | 137 => 1 + values10 (37 : Fin 54)
  | 138 => 1 + values10 (38 : Fin 54)
  | 139 => 1 + values10 (39 : Fin 54)
  | 140 => 1 + values10 (40 : Fin 54)
  | 141 => 1 + values10 (41 : Fin 54)
  | 142 => 1 + values10 (42 : Fin 54)
  | 143 => 1 + values10 (43 : Fin 54)
  | 144 => 1 + values10 (44 : Fin 54)
  | 145 => 1 + values10 (45 : Fin 54)
  | 146 => 1 + values10 (46 : Fin 54)
  | 147 => 1 + values10 (47 : Fin 54)
  | 148 => 1 + values10 (48 : Fin 54)
  | 149 => 1 + values10 (49 : Fin 54)
  | 150 => 1 + values10 (50 : Fin 54)
  | 151 => 1 + values10 (51 : Fin 54)
  | 152 => 1 + values10 (52 : Fin 54)
  | 153 => 1 + values10 (53 : Fin 54)
  | _ => 0

noncomputable def values12 (i : Fin 154) : ℝ :=
  values12Nat i.1

set_option linter.unusedSimpArgs false in
macro "a158415_twelve_table" : tactic =>
  `(tactic|
    (simp [values12, values12Nat, values11, values11Nat, values10, values10Nat,
      values9, values9List, values8, values8List, values7, values7List, values6,
      values6Nat, values5, values5Nat, rt2_4, rt2_8, rt2_16, rt2_32, rt2_64,
      rt3_4, rt3_8, rt3_16, sqrt_one_add_sqrt_two,
      sqrt_sqrt_one_add_sqrt_two, sqrt_sqrt_sqrt_one_add_sqrt_two,
      sqrt_one_add_rt2_4, sqrt_sqrt_one_add_rt2_4, sqrt_one_add_rt2_8,
      sqrt_one_add_sqrt_three, sqrt_two_add_sqrt_two, sqrt_four, add_comm,
      add_assoc, add_left_comm, two_mul] <;> ring_nf))

theorem values11_nonneg (i : Fin 91) : (0 : ℝ) ≤ values11 i := by
  have h0 : (0 : ℝ) ≤ values11 (0 : Fin 91) := by
    norm_num [values11, values11Nat]
  exact h0.trans (values11_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values11_strictMono :
    StrictMono fun i : Fin 91 => Real.sqrt (values11 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values11_nonneg i) (values11_strictMono hij)

set_option linter.unusedTactic false in
theorem values12_special_86 :
    values12 (86 : Fin 154) < values12 (87 : Fin 154) := by
  have hleft : values12 (86 : Fin 154) < (2001 / 1000 : ℝ) := by
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by a158415_twelve_table]
    change Real.sqrt (values11 (86 : Fin 91)) < (2001 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2001 / 1000 : ℝ))]
    norm_num
    change values11 (86 : Fin 91) < (4004001 / 1000000 : ℝ)
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by a158415_twelve_table]
    change 1 + values9 (28 : Fin 33) < (4004001 / 1000000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values9 (28 : Fin 33) < (3001 / 1000 : ℝ) := by
      rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (8 : Fin 13) < (3001 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values7 (8 : Fin 13) < (20001 / 10000 : ℝ) := by
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (0 : Fin 5) < (20001 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values5 (0 : Fin 5) < (100001 / 100000 : ℝ) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change Real.sqrt (1) < (100001 / 100000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (100001 / 100000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2001 / 1000 : ℝ) < values12 (87 : Fin 154) := by
    rw [show values12 (87 : Fin 154) = 1 + values10 (1 : Fin 54) by a158415_twelve_table]
    change (2001 / 1000 : ℝ) < 1 + values10 (1 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (201 / 200 : ℝ) < values10 (1 : Fin 54) := by
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by a158415_twelve_table]
      change (201 / 200 : ℝ) < Real.sqrt (values9 (1 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (40401 / 40000 : ℝ) < values9 (1 : Fin 33)
      rw [show values9 (1 : Fin 33) = Real.sqrt (values8 (1 : Fin 20)) by a158415_twelve_table]
      change (40401 / 40000 : ℝ) < Real.sqrt (values8 (1 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1632240801 / 1600000000 : ℝ) < values8 (1 : Fin 20)
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (1632240801 / 1600000000 : ℝ) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2664210032449121601 / 2560000000000000000 : ℝ) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (2664210032449121601 / 2560000000000000000 : ℝ) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (7098015097002549574145912676484803201 / 6553600000000000000000000000000000000 : ℝ) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (7098015097002549574145912676484803201 / 6553600000000000000000000000000000000 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (50381818317276113240557224617393945529897613634431731589017585895699846401 / 42949672960000000000000000000000000000000000000000000000000000000000000000 : ℝ) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (50381818317276113240557224617393945529897613634431731589017585895699846401 / 42949672960000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2538327616955018886730420651552214215195535028071120035836117004859737444889844231429717625404728668161769600154876137639246888254138012774992652801 / 1844674407370955161600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt 2
      change (2538327616955018886730420651552214215195535028071120035836117004859737444889844231429717625404728668161769600154876137639246888254138012774992652801 / 1844674407370955161600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_91 :
    values12 (91 : Fin 154) < values12 (92 : Fin 154) := by
  have hleft : values12 (91 : Fin 154) < (409 / 200 : ℝ) := by
    rw [show values12 (91 : Fin 154) = 1 + values10 (5 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (5 : Fin 54) < (409 / 200 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (5 : Fin 54) < (10443 / 10000 : ℝ) := by
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (5 : Fin 33)) < (10443 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10443 / 10000 : ℝ))]
      norm_num
      change values9 (5 : Fin 33) < (109056249 / 100000000 : ℝ)
      rw [show values9 (5 : Fin 33) = Real.sqrt (values8 (5 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (5 : Fin 20)) < (109056249 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109056249 / 100000000 : ℝ))]
      norm_num
      change values8 (5 : Fin 20) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893265445950001 / 10000000000000000 : ℝ))]
      norm_num
      change values7 (5 : Fin 13) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ))]
      norm_num
      change values6 (5 : Fin 8) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (409 / 200 : ℝ) < values12 (92 : Fin 154) := by
    rw [show values12 (92 : Fin 154) = Real.sqrt (values11 (87 : Fin 91)) by a158415_twelve_table]
    change (409 / 200 : ℝ) < Real.sqrt (values11 (87 : Fin 91))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (167281 / 40000 : ℝ) < values11 (87 : Fin 91)
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by a158415_twelve_table]
    change (167281 / 40000 : ℝ) < 1 + values9 (29 : Fin 33)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (3189 / 1000 : ℝ) < values9 (29 : Fin 33) := by
      rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
      change (3189 / 1000 : ℝ) < 1 + values7 (9 : Fin 13)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (5473 / 2500 : ℝ) < values7 (9 : Fin 13) := by
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change (5473 / 2500 : ℝ) < 1 + values5 (1 : Fin 5)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (1189207 / 1000000 : ℝ) < values5 (1 : Fin 5) := by
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (1189207 / 1000000 : ℝ) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1414213288849 / 1000000000000 : ℝ) < Real.sqrt 2
          change (1414213288849 / 1000000000000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_92 :
    values12 (92 : Fin 154) < values12 (93 : Fin 154) := by
  have hleft : values12 (92 : Fin 154) < (2047 / 1000 : ℝ) := by
    rw [show values12 (92 : Fin 154) = Real.sqrt (values11 (87 : Fin 91)) by a158415_twelve_table]
    change Real.sqrt (values11 (87 : Fin 91)) < (2047 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2047 / 1000 : ℝ))]
    norm_num
    change values11 (87 : Fin 91) < (4190209 / 1000000 : ℝ)
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by a158415_twelve_table]
    change 1 + values9 (29 : Fin 33) < (4190209 / 1000000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values9 (29 : Fin 33) < (31893 / 10000 : ℝ) := by
      rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (9 : Fin 13) < (31893 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (9 : Fin 13) < (218921 / 100000 : ℝ) := by
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (1 : Fin 5) < (218921 / 100000 : ℝ)
        have h5 : 1 < (10000001 / 10000000 : ℝ) := by
          norm_num
        have h6 : values5 (1 : Fin 5) < (148651 / 125000 : ℝ) := by
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (148651 / 125000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (148651 / 125000 : ℝ))]
          norm_num
          change Real.sqrt 2 < (22097119801 / 15625000000 : ℝ)
          change Real.sqrt (2) < (22097119801 / 15625000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22097119801 / 15625000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2047 / 1000 : ℝ) < values12 (93 : Fin 154) := by
    rw [show values12 (93 : Fin 154) = 1 + values10 (6 : Fin 54) by a158415_twelve_table]
    change (2047 / 1000 : ℝ) < 1 + values10 (6 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (132 / 125 : ℝ) < values10 (6 : Fin 54) := by
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by a158415_twelve_table]
      change (132 / 125 : ℝ) < Real.sqrt (values9 (6 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (17424 / 15625 : ℝ) < values9 (6 : Fin 33)
      rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
      change (17424 / 15625 : ℝ) < Real.sqrt (values8 (6 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (303595776 / 244140625 : ℝ) < values8 (6 : Fin 20)
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (303595776 / 244140625 : ℝ) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (92170395205042176 / 59604644775390625 : ℝ) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (92170395205042176 / 59604644775390625 : ℝ) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (8495381752253661749201333938814976 / 3552713678800500929355621337890625 : ℝ) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (8495381752253661749201333938814976 / 3552713678800500929355621337890625 : ℝ) < 1 + Real.sqrt 2
      have h9 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h10 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_95 :
    values12 (95 : Fin 154) < values12 (96 : Fin 154) := by
  have hleft : values12 (95 : Fin 154) < (2091 / 1000 : ℝ) := by
    rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (8 : Fin 54) < (2091 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (8 : Fin 54) < (5453 / 5000 : ℝ) := by
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (8 : Fin 33)) < (5453 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5453 / 5000 : ℝ))]
      norm_num
      change values9 (8 : Fin 33) < (29735209 / 25000000 : ℝ)
      rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (8 : Fin 20)) < (29735209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (29735209 / 25000000 : ℝ))]
      norm_num
      change values8 (8 : Fin 20) < (884182654273681 / 625000000000000 : ℝ)
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (8 : Fin 13)) < (884182654273681 / 625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (884182654273681 / 625000000000000 : ℝ))]
      norm_num
      change values7 (8 : Fin 13) < (781778966118451701933649289761 / 390625000000000000000000000000 : ℝ)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (0 : Fin 5) < (781778966118451701933649289761 / 390625000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values5 (0 : Fin 5) < (10001 / 10000 : ℝ) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change Real.sqrt (1) < (10001 / 10000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10001 / 10000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (2091 / 1000 : ℝ) < values12 (96 : Fin 154) := by
    rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by a158415_twelve_table]
    change (2091 / 1000 : ℝ) < Real.sqrt (values11 (88 : Fin 91))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (4372281 / 1000000 : ℝ) < values11 (88 : Fin 91)
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by a158415_twelve_table]
    change (4372281 / 1000000 : ℝ) < 1 + values9 (30 : Fin 33)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1707 / 500 : ℝ) < values9 (30 : Fin 33) := by
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change (1707 / 500 : ℝ) < 1 + values7 (10 : Fin 13)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (12071 / 5000 : ℝ) < values7 (10 : Fin 13) := by
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change (12071 / 5000 : ℝ) < 1 + values5 (2 : Fin 5)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (141421 / 100000 : ℝ) < values5 (2 : Fin 5) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (141421 / 100000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_96 :
    values12 (96 : Fin 154) < values12 (97 : Fin 154) := by
  have hleft : values12 (96 : Fin 154) < (1051 / 500 : ℝ) := by
    rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by a158415_twelve_table]
    change Real.sqrt (values11 (88 : Fin 91)) < (1051 / 500 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (1051 / 500 : ℝ))]
    norm_num
    change values11 (88 : Fin 91) < (1104601 / 250000 : ℝ)
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by a158415_twelve_table]
    change 1 + values9 (30 : Fin 33) < (1104601 / 250000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values9 (30 : Fin 33) < (683 / 200 : ℝ) := by
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (10 : Fin 13) < (683 / 200 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values7 (10 : Fin 13) < (24143 / 10000 : ℝ) := by
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (24143 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values5 (2 : Fin 5) < (70711 / 50000 : ℝ) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (70711 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1051 / 500 : ℝ) < values12 (97 : Fin 154) := by
    rw [show values12 (97 : Fin 154) = 1 + values10 (9 : Fin 54) by a158415_twelve_table]
    change (1051 / 500 : ℝ) < 1 + values10 (9 : Fin 54)
    have h7 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h8 : (2757 / 2500 : ℝ) < values10 (9 : Fin 54) := by
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by a158415_twelve_table]
      change (2757 / 2500 : ℝ) < Real.sqrt (values9 (9 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (7601049 / 6250000 : ℝ) < values9 (9 : Fin 33)
      rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
      change (7601049 / 6250000 : ℝ) < Real.sqrt (values8 (9 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (57775945900401 / 39062500000000 : ℝ) < values8 (9 : Fin 20)
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (57775945900401 / 39062500000000 : ℝ) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3338059924686063118611960801 / 1525878906250000000000000000 : ℝ) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (3338059924686063118611960801 / 1525878906250000000000000000 : ℝ) < 1 + values5 (1 : Fin 5)
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : ℝ) < Real.sqrt 2
        change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_102 :
    values12 (102 : Fin 154) < values12 (103 : Fin 154) := by
  have hleft : values12 (102 : Fin 154) < (2217 / 1000 : ℝ) := by
    rw [show values12 (102 : Fin 154) = 1 + values10 (14 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (14 : Fin 54) < (2217 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (14 : Fin 54) < (3041 / 2500 : ℝ) := by
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (14 : Fin 33)) < (3041 / 2500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (3041 / 2500 : ℝ))]
      norm_num
      change values9 (14 : Fin 33) < (9247681 / 6250000 : ℝ)
      rw [show values9 (14 : Fin 33) = Real.sqrt (values8 (14 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (14 : Fin 20)) < (9247681 / 6250000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9247681 / 6250000 : ℝ))]
      norm_num
      change values8 (14 : Fin 20) < (85519603877761 / 39062500000000 : ℝ)
      rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (2 : Fin 8) < (85519603877761 / 39062500000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values6 (2 : Fin 8) < (118921 / 100000 : ℝ) := by
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (118921 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118921 / 100000 : ℝ))]
        norm_num
        change values5 (2 : Fin 5) < (14142204241 / 10000000000 : ℝ)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (14142204241 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142204241 / 10000000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (2217 / 1000 : ℝ) < values12 (103 : Fin 154) := by
    rw [show values12 (103 : Fin 154) = Real.sqrt (values11 (89 : Fin 91)) by a158415_twelve_table]
    change (2217 / 1000 : ℝ) < Real.sqrt (values11 (89 : Fin 91))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (4915089 / 1000000 : ℝ) < values11 (89 : Fin 91)
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by a158415_twelve_table]
    change (4915089 / 1000000 : ℝ) < 1 + values9 (31 : Fin 33)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (3999 / 1000 : ℝ) < values9 (31 : Fin 33) := by
      rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
      change (3999 / 1000 : ℝ) < 1 + values7 (11 : Fin 13)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (29999 / 10000 : ℝ) < values7 (11 : Fin 13) := by
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (29999 / 10000 : ℝ) < 1 + values5 (3 : Fin 5)
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (199999 / 100000 : ℝ) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : ℝ) < 1 + 1
          have h11 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          have h12 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_103 :
    values12 (103 : Fin 154) < values12 (104 : Fin 154) := by
  have hleft : values12 (103 : Fin 154) < (2237 / 1000 : ℝ) := by
    rw [show values12 (103 : Fin 154) = Real.sqrt (values11 (89 : Fin 91)) by a158415_twelve_table]
    change Real.sqrt (values11 (89 : Fin 91)) < (2237 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2237 / 1000 : ℝ))]
    norm_num
    change values11 (89 : Fin 91) < (5004169 / 1000000 : ℝ)
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by a158415_twelve_table]
    change 1 + values9 (31 : Fin 33) < (5004169 / 1000000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values9 (31 : Fin 33) < (4001 / 1000 : ℝ) := by
      rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (11 : Fin 13) < (4001 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values7 (11 : Fin 13) < (30001 / 10000 : ℝ) := by
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (3 : Fin 5) < (30001 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values5 (3 : Fin 5) < (200001 / 100000 : ℝ) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (200001 / 100000 : ℝ)
          have h7 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2237 / 1000 : ℝ) < values12 (104 : Fin 154) := by
    rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by a158415_twelve_table]
    change (2237 / 1000 : ℝ) < 1 + values10 (15 : Fin 54)
    have h9 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h10 : (623 / 500 : ℝ) < values10 (15 : Fin 54) := by
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by a158415_twelve_table]
      change (623 / 500 : ℝ) < Real.sqrt (values9 (15 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : ℝ) < values9 (15 : Fin 33)
      rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
      change (388129 / 250000 : ℝ) < Real.sqrt (values8 (15 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : ℝ) < values8 (15 : Fin 20)
      rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
      change (150644120641 / 62500000000 : ℝ) < 1 + values6 (3 : Fin 8)
      have h11 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h12 : (707 / 500 : ℝ) < values6 (3 : Fin 8) := by
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (707 / 500 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (499849 / 250000 : ℝ) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (499849 / 250000 : ℝ) < 1 + 1
        have h13 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h14 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_104 :
    values12 (104 : Fin 154) < values12 (105 : Fin 154) := by
  have hleft : values12 (104 : Fin 154) < (2247 / 1000 : ℝ) := by
    rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (15 : Fin 54) < (2247 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (15 : Fin 54) < (6233 / 5000 : ℝ) := by
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (15 : Fin 33)) < (6233 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (6233 / 5000 : ℝ))]
      norm_num
      change values9 (15 : Fin 33) < (38850289 / 25000000 : ℝ)
      rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (15 : Fin 20)) < (38850289 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (38850289 / 25000000 : ℝ))]
      norm_num
      change values8 (15 : Fin 20) < (1509344955383521 / 625000000000000 : ℝ)
      rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (3 : Fin 8) < (1509344955383521 / 625000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values6 (3 : Fin 8) < (14143 / 10000 : ℝ) := by
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (3 : Fin 5)) < (14143 / 10000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
        norm_num
        change values5 (3 : Fin 5) < (200024449 / 100000000 : ℝ)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200024449 / 100000000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (2247 / 1000 : ℝ) < values12 (105 : Fin 154) := by
    rw [show values12 (105 : Fin 154) = values5 (1 : Fin 5) + values6 (1 : Fin 8) by a158415_twelve_table]
    change (2247 / 1000 : ℝ) < values5 (1 : Fin 5) + values6 (1 : Fin 8)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (109 / 100 : ℝ) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109 / 100 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : ℝ) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11881 / 10000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : ℝ) < Real.sqrt 2
      change (141158161 / 100000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_105 :
    values12 (105 : Fin 154) < values12 (106 : Fin 154) := by
  have hleft : values12 (105 : Fin 154) < (57 / 25 : ℝ) := by
    rw [show values12 (105 : Fin 154) = values5 (1 : Fin 5) + values6 (1 : Fin 8) by a158415_twelve_table]
    change values5 (1 : Fin 5) + values6 (1 : Fin 8) < (57 / 25 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
    have h2 : values6 (1 : Fin 8) < (5453 / 5000 : ℝ) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5453 / 5000 : ℝ))]
      norm_num
      change values5 (1 : Fin 5) < (29735209 / 25000000 : ℝ)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (29735209 / 25000000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (884182654273681 / 625000000000000 : ℝ)
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (884182654273681 / 625000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (57 / 25 : ℝ) < values12 (106 : Fin 154) := by
    rw [show values12 (106 : Fin 154) = 1 + values10 (16 : Fin 54) by a158415_twelve_table]
    change (57 / 25 : ℝ) < 1 + values10 (16 : Fin 54)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (257 / 200 : ℝ) < values10 (16 : Fin 54) := by
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by a158415_twelve_table]
      change (257 / 200 : ℝ) < Real.sqrt (values9 (16 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (66049 / 40000 : ℝ) < values9 (16 : Fin 33)
      rw [show values9 (16 : Fin 33) = Real.sqrt (values8 (16 : Fin 20)) by a158415_twelve_table]
      change (66049 / 40000 : ℝ) < Real.sqrt (values8 (16 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4362470401 / 1600000000 : ℝ) < values8 (16 : Fin 20)
      rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
      change (4362470401 / 1600000000 : ℝ) < 1 + values6 (4 : Fin 8)
      have h5 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h6 : (433 / 250 : ℝ) < values6 (4 : Fin 8) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (433 / 250 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : ℝ) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (187489 / 62500 : ℝ) < 1 + 2
        have h7 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h8 : (199999 / 100000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_108 :
    values12 (108 : Fin 154) < values12 (109 : Fin 154) := by
  have hleft : values12 (108 : Fin 154) < (59 / 25 : ℝ) := by
    rw [show values12 (108 : Fin 154) = 1 + values10 (18 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (18 : Fin 54) < (59 / 25 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (18 : Fin 54) < (6797 / 5000 : ℝ) := by
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (18 : Fin 33)) < (6797 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (6797 / 5000 : ℝ))]
      norm_num
      change values9 (18 : Fin 33) < (46199209 / 25000000 : ℝ)
      rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (18 : Fin 20)) < (46199209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (46199209 / 25000000 : ℝ))]
      norm_num
      change values8 (18 : Fin 20) < (2134366912225681 / 625000000000000 : ℝ)
      rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (6 : Fin 8) < (2134366912225681 / 625000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values6 (6 : Fin 8) < (24143 / 10000 : ℝ) := by
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (24143 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
          change Real.sqrt (2) < (70711 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (59 / 25 : ℝ) < values12 (109 : Fin 154) := by
    rw [show values12 (109 : Fin 154) = values5 (1 : Fin 5) + values6 (2 : Fin 8) by a158415_twelve_table]
    change (59 / 25 : ℝ) < values5 (1 : Fin 5) + values6 (2 : Fin 8)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1189 / 1000 : ℝ) < values6 (2 : Fin 8) := by
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_109 :
    values12 (109 : Fin 154) < values12 (110 : Fin 154) := by
  have hleft : values12 (109 : Fin 154) < (2379 / 1000 : ℝ) := by
    rw [show values12 (109 : Fin 154) = values5 (1 : Fin 5) + values6 (2 : Fin 8) by a158415_twelve_table]
    change values5 (1 : Fin 5) + values6 (2 : Fin 8) < (2379 / 1000 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
    have h2 : values6 (2 : Fin 8) < (11893 / 10000 : ℝ) := by
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change values5 (2 : Fin 5) < (141443449 / 100000000 : ℝ)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
    linarith
  have hright : (2379 / 1000 : ℝ) < values12 (110 : Fin 154) := by
    rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by a158415_twelve_table]
    change (2379 / 1000 : ℝ) < 1 + values10 (19 : Fin 54)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (707 / 500 : ℝ) < values10 (19 : Fin 54) := by
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by a158415_twelve_table]
      change (707 / 500 : ℝ) < Real.sqrt (values9 (19 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : ℝ) < values9 (19 : Fin 33)
      rw [show values9 (19 : Fin 33) = Real.sqrt (values8 (19 : Fin 20)) by a158415_twelve_table]
      change (499849 / 250000 : ℝ) < Real.sqrt (values8 (19 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (249849022801 / 62500000000 : ℝ) < values8 (19 : Fin 20)
      rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
      change (249849022801 / 62500000000 : ℝ) < 1 + values6 (7 : Fin 8)
      have h5 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h6 : (29999 / 10000 : ℝ) < values6 (7 : Fin 8) := by
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (29999 / 10000 : ℝ) < 1 + 2
        have h7 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h8 : (199999 / 100000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_112 :
    values12 (112 : Fin 154) < values12 (113 : Fin 154) := by
  have hleft : values12 (112 : Fin 154) < (1223 / 500 : ℝ) := by
    rw [show values12 (112 : Fin 154) = 1 + values10 (21 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (21 : Fin 54) < (1223 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values10 (21 : Fin 54) < (14459 / 10000 : ℝ) := by
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (21 : Fin 33)) < (14459 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14459 / 10000 : ℝ))]
      norm_num
      change values9 (21 : Fin 33) < (209062681 / 100000000 : ℝ)
      rw [show values9 (21 : Fin 33) = 1 + values7 (2 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (2 : Fin 13) < (209062681 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (2 : Fin 13) < (109051 / 100000 : ℝ) := by
        rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (2 : Fin 8)) < (109051 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109051 / 100000 : ℝ))]
        norm_num
        change values6 (2 : Fin 8) < (11892120601 / 10000000000 : ℝ)
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (11892120601 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11892120601 / 10000000000 : ℝ))]
        norm_num
        change values5 (2 : Fin 5) < (141422532388728601201 / 100000000000000000000 : ℝ)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (141422532388728601201 / 100000000000000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141422532388728601201 / 100000000000000000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (1223 / 500 : ℝ) < values12 (113 : Fin 154) := by
    rw [show values12 (113 : Fin 154) = Real.sqrt (values11 (90 : Fin 91)) by a158415_twelve_table]
    change (1223 / 500 : ℝ) < Real.sqrt (values11 (90 : Fin 91))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1495729 / 250000 : ℝ) < values11 (90 : Fin 91)
    rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by a158415_twelve_table]
    change (1495729 / 250000 : ℝ) < 1 + values9 (32 : Fin 33)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (4999 / 1000 : ℝ) < values9 (32 : Fin 33) := by
      rw [show values9 (32 : Fin 33) = 1 + values7 (12 : Fin 13) by a158415_twelve_table]
      change (4999 / 1000 : ℝ) < 1 + values7 (12 : Fin 13)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (39999 / 10000 : ℝ) < values7 (12 : Fin 13) := by
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change (39999 / 10000 : ℝ) < 1 + values5 (4 : Fin 5)
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (299999 / 100000 : ℝ) < values5 (4 : Fin 5) := by
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change (299999 / 100000 : ℝ) < 1 + 2
          have h11 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          have h12 : (1999999 / 1000000 : ℝ) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_113 :
    values12 (113 : Fin 154) < values12 (114 : Fin 154) := by
  have hleft : values12 (113 : Fin 154) < (49 / 20 : ℝ) := by
    rw [show values12 (113 : Fin 154) = Real.sqrt (values11 (90 : Fin 91)) by a158415_twelve_table]
    change Real.sqrt (values11 (90 : Fin 91)) < (49 / 20 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (49 / 20 : ℝ))]
    norm_num
    change values11 (90 : Fin 91) < (2401 / 400 : ℝ)
    rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by a158415_twelve_table]
    change 1 + values9 (32 : Fin 33) < (2401 / 400 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values9 (32 : Fin 33) < (50001 / 10000 : ℝ) := by
      rw [show values9 (32 : Fin 33) = 1 + values7 (12 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (12 : Fin 13) < (50001 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (12 : Fin 13) < (400001 / 100000 : ℝ) := by
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (4 : Fin 5) < (400001 / 100000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values5 (4 : Fin 5) < (3000001 / 1000000 : ℝ) := by
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (3000001 / 1000000 : ℝ)
          have h7 : 1 < (10000001 / 10000000 : ℝ) := by
            norm_num
          have h8 : 2 < (20000001 / 10000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (49 / 20 : ℝ) < values12 (114 : Fin 154) := by
    rw [show values12 (114 : Fin 154) = Real.sqrt 2 + values7 (1 : Fin 13) by a158415_twelve_table]
    change (49 / 20 : ℝ) < Real.sqrt 2 + values7 (1 : Fin 13)
    have h9 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (261 / 250 : ℝ) < values7 (1 : Fin 13) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (261 / 250 : ℝ) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : ℝ) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (68121 / 62500 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : ℝ) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (4640470641 / 3906250000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : ℝ) < Real.sqrt 2
      change (21533967769982950881 / 15258789062500000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_114 :
    values12 (114 : Fin 154) < values12 (115 : Fin 154) := by
  have hleft : values12 (114 : Fin 154) < (2459 / 1000 : ℝ) := by
    rw [show values12 (114 : Fin 154) = Real.sqrt 2 + values7 (1 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (1 : Fin 13) < (2459 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (1 : Fin 13) < (10443 / 10000 : ℝ) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (10443 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10443 / 10000 : ℝ))]
      norm_num
      change values6 (1 : Fin 8) < (109056249 / 100000000 : ℝ)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (109056249 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109056249 / 100000000 : ℝ))]
      norm_num
      change values5 (1 : Fin 5) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893265445950001 / 10000000000000000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      change Real.sqrt (2) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (2459 / 1000 : ℝ) < values12 (115 : Fin 154) := by
    rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by a158415_twelve_table]
    change (2459 / 1000 : ℝ) < 1 + values10 (22 : Fin 54)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (1479 / 1000 : ℝ) < values10 (22 : Fin 54) := by
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by a158415_twelve_table]
      change (1479 / 1000 : ℝ) < Real.sqrt (values9 (22 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2187441 / 1000000 : ℝ) < values9 (22 : Fin 33)
      rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
      change (2187441 / 1000000 : ℝ) < 1 + values7 (3 : Fin 13)
      have h5 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h6 : (1189 / 1000 : ℝ) < values7 (3 : Fin 13) := by
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change (1189 / 1000 : ℝ) < Real.sqrt (values6 (3 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : ℝ) < values6 (3 : Fin 8)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (1413721 / 1000000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1998607065841 / 1000000000000 : ℝ) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (1998607065841 / 1000000000000 : ℝ) < 1 + 1
        have h7 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h8 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_115 :
    values12 (115 : Fin 154) < values12 (116 : Fin 154) := by
  have hleft : values12 (115 : Fin 154) < (62 / 25 : ℝ) := by
    rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (22 : Fin 54) < (62 / 25 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (22 : Fin 54) < (3699 / 2500 : ℝ) := by
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (22 : Fin 33)) < (3699 / 2500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (3699 / 2500 : ℝ))]
      norm_num
      change values9 (22 : Fin 33) < (13682601 / 6250000 : ℝ)
      rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (3 : Fin 13) < (13682601 / 6250000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values7 (3 : Fin 13) < (118921 / 100000 : ℝ) := by
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (3 : Fin 8)) < (118921 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118921 / 100000 : ℝ))]
        norm_num
        change values6 (3 : Fin 8) < (14142204241 / 10000000000 : ℝ)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (3 : Fin 5)) < (14142204241 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142204241 / 10000000000 : ℝ))]
        norm_num
        change values5 (3 : Fin 5) < (200001940794158386081 / 100000000000000000000 : ℝ)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001940794158386081 / 100000000000000000000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (62 / 25 : ℝ) < values12 (116 : Fin 154) := by
    rw [show values12 (116 : Fin 154) = Real.sqrt 2 + values7 (2 : Fin 13) by a158415_twelve_table]
    change (62 / 25 : ℝ) < Real.sqrt 2 + values7 (2 : Fin 13)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (109 / 100 : ℝ) < values7 (2 : Fin 13) := by
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change (109 / 100 : ℝ) < Real.sqrt (values6 (2 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : ℝ) < values6 (2 : Fin 8)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (11881 / 10000 : ℝ) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : ℝ) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (141158161 / 100000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_116 :
    values12 (116 : Fin 154) < values12 (117 : Fin 154) := by
  have hleft : values12 (116 : Fin 154) < (501 / 200 : ℝ) := by
    rw [show values12 (116 : Fin 154) = Real.sqrt 2 + values7 (2 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (2 : Fin 13) < (501 / 200 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (2 : Fin 13) < (5453 / 5000 : ℝ) := by
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (2 : Fin 8)) < (5453 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5453 / 5000 : ℝ))]
      norm_num
      change values6 (2 : Fin 8) < (29735209 / 25000000 : ℝ)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (29735209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (29735209 / 25000000 : ℝ))]
      norm_num
      change values5 (2 : Fin 5) < (884182654273681 / 625000000000000 : ℝ)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (884182654273681 / 625000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (501 / 200 : ℝ) < values12 (117 : Fin 154) := by
    rw [show values12 (117 : Fin 154) = 1 + values10 (23 : Fin 54) by a158415_twelve_table]
    change (501 / 200 : ℝ) < 1 + values10 (23 : Fin 54)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (1521 / 1000 : ℝ) < values10 (23 : Fin 54) := by
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by a158415_twelve_table]
      change (1521 / 1000 : ℝ) < Real.sqrt (values9 (23 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2313441 / 1000000 : ℝ) < values9 (23 : Fin 33)
      rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
      change (2313441 / 1000000 : ℝ) < 1 + values7 (4 : Fin 13)
      have h5 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h6 : (329 / 250 : ℝ) < values7 (4 : Fin 13) := by
        rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
        change (329 / 250 : ℝ) < Real.sqrt (values6 (4 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108241 / 62500 : ℝ) < values6 (4 : Fin 8)
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (108241 / 62500 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11716114081 / 3906250000 : ℝ) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (11716114081 / 3906250000 : ℝ) < 1 + 2
        have h7 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h8 : (19999 / 10000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_119 :
    values12 (119 : Fin 154) < values12 (120 : Fin 154) := by
  have hleft : values12 (119 : Fin 154) < (2599 / 1000 : ℝ) := by
    rw [show values12 (119 : Fin 154) = 1 + values10 (25 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (25 : Fin 54) < (2599 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (25 : Fin 54) < (15981 / 10000 : ℝ) := by
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (25 : Fin 33)) < (15981 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (15981 / 10000 : ℝ))]
      norm_num
      change values9 (25 : Fin 33) < (255392361 / 100000000 : ℝ)
      rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (6 : Fin 13) < (255392361 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (6 : Fin 13) < (7769 / 5000 : ℝ) := by
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (7769 / 5000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (7769 / 5000 : ℝ))]
        norm_num
        change values6 (6 : Fin 8) < (60357361 / 25000000 : ℝ)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (60357361 / 25000000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
          change Real.sqrt (2) < (70711 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2599 / 1000 : ℝ) < values12 (120 : Fin 154) := by
    rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by a158415_twelve_table]
    change (2599 / 1000 : ℝ) < Real.sqrt 2 + values7 (3 : Fin 13)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1189 / 1000 : ℝ) < values7 (3 : Fin 13) := by
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (values6 (3 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < values6 (3 : Fin 8)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change (1413721 / 1000000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : ℝ) < values5 (3 : Fin 5)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : ℝ) < 1 + 1
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_120 :
    values12 (120 : Fin 154) < values12 (121 : Fin 154) := by
  have hleft : values12 (120 : Fin 154) < (651 / 250 : ℝ) := by
    rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (3 : Fin 13) < (651 / 250 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (3 : Fin 13) < (11893 / 10000 : ℝ) := by
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (3 : Fin 8)) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change values6 (3 : Fin 8) < (141443449 / 100000000 : ℝ)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (3 : Fin 5)) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
      change values5 (3 : Fin 5) < (20006249265015601 / 10000000000000000 : ℝ)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20006249265015601 / 10000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (651 / 250 : ℝ) < values12 (121 : Fin 154) := by
    rw [show values12 (121 : Fin 154) = 1 + values10 (26 : Fin 54) by a158415_twelve_table]
    change (651 / 250 : ℝ) < 1 + values10 (26 : Fin 54)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (413 / 250 : ℝ) < values10 (26 : Fin 54) := by
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by a158415_twelve_table]
      change (413 / 250 : ℝ) < Real.sqrt (values9 (26 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (170569 / 62500 : ℝ) < values9 (26 : Fin 33)
      rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
      change (170569 / 62500 : ℝ) < 1 + values7 (7 : Fin 13)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (433 / 250 : ℝ) < values7 (7 : Fin 13) := by
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (433 / 250 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : ℝ) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (187489 / 62500 : ℝ) < 1 + 2
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (199999 / 100000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_122 :
    values12 (122 : Fin 154) < values12 (123 : Fin 154) := by
  have hleft : values12 (122 : Fin 154) < (1341 / 500 : ℝ) := by
    rw [show values12 (122 : Fin 154) = 1 + values10 (27 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (27 : Fin 54) < (1341 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values10 (27 : Fin 54) < (8409 / 5000 : ℝ) := by
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (27 : Fin 33)) < (8409 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (8409 / 5000 : ℝ))]
      norm_num
      change values9 (27 : Fin 33) < (70711281 / 25000000 : ℝ)
      rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
      change Real.sqrt 2 + Real.sqrt 2 < (70711281 / 25000000 : ℝ)
      have h3 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
        change Real.sqrt (2) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
      have h4 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
        change Real.sqrt (2) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (1341 / 500 : ℝ) < values12 (123 : Fin 154) := by
    rw [show values12 (123 : Fin 154) = Real.sqrt 2 + values7 (4 : Fin 13) by a158415_twelve_table]
    change (1341 / 500 : ℝ) < Real.sqrt 2 + values7 (4 : Fin 13)
    have h5 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (329 / 250 : ℝ) < values7 (4 : Fin 13) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (329 / 250 : ℝ) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : ℝ) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (108241 / 62500 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : ℝ) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (11716114081 / 3906250000 : ℝ) < 1 + 2
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (19999 / 10000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_123 :
    values12 (123 : Fin 154) < values12 (124 : Fin 154) := by
  have hleft : values12 (123 : Fin 154) < (2731 / 1000 : ℝ) := by
    rw [show values12 (123 : Fin 154) = Real.sqrt 2 + values7 (4 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (4 : Fin 13) < (2731 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (4 : Fin 13) < (13161 / 10000 : ℝ) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (13161 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (13161 / 10000 : ℝ))]
      norm_num
      change values6 (4 : Fin 8) < (173211921 / 100000000 : ℝ)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (173211921 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (173211921 / 100000000 : ℝ))]
      norm_num
      change values5 (4 : Fin 5) < (30002369576510241 / 10000000000000000 : ℝ)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30002369576510241 / 10000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (2731 / 1000 : ℝ) < values12 (124 : Fin 154) := by
    rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by a158415_twelve_table]
    change (2731 / 1000 : ℝ) < 1 + values10 (28 : Fin 54)
    have h5 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h6 : (433 / 250 : ℝ) < values10 (28 : Fin 54) := by
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values9 (28 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values9 (28 : Fin 33)
      rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + values7 (8 : Fin 13)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (199999 / 100000 : ℝ) < values7 (8 : Fin 13) := by
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change (199999 / 100000 : ℝ) < 1 + values5 (0 : Fin 5)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (999999 / 1000000 : ℝ) < values5 (0 : Fin 5) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change (999999 / 1000000 : ℝ) < Real.sqrt (1)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_125 :
    values12 (125 : Fin 154) < values12 (126 : Fin 154) := by
  have hleft : values12 (125 : Fin 154) < (1393 / 500 : ℝ) := by
    rw [show values12 (125 : Fin 154) = 1 + values10 (29 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (29 : Fin 54) < (1393 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values10 (29 : Fin 54) < (22323 / 12500 : ℝ) := by
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (29 : Fin 33)) < (22323 / 12500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22323 / 12500 : ℝ))]
      norm_num
      change values9 (29 : Fin 33) < (498316329 / 156250000 : ℝ)
      rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (9 : Fin 13) < (498316329 / 156250000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values7 (9 : Fin 13) < (218921 / 100000 : ℝ) := by
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (1 : Fin 5) < (218921 / 100000 : ℝ)
        have h5 : 1 < (10000001 / 10000000 : ℝ) := by
          norm_num
        have h6 : values5 (1 : Fin 5) < (148651 / 125000 : ℝ) := by
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (148651 / 125000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (148651 / 125000 : ℝ))]
          norm_num
          change Real.sqrt 2 < (22097119801 / 15625000000 : ℝ)
          change Real.sqrt (2) < (22097119801 / 15625000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22097119801 / 15625000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1393 / 500 : ℝ) < values12 (126 : Fin 154) := by
    rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by a158415_twelve_table]
    change (1393 / 500 : ℝ) < Real.sqrt 2 + values7 (5 : Fin 13)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (707 / 500 : ℝ) < values7 (5 : Fin 13) := by
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change (707 / 500 : ℝ) < Real.sqrt (values6 (5 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : ℝ) < values6 (5 : Fin 8)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change (499849 / 250000 : ℝ) < 1 + 1
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_126 :
    values12 (126 : Fin 154) < values12 (127 : Fin 154) := by
  have hleft : values12 (126 : Fin 154) < (2829 / 1000 : ℝ) := by
    rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (5 : Fin 13) < (2829 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (5 : Fin 13) < (14143 / 10000 : ℝ) := by
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
      change values6 (5 : Fin 8) < (200024449 / 100000000 : ℝ)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (200024449 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (2829 / 1000 : ℝ) < values12 (127 : Fin 154) := by
    rw [show values12 (127 : Fin 154) = 1 + values10 (30 : Fin 54) by a158415_twelve_table]
    change (2829 / 1000 : ℝ) < 1 + values10 (30 : Fin 54)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1847 / 1000 : ℝ) < values10 (30 : Fin 54) := by
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by a158415_twelve_table]
      change (1847 / 1000 : ℝ) < Real.sqrt (values9 (30 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3411409 / 1000000 : ℝ) < values9 (30 : Fin 33)
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change (3411409 / 1000000 : ℝ) < 1 + values7 (10 : Fin 13)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (1207 / 500 : ℝ) < values7 (10 : Fin 13) := by
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change (1207 / 500 : ℝ) < 1 + values5 (2 : Fin 5)
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (7071 / 5000 : ℝ) < values5 (2 : Fin 5) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (7071 / 5000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_127 :
    values12 (127 : Fin 154) < values12 (128 : Fin 154) := by
  have hleft : values12 (127 : Fin 154) < (356 / 125 : ℝ) := by
    rw [show values12 (127 : Fin 154) = 1 + values10 (30 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (30 : Fin 54) < (356 / 125 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values10 (30 : Fin 54) < (9239 / 5000 : ℝ) := by
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (30 : Fin 33)) < (9239 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9239 / 5000 : ℝ))]
      norm_num
      change values9 (30 : Fin 33) < (85359121 / 25000000 : ℝ)
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (10 : Fin 13) < (85359121 / 25000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (10 : Fin 13) < (120711 / 50000 : ℝ) := by
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (120711 / 50000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values5 (2 : Fin 5) < (707107 / 500000 : ℝ) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (707107 / 500000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (356 / 125 : ℝ) < values12 (128 : Fin 154) := by
    rw [show values12 (128 : Fin 154) = values5 (1 : Fin 5) + values6 (4 : Fin 8) by a158415_twelve_table]
    change (356 / 125 : ℝ) < values5 (1 : Fin 5) + values6 (4 : Fin 8)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (433 / 250 : ℝ) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + 2
      have h9 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_128 :
    values12 (128 : Fin 154) < values12 (129 : Fin 154) := by
  have hleft : values12 (128 : Fin 154) < (1461 / 500 : ℝ) := by
    rw [show values12 (128 : Fin 154) = values5 (1 : Fin 5) + values6 (4 : Fin 8) by a158415_twelve_table]
    change values5 (1 : Fin 5) + values6 (4 : Fin 8) < (1461 / 500 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
    have h2 : values6 (4 : Fin 8) < (17321 / 10000 : ℝ) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17321 / 10000 : ℝ))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : ℝ)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (1461 / 500 : ℝ) < values12 (129 : Fin 154) := by
    rw [show values12 (129 : Fin 154) = Real.sqrt 2 + values7 (6 : Fin 13) by a158415_twelve_table]
    change (1461 / 500 : ℝ) < Real.sqrt 2 + values7 (6 : Fin 13)
    have h5 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (1553 / 1000 : ℝ) < values7 (6 : Fin 13) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (1553 / 1000 : ℝ) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : ℝ) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (2411809 / 1000000 : ℝ) < 1 + Real.sqrt 2
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_129 :
    values12 (129 : Fin 154) < values12 (130 : Fin 154) := by
  have hleft : values12 (129 : Fin 154) < (371 / 125 : ℝ) := by
    rw [show values12 (129 : Fin 154) = Real.sqrt 2 + values7 (6 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (6 : Fin 13) < (371 / 125 : ℝ)
    have h1 : Real.sqrt 2 < (707107 / 500000 : ℝ) := by
      change Real.sqrt (2) < (707107 / 500000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
      norm_num
    have h2 : values7 (6 : Fin 13) < (776887 / 500000 : ℝ) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (776887 / 500000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (776887 / 500000 : ℝ))]
      norm_num
      change values6 (6 : Fin 8) < (603553410769 / 250000000000 : ℝ)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (603553410769 / 250000000000 : ℝ)
      have h3 : 1 < (100000001 / 100000000 : ℝ) := by
        norm_num
      have h4 : Real.sqrt 2 < (141421357 / 100000000 : ℝ) := by
        change Real.sqrt (2) < (141421357 / 100000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141421357 / 100000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (371 / 125 : ℝ) < values12 (130 : Fin 154) := by
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by a158415_twelve_table]
    change (371 / 125 : ℝ) < 1 + values10 (31 : Fin 54)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1999 / 1000 : ℝ) < values10 (31 : Fin 54) := by
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by a158415_twelve_table]
      change (1999 / 1000 : ℝ) < Real.sqrt (values9 (31 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3996001 / 1000000 : ℝ) < values9 (31 : Fin 33)
      rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
      change (3996001 / 1000000 : ℝ) < 1 + values7 (11 : Fin 13)
      have h7 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h8 : (2999 / 1000 : ℝ) < values7 (11 : Fin 13) := by
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (2999 / 1000 : ℝ) < 1 + values5 (3 : Fin 5)
        have h9 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h10 : (19999 / 10000 : ℝ) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (19999 / 10000 : ℝ) < 1 + 1
          have h11 : (99999 / 100000 : ℝ) < 1 := by
            norm_num
          have h12 : (99999 / 100000 : ℝ) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_133 :
    values12 (133 : Fin 154) < values12 (134 : Fin 154) := by
  have hleft : values12 (133 : Fin 154) < (3091 / 1000 : ℝ) := by
    rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (34 : Fin 54) < (3091 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (34 : Fin 54) < (10453 / 5000 : ℝ) := by
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (3 : Fin 20) < (10453 / 5000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (3 : Fin 20) < (109051 / 100000 : ℝ) := by
        rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (3 : Fin 13)) < (109051 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109051 / 100000 : ℝ))]
        norm_num
        change values7 (3 : Fin 13) < (11892120601 / 10000000000 : ℝ)
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (3 : Fin 8)) < (11892120601 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11892120601 / 10000000000 : ℝ))]
        norm_num
        change values6 (3 : Fin 8) < (141422532388728601201 / 100000000000000000000 : ℝ)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (3 : Fin 5)) < (141422532388728601201 / 100000000000000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141422532388728601201 / 100000000000000000000 : ℝ))]
        norm_num
        change values5 (3 : Fin 5) < (20000332667240990236437247255686098642401 / 10000000000000000000000000000000000000000 : ℝ)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (20000332667240990236437247255686098642401 / 10000000000000000000000000000000000000000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (3091 / 1000 : ℝ) < values12 (134 : Fin 154) := by
    rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by a158415_twelve_table]
    change (3091 / 1000 : ℝ) < Real.sqrt 2 + values7 (7 : Fin 13)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (433 / 250 : ℝ) < values7 (7 : Fin 13) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + 2
      have h9 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values12_special_134 :
    values12 (134 : Fin 154) < values12 (135 : Fin 154) := by
  have hleft : values12 (134 : Fin 154) < (3147 / 1000 : ℝ) := by
    rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by a158415_twelve_table]
    change Real.sqrt 2 + values7 (7 : Fin 13) < (3147 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values7 (7 : Fin 13) < (17321 / 10000 : ℝ) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (17321 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17321 / 10000 : ℝ))]
      norm_num
      change values6 (7 : Fin 8) < (300017041 / 100000000 : ℝ)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (3147 / 1000 : ℝ) < values12 (135 : Fin 154) := by
    rw [show values12 (135 : Fin 154) = 1 + values10 (35 : Fin 54) by a158415_twelve_table]
    change (3147 / 1000 : ℝ) < 1 + values10 (35 : Fin 54)
    have h5 : (99999 / 100000 : ℝ) < 1 := by
      norm_num
    have h6 : (1342 / 625 : ℝ) < values10 (35 : Fin 54) := by
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by a158415_twelve_table]
      change (1342 / 625 : ℝ) < 1 + values8 (4 : Fin 20)
      have h7 : (9999999 / 10000000 : ℝ) < 1 := by
        norm_num
      have h8 : (573601 / 500000 : ℝ) < values8 (4 : Fin 20) := by
        rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
        change (573601 / 500000 : ℝ) < Real.sqrt (values7 (4 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (329018107201 / 250000000000 : ℝ) < values7 (4 : Fin 13)
        rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
        change (329018107201 / 250000000000 : ℝ) < Real.sqrt (values6 (4 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108252914866128728054401 / 62500000000000000000000 : ℝ) < values6 (4 : Fin 8)
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (108252914866128728054401 / 62500000000000000000000 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : ℝ) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : ℝ) < 1 + 2
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (1999999 / 1000000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option maxHeartbeats 2000000 in
theorem values12_strictMono : StrictMono values12 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact sqrt_values11_strictMono (by decide)
  · exact values12_special_86
  · change 1 + values10 (1 : Fin 54) < 1 + values10 (2 : Fin 54)
    linarith [values10_strictMono (by native_decide : (1 : Fin 54) < 2)]
  · change 1 + values10 (2 : Fin 54) < 1 + values10 (3 : Fin 54)
    linarith [values10_strictMono (by native_decide : (2 : Fin 54) < 3)]
  · change 1 + values10 (3 : Fin 54) < 1 + values10 (4 : Fin 54)
    linarith [values10_strictMono (by native_decide : (3 : Fin 54) < 4)]
  · change 1 + values10 (4 : Fin 54) < 1 + values10 (5 : Fin 54)
    linarith [values10_strictMono (by native_decide : (4 : Fin 54) < 5)]
  · exact values12_special_91
  · exact values12_special_92
  · change 1 + values10 (6 : Fin 54) < 1 + values10 (7 : Fin 54)
    linarith [values10_strictMono (by native_decide : (6 : Fin 54) < 7)]
  · change 1 + values10 (7 : Fin 54) < 1 + values10 (8 : Fin 54)
    linarith [values10_strictMono (by native_decide : (7 : Fin 54) < 8)]
  · exact values12_special_95
  · exact values12_special_96
  · change 1 + values10 (9 : Fin 54) < 1 + values10 (10 : Fin 54)
    linarith [values10_strictMono (by native_decide : (9 : Fin 54) < 10)]
  · change 1 + values10 (10 : Fin 54) < 1 + values10 (11 : Fin 54)
    linarith [values10_strictMono (by native_decide : (10 : Fin 54) < 11)]
  · change 1 + values10 (11 : Fin 54) < 1 + values10 (12 : Fin 54)
    linarith [values10_strictMono (by native_decide : (11 : Fin 54) < 12)]
  · change 1 + values10 (12 : Fin 54) < 1 + values10 (13 : Fin 54)
    linarith [values10_strictMono (by native_decide : (12 : Fin 54) < 13)]
  · change 1 + values10 (13 : Fin 54) < 1 + values10 (14 : Fin 54)
    linarith [values10_strictMono (by native_decide : (13 : Fin 54) < 14)]
  · exact values12_special_102
  · exact values12_special_103
  · exact values12_special_104
  · exact values12_special_105
  · change 1 + values10 (16 : Fin 54) < 1 + values10 (17 : Fin 54)
    linarith [values10_strictMono (by native_decide : (16 : Fin 54) < 17)]
  · change 1 + values10 (17 : Fin 54) < 1 + values10 (18 : Fin 54)
    linarith [values10_strictMono (by native_decide : (17 : Fin 54) < 18)]
  · exact values12_special_108
  · exact values12_special_109
  · change 1 + values10 (19 : Fin 54) < 1 + values10 (20 : Fin 54)
    linarith [values10_strictMono (by native_decide : (19 : Fin 54) < 20)]
  · change 1 + values10 (20 : Fin 54) < 1 + values10 (21 : Fin 54)
    linarith [values10_strictMono (by native_decide : (20 : Fin 54) < 21)]
  · exact values12_special_112
  · exact values12_special_113
  · exact values12_special_114
  · exact values12_special_115
  · exact values12_special_116
  · change 1 + values10 (23 : Fin 54) < 1 + values10 (24 : Fin 54)
    linarith [values10_strictMono (by native_decide : (23 : Fin 54) < 24)]
  · change 1 + values10 (24 : Fin 54) < 1 + values10 (25 : Fin 54)
    linarith [values10_strictMono (by native_decide : (24 : Fin 54) < 25)]
  · exact values12_special_119
  · exact values12_special_120
  · change 1 + values10 (26 : Fin 54) < 1 + values10 (27 : Fin 54)
    linarith [values10_strictMono (by native_decide : (26 : Fin 54) < 27)]
  · exact values12_special_122
  · exact values12_special_123
  · change 1 + values10 (28 : Fin 54) < 1 + values10 (29 : Fin 54)
    linarith [values10_strictMono (by native_decide : (28 : Fin 54) < 29)]
  · exact values12_special_125
  · exact values12_special_126
  · exact values12_special_127
  · exact values12_special_128
  · exact values12_special_129
  · change 1 + values10 (31 : Fin 54) < 1 + values10 (32 : Fin 54)
    linarith [values10_strictMono (by native_decide : (31 : Fin 54) < 32)]
  · change 1 + values10 (32 : Fin 54) < 1 + values10 (33 : Fin 54)
    linarith [values10_strictMono (by native_decide : (32 : Fin 54) < 33)]
  · change 1 + values10 (33 : Fin 54) < 1 + values10 (34 : Fin 54)
    linarith [values10_strictMono (by native_decide : (33 : Fin 54) < 34)]
  · exact values12_special_133
  · exact values12_special_134
  · change 1 + values10 (35 : Fin 54) < 1 + values10 (36 : Fin 54)
    linarith [values10_strictMono (by native_decide : (35 : Fin 54) < 36)]
  · change 1 + values10 (36 : Fin 54) < 1 + values10 (37 : Fin 54)
    linarith [values10_strictMono (by native_decide : (36 : Fin 54) < 37)]
  · change 1 + values10 (37 : Fin 54) < 1 + values10 (38 : Fin 54)
    linarith [values10_strictMono (by native_decide : (37 : Fin 54) < 38)]
  · change 1 + values10 (38 : Fin 54) < 1 + values10 (39 : Fin 54)
    linarith [values10_strictMono (by native_decide : (38 : Fin 54) < 39)]
  · change 1 + values10 (39 : Fin 54) < 1 + values10 (40 : Fin 54)
    linarith [values10_strictMono (by native_decide : (39 : Fin 54) < 40)]
  · change 1 + values10 (40 : Fin 54) < 1 + values10 (41 : Fin 54)
    linarith [values10_strictMono (by native_decide : (40 : Fin 54) < 41)]
  · change 1 + values10 (41 : Fin 54) < 1 + values10 (42 : Fin 54)
    linarith [values10_strictMono (by native_decide : (41 : Fin 54) < 42)]
  · change 1 + values10 (42 : Fin 54) < 1 + values10 (43 : Fin 54)
    linarith [values10_strictMono (by native_decide : (42 : Fin 54) < 43)]
  · change 1 + values10 (43 : Fin 54) < 1 + values10 (44 : Fin 54)
    linarith [values10_strictMono (by native_decide : (43 : Fin 54) < 44)]
  · change 1 + values10 (44 : Fin 54) < 1 + values10 (45 : Fin 54)
    linarith [values10_strictMono (by native_decide : (44 : Fin 54) < 45)]
  · change 1 + values10 (45 : Fin 54) < 1 + values10 (46 : Fin 54)
    linarith [values10_strictMono (by native_decide : (45 : Fin 54) < 46)]
  · change 1 + values10 (46 : Fin 54) < 1 + values10 (47 : Fin 54)
    linarith [values10_strictMono (by native_decide : (46 : Fin 54) < 47)]
  · change 1 + values10 (47 : Fin 54) < 1 + values10 (48 : Fin 54)
    linarith [values10_strictMono (by native_decide : (47 : Fin 54) < 48)]
  · change 1 + values10 (48 : Fin 54) < 1 + values10 (49 : Fin 54)
    linarith [values10_strictMono (by native_decide : (48 : Fin 54) < 49)]
  · change 1 + values10 (49 : Fin 54) < 1 + values10 (50 : Fin 54)
    linarith [values10_strictMono (by native_decide : (49 : Fin 54) < 50)]
  · change 1 + values10 (50 : Fin 54) < 1 + values10 (51 : Fin 54)
    linarith [values10_strictMono (by native_decide : (50 : Fin 54) < 51)]
  · change 1 + values10 (51 : Fin 54) < 1 + values10 (52 : Fin 54)
    linarith [values10_strictMono (by native_decide : (51 : Fin 54) < 52)]
  · change 1 + values10 (52 : Fin 54) < 1 + values10 (53 : Fin 54)
    linarith [values10_strictMono (by native_decide : (52 : Fin 54) < 53)]

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_values11_mem_range_values12 (i : Fin 91) :
    Real.sqrt (values11 i) ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(0 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(1 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(2 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(3 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(4 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(5 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(6 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(7 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(8 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(9 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(10 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(11 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(12 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(13 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(14 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(15 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(16 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(17 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(18 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(19 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(20 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(21 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(22 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(23 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(24 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(25 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(26 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(27 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(28 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(29 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(30 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(31 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(32 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(33 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(34 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(35 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(36 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(37 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(38 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(39 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(40 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(41 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(42 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(43 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(44 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(45 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(46 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(47 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(48 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(49 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(50 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(51 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(52 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(53 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(54 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(55 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(56 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(57 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(58 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(59 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(60 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(61 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(62 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(63 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(64 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(65 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(66 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(67 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(68 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(69 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(70 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(71 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(72 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(73 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(74 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(75 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(76 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(77 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(78 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(79 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(80 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(81 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(82 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(83 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(84 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(85 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(86 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(92 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(96 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(103 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(113 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values10_mem_range_values12 (i : Fin 54) :
    1 + values10 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(86 : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩
  · exact ⟨(87 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(88 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(89 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(90 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(91 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(93 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(94 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(95 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(97 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(98 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(99 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(101 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(102 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(104 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(106 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(107 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(108 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(111 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(112 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(115 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(117 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(118 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(119 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(121 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(122 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(124 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(125 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(127 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(131 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(132 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(135 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(137 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(138 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(139 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(141 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(142 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(143 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(145 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(147 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(150 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(152 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(153 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values9_mem_range_values12 (i : Fin 33) :
    1 + values9 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(86 : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩
  · exact ⟨(88 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(89 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(91 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(94 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(95 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(98 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(99 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(102 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(104 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(107 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(112 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(115 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(118 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(121 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(124 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(127 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(132 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(139 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(142 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(145 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(153 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values8_mem_range_values12 (i : Fin 20) :
    1 + values8 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(86 : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩
  · exact ⟨(89 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(91 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(95 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(99 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(104 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(107 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(115 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(118 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(124 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values8_mem_range_values12 (i : Fin 20) :
    2 + values8 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(131 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(132 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(135 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(138 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(139 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(141 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(142 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(147 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(150 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(152 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(153 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values7_mem_range_values12 (i : Fin 13) :
    1 + values7 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(86 : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩
  · exact ⟨(91 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(95 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(107 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(118 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(124 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_two_add_values7_mem_range_values12 (i : Fin 13) :
    Real.sqrt 2 + values7 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(114 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(116 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(120 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(123 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(126 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(129 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(134 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(143 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(145 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(152 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values7_mem_range_values12 (i : Fin 13) :
    2 + values7 i ∈ Set.range values12 := by
  fin_cases i
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(132 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(139 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(142 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(153 : Fin 154), by a158415_twelve_table⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values5_add_values6_mem_range_values12 (i : Fin 5) (j : Fin 8) :
    values5 i + values6 j ∈ Set.range values12 := by
  fin_cases i <;> fin_cases j
  · exact ⟨(86 : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩
  · exact ⟨(95 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(124 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(100 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(105 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(109 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(120 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(128 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(143 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(110 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(116 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(120 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(126 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(134 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(145 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(130 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(133 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(136 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(140 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(144 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(146 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(147 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(148 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(149 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(150 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(151 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(152 : Fin 154), by a158415_twelve_table⟩
  · exact ⟨(153 : Fin 154), by a158415_twelve_table⟩

@[simp] theorem sqrt_values11_mem_recursiveValueSet_twelve (i : Fin 91) :
    Real.sqrt (values11 i) ∈ recursiveValueSet 12 := by
  rw [recursiveValueSet]
  exact Or.inl ⟨values11 i, values11_mem_recursiveValueSet i, rfl⟩

@[simp] theorem one_add_values10_mem_recursiveValueSet_twelve (i : Fin 54) :
    1 + values10 i ∈ recursiveValueSet 12 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨0, by decide⟩, 1, ?_, values10 i, ?_, rfl⟩
  · simp [recursiveValueSet]
  · change values10 i ∈ recursiveValueSet 10
    rw [recursiveValueSet_ten]
    exact ⟨i, rfl⟩

@[simp] theorem values5_add_values6_mem_recursiveValueSet_twelve
    (i : Fin 5) (j : Fin 8) :
    values5 i + values6 j ∈ recursiveValueSet 12 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨4, by decide⟩, values5 i, ?_, values6 j, ?_, rfl⟩
  · change values5 i ∈ recursiveValueSet 5
    rw [recursiveValueSet_five_eq_range_values5]
    exact ⟨i, rfl⟩
  · change values6 j ∈ recursiveValueSet 6
    rw [recursiveValueSet_six_eq_range_values6]
    exact ⟨j, rfl⟩

@[simp] theorem sqrt_two_add_values7_mem_recursiveValueSet_twelve (i : Fin 13) :
    Real.sqrt 2 + values7 i ∈ recursiveValueSet 12 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, values7 i, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change values7 i ∈ recursiveValueSet 7
    rw [recursiveValueSet_seven]
    exact ⟨i, rfl⟩

set_option maxHeartbeats 1000000 in
theorem values12_mem_recursiveValueSet (i : Fin 154) :
    values12 i ∈ recursiveValueSet 12 := by
  fin_cases i
  · exact sqrt_values11_mem_recursiveValueSet_twelve (0 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (1 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (2 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (3 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (4 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (5 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (6 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (7 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (8 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (9 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (10 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (11 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (12 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (13 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (14 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (15 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (16 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (17 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (18 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (19 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (20 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (21 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (22 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (23 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (24 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (25 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (26 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (27 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (28 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (29 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (30 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (31 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (32 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (33 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (34 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (35 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (36 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (37 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (38 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (39 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (40 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (41 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (42 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (43 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (44 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (45 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (46 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (47 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (48 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (49 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (50 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (51 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (52 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (53 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (54 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (55 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (56 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (57 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (58 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (59 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (60 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (61 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (62 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (63 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (64 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (65 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (66 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (67 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (68 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (69 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (70 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (71 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (72 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (73 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (74 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (75 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (76 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (77 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (78 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (79 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (80 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (81 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (82 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (83 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (84 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (85 : Fin 91)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (86 : Fin 91)
  · exact one_add_values10_mem_recursiveValueSet_twelve (1 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (2 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (3 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (4 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (5 : Fin 54)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (87 : Fin 91)
  · exact one_add_values10_mem_recursiveValueSet_twelve (6 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (7 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (8 : Fin 54)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (88 : Fin 91)
  · exact one_add_values10_mem_recursiveValueSet_twelve (9 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (10 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (11 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (12 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (13 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (14 : Fin 54)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (89 : Fin 91)
  · exact one_add_values10_mem_recursiveValueSet_twelve (15 : Fin 54)
  · exact values5_add_values6_mem_recursiveValueSet_twelve (1 : Fin 5) (1 : Fin 8)
  · exact one_add_values10_mem_recursiveValueSet_twelve (16 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (17 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (18 : Fin 54)
  · exact values5_add_values6_mem_recursiveValueSet_twelve (1 : Fin 5) (2 : Fin 8)
  · exact one_add_values10_mem_recursiveValueSet_twelve (19 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (20 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (21 : Fin 54)
  · exact sqrt_values11_mem_recursiveValueSet_twelve (90 : Fin 91)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (1 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (22 : Fin 54)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (2 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (23 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (24 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (25 : Fin 54)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (3 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (26 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (27 : Fin 54)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (4 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (28 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (29 : Fin 54)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (5 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (30 : Fin 54)
  · exact values5_add_values6_mem_recursiveValueSet_twelve (1 : Fin 5) (4 : Fin 8)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (6 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (31 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (32 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (33 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (34 : Fin 54)
  · exact sqrt_two_add_values7_mem_recursiveValueSet_twelve (7 : Fin 13)
  · exact one_add_values10_mem_recursiveValueSet_twelve (35 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (36 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (37 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (38 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (39 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (40 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (41 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (42 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (43 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (44 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (45 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (46 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (47 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (48 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (49 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (50 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (51 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (52 : Fin 54)
  · exact one_add_values10_mem_recursiveValueSet_twelve (53 : Fin 54)

theorem values12_range_subset_recursiveValueSet_twelve :
    Set.range values12 ⊆ recursiveValueSet 12 := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact values12_mem_recursiveValueSet i

theorem values12_range_ncard :
    (Set.range values12).ncard = 154 := by
  rw [Set.ncard_range_of_injective values12_strictMono.injective]
  norm_num

theorem recursiveValueSet_twelve_unary_subset_range :
    ((fun x : ℝ => Real.sqrt x) '' recursiveValueSet 11) ⊆ Set.range values12 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_eleven] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values11_mem_range_values12 i

set_option maxHeartbeats 2000000 in
theorem recursiveValueSet_twelve_subset_range :
    recursiveValueSet 12 ⊆ Set.range values12 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with hsqrt | hadd
  · exact recursiveValueSet_twelve_unary_subset_range hsqrt
  · rcases hadd with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 10 := by simpa using hb
      rw [recursiveValueSet_ten] at hb'
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values10_mem_range_values12 i
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rw [recursiveValueSet_nine] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values9_mem_range_values12 i
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl
      · exact one_add_values8_mem_range_values12 i
      · exact two_add_values8_mem_range_values12 i
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_values7_mem_range_values12 i
      · exact sqrt_two_add_values7_mem_range_values12 i
      · exact two_add_values7_mem_range_values12 i
    · rw [recursiveValueSet_five_eq_range_values5] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six_eq_range_values6] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values5_add_values6_mem_range_values12 i j
    · rw [recursiveValueSet_six_eq_range_values6] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five_eq_range_values5] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      simpa [add_comm] using values5_add_values6_mem_range_values12 j i
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl | rfl
      · simpa [add_comm] using one_add_values7_mem_range_values12 i
      · simpa [add_comm] using sqrt_two_add_values7_mem_range_values12 i
      · simpa [add_comm] using two_add_values7_mem_range_values12 i
    · rw [recursiveValueSet_eight] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · simpa [add_comm] using one_add_values8_mem_range_values12 i
      · simpa [add_comm] using two_add_values8_mem_range_values12 i
    · rw [recursiveValueSet_nine] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      simpa [add_comm] using one_add_values9_mem_range_values12 i
    · rw [recursiveValueSet_ten] at ha
      simp [recursiveValueSet] at hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with rfl
      simpa [add_comm] using one_add_values10_mem_range_values12 i

theorem recursiveValueSet_twelve :
    recursiveValueSet 12 = Set.range values12 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_twelve_subset_range
  · exact values12_range_subset_recursiveValueSet_twelve

theorem recursiveValueSet_twelve_ncard :
    (recursiveValueSet 12).ncard = 154 := by
  rw [recursiveValueSet_twelve, values12_range_ncard]

theorem a158415_twelve : a158415 12 = 154 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_twelve_ncard

end Expr

export Expr (a158415_twelve)

end A158415

end LeanProofs
