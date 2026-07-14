import A158415.Certificates.N12.Twelve

/-!
# Size-thirteen certificate for OEIS A158415

This module records the 264 exact representatives discovered for size 13 and
proves that this table is exactly the split-recursive value set, yielding
`a158415 13 = 264`.
-/

namespace LeanProofs

namespace A158415

namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable def values13Nat : Nat -> Real
  | 0 => Real.sqrt (values12 (0 : Fin 154))
  | 1 => Real.sqrt (values12 (1 : Fin 154))
  | 2 => Real.sqrt (values12 (2 : Fin 154))
  | 3 => Real.sqrt (values12 (3 : Fin 154))
  | 4 => Real.sqrt (values12 (4 : Fin 154))
  | 5 => Real.sqrt (values12 (5 : Fin 154))
  | 6 => Real.sqrt (values12 (6 : Fin 154))
  | 7 => Real.sqrt (values12 (7 : Fin 154))
  | 8 => Real.sqrt (values12 (8 : Fin 154))
  | 9 => Real.sqrt (values12 (9 : Fin 154))
  | 10 => Real.sqrt (values12 (10 : Fin 154))
  | 11 => Real.sqrt (values12 (11 : Fin 154))
  | 12 => Real.sqrt (values12 (12 : Fin 154))
  | 13 => Real.sqrt (values12 (13 : Fin 154))
  | 14 => Real.sqrt (values12 (14 : Fin 154))
  | 15 => Real.sqrt (values12 (15 : Fin 154))
  | 16 => Real.sqrt (values12 (16 : Fin 154))
  | 17 => Real.sqrt (values12 (17 : Fin 154))
  | 18 => Real.sqrt (values12 (18 : Fin 154))
  | 19 => Real.sqrt (values12 (19 : Fin 154))
  | 20 => Real.sqrt (values12 (20 : Fin 154))
  | 21 => Real.sqrt (values12 (21 : Fin 154))
  | 22 => Real.sqrt (values12 (22 : Fin 154))
  | 23 => Real.sqrt (values12 (23 : Fin 154))
  | 24 => Real.sqrt (values12 (24 : Fin 154))
  | 25 => Real.sqrt (values12 (25 : Fin 154))
  | 26 => Real.sqrt (values12 (26 : Fin 154))
  | 27 => Real.sqrt (values12 (27 : Fin 154))
  | 28 => Real.sqrt (values12 (28 : Fin 154))
  | 29 => Real.sqrt (values12 (29 : Fin 154))
  | 30 => Real.sqrt (values12 (30 : Fin 154))
  | 31 => Real.sqrt (values12 (31 : Fin 154))
  | 32 => Real.sqrt (values12 (32 : Fin 154))
  | 33 => Real.sqrt (values12 (33 : Fin 154))
  | 34 => Real.sqrt (values12 (34 : Fin 154))
  | 35 => Real.sqrt (values12 (35 : Fin 154))
  | 36 => Real.sqrt (values12 (36 : Fin 154))
  | 37 => Real.sqrt (values12 (37 : Fin 154))
  | 38 => Real.sqrt (values12 (38 : Fin 154))
  | 39 => Real.sqrt (values12 (39 : Fin 154))
  | 40 => Real.sqrt (values12 (40 : Fin 154))
  | 41 => Real.sqrt (values12 (41 : Fin 154))
  | 42 => Real.sqrt (values12 (42 : Fin 154))
  | 43 => Real.sqrt (values12 (43 : Fin 154))
  | 44 => Real.sqrt (values12 (44 : Fin 154))
  | 45 => Real.sqrt (values12 (45 : Fin 154))
  | 46 => Real.sqrt (values12 (46 : Fin 154))
  | 47 => Real.sqrt (values12 (47 : Fin 154))
  | 48 => Real.sqrt (values12 (48 : Fin 154))
  | 49 => Real.sqrt (values12 (49 : Fin 154))
  | 50 => Real.sqrt (values12 (50 : Fin 154))
  | 51 => Real.sqrt (values12 (51 : Fin 154))
  | 52 => Real.sqrt (values12 (52 : Fin 154))
  | 53 => Real.sqrt (values12 (53 : Fin 154))
  | 54 => Real.sqrt (values12 (54 : Fin 154))
  | 55 => Real.sqrt (values12 (55 : Fin 154))
  | 56 => Real.sqrt (values12 (56 : Fin 154))
  | 57 => Real.sqrt (values12 (57 : Fin 154))
  | 58 => Real.sqrt (values12 (58 : Fin 154))
  | 59 => Real.sqrt (values12 (59 : Fin 154))
  | 60 => Real.sqrt (values12 (60 : Fin 154))
  | 61 => Real.sqrt (values12 (61 : Fin 154))
  | 62 => Real.sqrt (values12 (62 : Fin 154))
  | 63 => Real.sqrt (values12 (63 : Fin 154))
  | 64 => Real.sqrt (values12 (64 : Fin 154))
  | 65 => Real.sqrt (values12 (65 : Fin 154))
  | 66 => Real.sqrt (values12 (66 : Fin 154))
  | 67 => Real.sqrt (values12 (67 : Fin 154))
  | 68 => Real.sqrt (values12 (68 : Fin 154))
  | 69 => Real.sqrt (values12 (69 : Fin 154))
  | 70 => Real.sqrt (values12 (70 : Fin 154))
  | 71 => Real.sqrt (values12 (71 : Fin 154))
  | 72 => Real.sqrt (values12 (72 : Fin 154))
  | 73 => Real.sqrt (values12 (73 : Fin 154))
  | 74 => Real.sqrt (values12 (74 : Fin 154))
  | 75 => Real.sqrt (values12 (75 : Fin 154))
  | 76 => Real.sqrt (values12 (76 : Fin 154))
  | 77 => Real.sqrt (values12 (77 : Fin 154))
  | 78 => Real.sqrt (values12 (78 : Fin 154))
  | 79 => Real.sqrt (values12 (79 : Fin 154))
  | 80 => Real.sqrt (values12 (80 : Fin 154))
  | 81 => Real.sqrt (values12 (81 : Fin 154))
  | 82 => Real.sqrt (values12 (82 : Fin 154))
  | 83 => Real.sqrt (values12 (83 : Fin 154))
  | 84 => Real.sqrt (values12 (84 : Fin 154))
  | 85 => Real.sqrt (values12 (85 : Fin 154))
  | 86 => Real.sqrt (values12 (86 : Fin 154))
  | 87 => Real.sqrt (values12 (87 : Fin 154))
  | 88 => Real.sqrt (values12 (88 : Fin 154))
  | 89 => Real.sqrt (values12 (89 : Fin 154))
  | 90 => Real.sqrt (values12 (90 : Fin 154))
  | 91 => Real.sqrt (values12 (91 : Fin 154))
  | 92 => Real.sqrt (values12 (92 : Fin 154))
  | 93 => Real.sqrt (values12 (93 : Fin 154))
  | 94 => Real.sqrt (values12 (94 : Fin 154))
  | 95 => Real.sqrt (values12 (95 : Fin 154))
  | 96 => Real.sqrt (values12 (96 : Fin 154))
  | 97 => Real.sqrt (values12 (97 : Fin 154))
  | 98 => Real.sqrt (values12 (98 : Fin 154))
  | 99 => Real.sqrt (values12 (99 : Fin 154))
  | 100 => Real.sqrt (values12 (100 : Fin 154))
  | 101 => Real.sqrt (values12 (101 : Fin 154))
  | 102 => Real.sqrt (values12 (102 : Fin 154))
  | 103 => Real.sqrt (values12 (103 : Fin 154))
  | 104 => Real.sqrt (values12 (104 : Fin 154))
  | 105 => Real.sqrt (values12 (105 : Fin 154))
  | 106 => Real.sqrt (values12 (106 : Fin 154))
  | 107 => Real.sqrt (values12 (107 : Fin 154))
  | 108 => Real.sqrt (values12 (108 : Fin 154))
  | 109 => Real.sqrt (values12 (109 : Fin 154))
  | 110 => Real.sqrt (values12 (110 : Fin 154))
  | 111 => Real.sqrt (values12 (111 : Fin 154))
  | 112 => Real.sqrt (values12 (112 : Fin 154))
  | 113 => Real.sqrt (values12 (113 : Fin 154))
  | 114 => Real.sqrt (values12 (114 : Fin 154))
  | 115 => Real.sqrt (values12 (115 : Fin 154))
  | 116 => Real.sqrt (values12 (116 : Fin 154))
  | 117 => Real.sqrt (values12 (117 : Fin 154))
  | 118 => Real.sqrt (values12 (118 : Fin 154))
  | 119 => Real.sqrt (values12 (119 : Fin 154))
  | 120 => Real.sqrt (values12 (120 : Fin 154))
  | 121 => Real.sqrt (values12 (121 : Fin 154))
  | 122 => Real.sqrt (values12 (122 : Fin 154))
  | 123 => Real.sqrt (values12 (123 : Fin 154))
  | 124 => Real.sqrt (values12 (124 : Fin 154))
  | 125 => Real.sqrt (values12 (125 : Fin 154))
  | 126 => Real.sqrt (values12 (126 : Fin 154))
  | 127 => Real.sqrt (values12 (127 : Fin 154))
  | 128 => Real.sqrt (values12 (128 : Fin 154))
  | 129 => Real.sqrt (values12 (129 : Fin 154))
  | 130 => Real.sqrt (values12 (130 : Fin 154))
  | 131 => Real.sqrt (values12 (131 : Fin 154))
  | 132 => Real.sqrt (values12 (132 : Fin 154))
  | 133 => Real.sqrt (values12 (133 : Fin 154))
  | 134 => Real.sqrt (values12 (134 : Fin 154))
  | 135 => Real.sqrt (values12 (135 : Fin 154))
  | 136 => Real.sqrt (values12 (136 : Fin 154))
  | 137 => Real.sqrt (values12 (137 : Fin 154))
  | 138 => Real.sqrt (values12 (138 : Fin 154))
  | 139 => Real.sqrt (values12 (139 : Fin 154))
  | 140 => Real.sqrt (values12 (140 : Fin 154))
  | 141 => Real.sqrt (values12 (141 : Fin 154))
  | 142 => Real.sqrt (values12 (142 : Fin 154))
  | 143 => Real.sqrt (values12 (143 : Fin 154))
  | 144 => Real.sqrt (values12 (144 : Fin 154))
  | 145 => Real.sqrt (values12 (145 : Fin 154))
  | 146 => Real.sqrt (values12 (146 : Fin 154))
  | 147 => 1 + values11 (1 : Fin 91)
  | 148 => 1 + values11 (2 : Fin 91)
  | 149 => 1 + values11 (3 : Fin 91)
  | 150 => 1 + values11 (4 : Fin 91)
  | 151 => 1 + values11 (5 : Fin 91)
  | 152 => Real.sqrt (values12 (147 : Fin 154))
  | 153 => 1 + values11 (6 : Fin 91)
  | 154 => 1 + values11 (7 : Fin 91)
  | 155 => 1 + values11 (8 : Fin 91)
  | 156 => Real.sqrt (values12 (148 : Fin 154))
  | 157 => 1 + values11 (9 : Fin 91)
  | 158 => 1 + values11 (10 : Fin 91)
  | 159 => 1 + values11 (11 : Fin 91)
  | 160 => 1 + values11 (12 : Fin 91)
  | 161 => 1 + values11 (13 : Fin 91)
  | 162 => Real.sqrt (values12 (149 : Fin 154))
  | 163 => 1 + values11 (14 : Fin 91)
  | 164 => 1 + values11 (15 : Fin 91)
  | 165 => 1 + values11 (16 : Fin 91)
  | 166 => 1 + values11 (17 : Fin 91)
  | 167 => 1 + values11 (18 : Fin 91)
  | 168 => Real.sqrt (values12 (150 : Fin 154))
  | 169 => values6 (1 : Fin 8) + values6 (1 : Fin 8)
  | 170 => 1 + values11 (19 : Fin 91)
  | 171 => 1 + values11 (20 : Fin 91)
  | 172 => 1 + values11 (21 : Fin 91)
  | 173 => 1 + values11 (22 : Fin 91)
  | 174 => values5 (1 : Fin 5) + values7 (1 : Fin 13)
  | 175 => 1 + values11 (23 : Fin 91)
  | 176 => Real.sqrt (values12 (151 : Fin 154))
  | 177 => 1 + values11 (24 : Fin 91)
  | 178 => 1 + values11 (25 : Fin 91)
  | 179 => values5 (1 : Fin 5) + values7 (2 : Fin 13)
  | 180 => 1 + values11 (26 : Fin 91)
  | 181 => 1 + values11 (27 : Fin 91)
  | 182 => 1 + values11 (28 : Fin 91)
  | 183 => Real.sqrt (values12 (152 : Fin 154))
  | 184 => 1 + values11 (29 : Fin 91)
  | 185 => 1 + values11 (30 : Fin 91)
  | 186 => values5 (1 : Fin 5) + values7 (3 : Fin 13)
  | 187 => 1 + values11 (31 : Fin 91)
  | 188 => 1 + values11 (32 : Fin 91)
  | 189 => 1 + values11 (33 : Fin 91)
  | 190 => Real.sqrt 2 + values8 (1 : Fin 20)
  | 191 => 1 + values11 (34 : Fin 91)
  | 192 => Real.sqrt (values12 (153 : Fin 154))
  | 193 => Real.sqrt 2 + values8 (2 : Fin 20)
  | 194 => 1 + values11 (35 : Fin 91)
  | 195 => 1 + values11 (36 : Fin 91)
  | 196 => 1 + values11 (37 : Fin 91)
  | 197 => 1 + values11 (38 : Fin 91)
  | 198 => Real.sqrt 2 + values8 (3 : Fin 20)
  | 199 => values5 (1 : Fin 5) + values7 (4 : Fin 13)
  | 200 => 1 + values11 (39 : Fin 91)
  | 201 => 1 + values11 (40 : Fin 91)
  | 202 => Real.sqrt 2 + values8 (4 : Fin 20)
  | 203 => 1 + values11 (41 : Fin 91)
  | 204 => 1 + values11 (42 : Fin 91)
  | 205 => Real.sqrt 2 + values8 (5 : Fin 20)
  | 206 => 1 + values11 (43 : Fin 91)
  | 207 => 1 + values11 (44 : Fin 91)
  | 208 => Real.sqrt 2 + values8 (6 : Fin 20)
  | 209 => 1 + values11 (45 : Fin 91)
  | 210 => Real.sqrt 2 + values8 (7 : Fin 20)
  | 211 => 1 + values11 (46 : Fin 91)
  | 212 => values5 (1 : Fin 5) + values7 (6 : Fin 13)
  | 213 => 1 + values11 (47 : Fin 91)
  | 214 => 1 + values11 (48 : Fin 91)
  | 215 => values6 (1 : Fin 8) + values6 (4 : Fin 8)
  | 216 => Real.sqrt 2 + values8 (8 : Fin 20)
  | 217 => 1 + values11 (49 : Fin 91)
  | 218 => Real.sqrt 2 + values8 (9 : Fin 20)
  | 219 => values5 (1 : Fin 5) + values7 (7 : Fin 13)
  | 220 => 1 + values11 (50 : Fin 91)
  | 221 => Real.sqrt 2 + values8 (10 : Fin 20)
  | 222 => 1 + values11 (51 : Fin 91)
  | 223 => 1 + values11 (52 : Fin 91)
  | 224 => 1 + values11 (53 : Fin 91)
  | 225 => 1 + values11 (54 : Fin 91)
  | 226 => 1 + values11 (55 : Fin 91)
  | 227 => 1 + values11 (56 : Fin 91)
  | 228 => 1 + values11 (57 : Fin 91)
  | 229 => 1 + values11 (58 : Fin 91)
  | 230 => Real.sqrt 2 + values8 (11 : Fin 20)
  | 231 => 1 + values11 (59 : Fin 91)
  | 232 => 1 + values11 (60 : Fin 91)
  | 233 => 1 + values11 (61 : Fin 91)
  | 234 => 1 + values11 (62 : Fin 91)
  | 235 => 1 + values11 (63 : Fin 91)
  | 236 => 1 + values11 (64 : Fin 91)
  | 237 => 1 + values11 (65 : Fin 91)
  | 238 => 1 + values11 (66 : Fin 91)
  | 239 => 1 + values11 (67 : Fin 91)
  | 240 => values6 (4 : Fin 8) + values6 (4 : Fin 8)
  | 241 => 1 + values11 (68 : Fin 91)
  | 242 => 1 + values11 (69 : Fin 91)
  | 243 => 1 + values11 (70 : Fin 91)
  | 244 => 1 + values11 (71 : Fin 91)
  | 245 => 1 + values11 (72 : Fin 91)
  | 246 => 1 + values11 (73 : Fin 91)
  | 247 => 1 + values11 (74 : Fin 91)
  | 248 => 1 + values11 (75 : Fin 91)
  | 249 => 1 + values11 (76 : Fin 91)
  | 250 => 1 + values11 (77 : Fin 91)
  | 251 => 1 + values11 (78 : Fin 91)
  | 252 => 1 + values11 (79 : Fin 91)
  | 253 => 1 + values11 (80 : Fin 91)
  | 254 => 1 + values11 (81 : Fin 91)
  | 255 => 1 + values11 (82 : Fin 91)
  | 256 => 1 + values11 (83 : Fin 91)
  | 257 => 1 + values11 (84 : Fin 91)
  | 258 => 1 + values11 (85 : Fin 91)
  | 259 => 1 + values11 (86 : Fin 91)
  | 260 => 1 + values11 (87 : Fin 91)
  | 261 => 1 + values11 (88 : Fin 91)
  | 262 => 1 + values11 (89 : Fin 91)
  | 263 => 1 + values11 (90 : Fin 91)
  | _ => 0
noncomputable def values13 (i : Fin 264) : ℝ :=
  values13Nat i.1

set_option linter.unusedSimpArgs false in
macro "a158415_thirteen_table" : tactic =>
  `(tactic|
    (simp only [values13, values13Nat] <;> ring_nf))

theorem values12_nonneg (i : Fin 154) : (0 : ℝ) ≤ values12 i := by
  have h0 : (0 : ℝ) ≤ values12 (0 : Fin 154) := by
    norm_num [values12, values12Nat]
  exact h0.trans (values12_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values12_strictMono :
    StrictMono fun i : Fin 154 => Real.sqrt (values12 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values12_nonneg i) (values12_strictMono hij)


set_option linter.unusedTactic false in
theorem values13_special_146 :
    values13 (146 : Fin 264) < values13 (147 : Fin 264) := by
  have hleft : values13 (146 : Fin 264) < (2001 / 1000 : ℝ) := by
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    change Real.sqrt (values12 (146 : Fin 154)) < (2001 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2001 / 1000 : ℝ))]
    norm_num
    change values12 (146 : Fin 154) < (4004001 / 1000000 : ℝ)
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (46 : Fin 54) < (4004001 / 1000000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values10 (46 : Fin 54) < (3001 / 1000 : ℝ) := by
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (12 : Fin 20) < (3001 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values8 (12 : Fin 20) < (20001 / 10000 : ℝ) := by
        rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (12 : Fin 13)) < (20001 / 10000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (20001 / 10000 : ℝ))]
        norm_num
        change values7 (12 : Fin 13) < (400040001 / 100000000 : ℝ)
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (4 : Fin 5) < (400040001 / 100000000 : ℝ)
        have h5 : 1 < (10001 / 10000 : ℝ) := by
          norm_num
        have h6 : values5 (4 : Fin 5) < (30001 / 10000 : ℝ) := by
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (30001 / 10000 : ℝ)
          have h7 : 1 < (100001 / 100000 : ℝ) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2001 / 1000 : ℝ) < values13 (147 : Fin 264) := by
    rw [show values13 (147 : Fin 264) = 1 + values11 (1 : Fin 91) by rfl]
    change (2001 / 1000 : ℝ) < 1 + values11 (1 : Fin 91)
    have h9 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h10 : (10027 / 10000 : ℝ) < values11 (1 : Fin 91) := by
      rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by a158415_twelve_table]
      change (10027 / 10000 : ℝ) < Real.sqrt (values10 (1 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (100540729 / 100000000 : ℝ) < values10 (1 : Fin 54)
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by a158415_twelve_table]
      change (100540729 / 100000000 : ℝ) < Real.sqrt (values9 (1 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10108438187851441 / 10000000000000000 : ℝ) < values9 (1 : Fin 33)
      rw [show values9 (1 : Fin 33) = Real.sqrt (values8 (1 : Fin 20)) by a158415_twelve_table]
      change (10108438187851441 / 10000000000000000 : ℝ) < Real.sqrt (values8 (1 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (102180522597613324406479885776481 / 100000000000000000000000000000000 : ℝ) < values8 (1 : Fin 20)
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (102180522597613324406479885776481 / 100000000000000000000000000000000 : ℝ) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10440859198321367241160595330446975327436160406549040772292743361 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (10440859198321367241160595330446975327436160406549040772292743361 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (109011540799171903435718248805797475835034040652749777718534356679259042850384546737034995795629066854014941197928328059409576321 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109011540799171903435718248805797475835034040652749777718534356679259042850384546737034995795629066854014941197928328059409576321 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11883516027409520475193605857915260867543378181709887160621348102592916787747786347271400070954826673762697181148884981356291200657783076890451698103526051622770183614156796199141512544406996008211462869257472400954088412143053620884342337340334640723895041 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11883516027409520475193605857915260867543378181709887160621348102592916787747786347271400070954826673762697181148884981356291200657783076890451698103526051622770183614156796199141512544406996008211462869257472400954088412143053620884342337340334640723895041 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141217953173698950989863449300516971405505280988812781486483866406192391466892147694609757163537933553260199898997575549528146276697181611727998623909847369845580136126170310038895179311791384548386768152008580388259739634304955096845084834735936223185957786926338537253236939943286258365137331426818324982252909624423536862960417795292230978651776295410613891660452514216527482262068086671336164518624520231840111958722451123327880044790452905610744993040753076093354591201228425673932277964350877064510384391681 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt 2
      change (141217953173698950989863449300516971405505280988812781486483866406192391466892147694609757163537933553260199898997575549528146276697181611727998623909847369845580136126170310038895179311791384548386768152008580388259739634304955096845084834735936223185957786926338537253236939943286258365137331426818324982252909624423536862960417795292230978651776295410613891660452514216527482262068086671336164518624520231840111958722451123327880044790452905610744993040753076093354591201228425673932277964350877064510384391681 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_151 :
    values13 (151 : Fin 264) < values13 (152 : Fin 264) := by
  have hleft : values13 (151 : Fin 264) < (1011 / 500 : ℝ) := by
    rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
    change 1 + values11 (5 : Fin 91) < (1011 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (5 : Fin 91) < (10219 / 10000 : ℝ) := by
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (5 : Fin 54)) < (10219 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10219 / 10000 : ℝ))]
      norm_num
      change values10 (5 : Fin 54) < (104427961 / 100000000 : ℝ)
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (5 : Fin 33)) < (104427961 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (104427961 / 100000000 : ℝ))]
      norm_num
      change values9 (5 : Fin 33) < (10905199038617521 / 10000000000000000 : ℝ)
      rw [show values9 (5 : Fin 33) = Real.sqrt (values8 (5 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (5 : Fin 20)) < (10905199038617521 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10905199038617521 / 10000000000000000 : ℝ))]
      norm_num
      change values8 (5 : Fin 20) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : ℝ)
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : ℝ))]
      norm_num
      change values7 (5 : Fin 13) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ))]
      norm_num
      change values6 (5 : Fin 8) < (200017858355834144152057285593529953526086114939832688773440502100850437168712195190982786797967106432267261395823796759254399361 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (200017858355834144152057285593529953526086114939832688773440502100850437168712195190982786797967106432267261395823796759254399361 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (1011 / 500 : ℝ) < values13 (152 : Fin 264) := by
    rw [show values13 (152 : Fin 264) = Real.sqrt (values12 (147 : Fin 154)) by rfl]
    change (1011 / 500 : ℝ) < Real.sqrt (values12 (147 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1022121 / 250000 : ℝ) < values12 (147 : Fin 154)
    rw [show values12 (147 : Fin 154) = 1 + values10 (47 : Fin 54) by a158415_twelve_table]
    change (1022121 / 250000 : ℝ) < 1 + values10 (47 : Fin 54)
    have h5 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h6 : (309 / 100 : ℝ) < values10 (47 : Fin 54) := by
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by a158415_twelve_table]
      change (309 / 100 : ℝ) < 1 + values8 (13 : Fin 20)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (4181 / 2000 : ℝ) < values8 (13 : Fin 20) := by
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change (4181 / 2000 : ℝ) < 1 + values6 (1 : Fin 8)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (1090507 / 1000000 : ℝ) < values6 (1 : Fin 8) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change (1090507 / 1000000 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1189205517049 / 1000000000000 : ℝ) < values5 (1 : Fin 5)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (1189205517049 / 1000000000000 : ℝ) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1414209761779779429668401 / 1000000000000000000000000 : ℝ) < Real.sqrt 2
          change (1414209761779779429668401 / 1000000000000000000000000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_152 :
    values13 (152 : Fin 264) < values13 (153 : Fin 264) := by
  have hleft : values13 (152 : Fin 264) < (2023 / 1000 : ℝ) := by
    rw [show values13 (152 : Fin 264) = Real.sqrt (values12 (147 : Fin 154)) by rfl]
    change Real.sqrt (values12 (147 : Fin 154)) < (2023 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2023 / 1000 : ℝ))]
    norm_num
    change values12 (147 : Fin 154) < (4092529 / 1000000 : ℝ)
    rw [show values12 (147 : Fin 154) = 1 + values10 (47 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (47 : Fin 54) < (4092529 / 1000000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (47 : Fin 54) < (3091 / 1000 : ℝ) := by
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (13 : Fin 20) < (3091 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values8 (13 : Fin 20) < (10453 / 5000 : ℝ) := by
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (1 : Fin 8) < (10453 / 5000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values6 (1 : Fin 8) < (109051 / 100000 : ℝ) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (1 : Fin 5)) < (109051 / 100000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109051 / 100000 : ℝ))]
          norm_num
          change values5 (1 : Fin 5) < (11892120601 / 10000000000 : ℝ)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (11892120601 / 10000000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11892120601 / 10000000000 : ℝ))]
          norm_num
          change Real.sqrt 2 < (141422532388728601201 / 100000000000000000000 : ℝ)
          change Real.sqrt (2) < (141422532388728601201 / 100000000000000000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141422532388728601201 / 100000000000000000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2023 / 1000 : ℝ) < values13 (153 : Fin 264) := by
    rw [show values13 (153 : Fin 264) = 1 + values11 (6 : Fin 91) by rfl]
    change (2023 / 1000 : ℝ) < 1 + values11 (6 : Fin 91)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (1027 / 1000 : ℝ) < values11 (6 : Fin 91) := by
      rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by a158415_twelve_table]
      change (1027 / 1000 : ℝ) < Real.sqrt (values10 (6 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1054729 / 1000000 : ℝ) < values10 (6 : Fin 54)
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by a158415_twelve_table]
      change (1054729 / 1000000 : ℝ) < Real.sqrt (values9 (6 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1112453263441 / 1000000000000 : ℝ) < values9 (6 : Fin 33)
      rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
      change (1112453263441 / 1000000000000 : ℝ) < Real.sqrt (values8 (6 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1237552263340530947160481 / 1000000000000000000000000 : ℝ) < values8 (6 : Fin 20)
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (1237552263340530947160481 / 1000000000000000000000000 : ℝ) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1531535604499270857675934697411020302836768151361 / 1000000000000000000000000000000000000000000000000 : ℝ) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (1531535604499270857675934697411020302836768151361 / 1000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2345601307848947005389892755452351872284504539052818223055200303796923946486940801176105406152321 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (2345601307848947005389892755452351872284504539052818223055200303796923946486940801176105406152321 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ) < 1 + Real.sqrt 2
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
theorem values13_special_155 :
    values13 (155 : Fin 264) < values13 (156 : Fin 264) := by
  have hleft : values13 (155 : Fin 264) < (409 / 200 : ℝ) := by
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    change 1 + values11 (8 : Fin 91) < (409 / 200 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (8 : Fin 91) < (10443 / 10000 : ℝ) := by
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (8 : Fin 54)) < (10443 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10443 / 10000 : ℝ))]
      norm_num
      change values10 (8 : Fin 54) < (109056249 / 100000000 : ℝ)
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (8 : Fin 33)) < (109056249 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109056249 / 100000000 : ℝ))]
      norm_num
      change values9 (8 : Fin 33) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (8 : Fin 20)) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893265445950001 / 10000000000000000 : ℝ))]
      norm_num
      change values8 (8 : Fin 20) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (8 : Fin 13)) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ))]
      norm_num
      change values7 (8 : Fin 13) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (0 : Fin 5) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values5 (0 : Fin 5) < (10001 / 10000 : ℝ) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change Real.sqrt (1) < (10001 / 10000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10001 / 10000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (409 / 200 : ℝ) < values13 (156 : Fin 264) := by
    rw [show values13 (156 : Fin 264) = Real.sqrt (values12 (148 : Fin 154)) by rfl]
    change (409 / 200 : ℝ) < Real.sqrt (values12 (148 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (167281 / 40000 : ℝ) < values12 (148 : Fin 154)
    rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by a158415_twelve_table]
    change (167281 / 40000 : ℝ) < 1 + values10 (48 : Fin 54)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (3189 / 1000 : ℝ) < values10 (48 : Fin 54) := by
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by a158415_twelve_table]
      change (3189 / 1000 : ℝ) < 1 + values8 (14 : Fin 20)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (5473 / 2500 : ℝ) < values8 (14 : Fin 20) := by
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change (5473 / 2500 : ℝ) < 1 + values6 (2 : Fin 8)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (1189207 / 1000000 : ℝ) < values6 (2 : Fin 8) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change (1189207 / 1000000 : ℝ) < Real.sqrt (values5 (2 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1414213288849 / 1000000000000 : ℝ) < values5 (2 : Fin 5)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (1414213288849 / 1000000000000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_156 :
    values13 (156 : Fin 264) < values13 (157 : Fin 264) := by
  have hleft : values13 (156 : Fin 264) < (2047 / 1000 : ℝ) := by
    rw [show values13 (156 : Fin 264) = Real.sqrt (values12 (148 : Fin 154)) by rfl]
    change Real.sqrt (values12 (148 : Fin 154)) < (2047 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2047 / 1000 : ℝ))]
    norm_num
    change values12 (148 : Fin 154) < (4190209 / 1000000 : ℝ)
    rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (48 : Fin 54) < (4190209 / 1000000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (48 : Fin 54) < (31893 / 10000 : ℝ) := by
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (14 : Fin 20) < (31893 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (14 : Fin 20) < (218921 / 100000 : ℝ) := by
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (2 : Fin 8) < (218921 / 100000 : ℝ)
        have h5 : 1 < (10000001 / 10000000 : ℝ) := by
          norm_num
        have h6 : values6 (2 : Fin 8) < (148651 / 125000 : ℝ) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (2 : Fin 5)) < (148651 / 125000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (148651 / 125000 : ℝ))]
          norm_num
          change values5 (2 : Fin 5) < (22097119801 / 15625000000 : ℝ)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (22097119801 / 15625000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22097119801 / 15625000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2047 / 1000 : ℝ) < values13 (157 : Fin 264) := by
    rw [show values13 (157 : Fin 264) = 1 + values11 (9 : Fin 91) by rfl]
    change (2047 / 1000 : ℝ) < 1 + values11 (9 : Fin 91)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (21 / 20 : ℝ) < values11 (9 : Fin 91) := by
      rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by a158415_twelve_table]
      change (21 / 20 : ℝ) < Real.sqrt (values10 (9 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (441 / 400 : ℝ) < values10 (9 : Fin 54)
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by a158415_twelve_table]
      change (441 / 400 : ℝ) < Real.sqrt (values9 (9 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (194481 / 160000 : ℝ) < values9 (9 : Fin 33)
      rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
      change (194481 / 160000 : ℝ) < Real.sqrt (values8 (9 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (37822859361 / 25600000000 : ℝ) < values8 (9 : Fin 20)
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (37822859361 / 25600000000 : ℝ) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1430568690241985328321 / 655360000000000000000 : ℝ) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (1430568690241985328321 / 655360000000000000000 : ℝ) < 1 + values5 (1 : Fin 5)
      have h9 : (999 / 1000 : ℝ) < 1 := by
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
theorem values13_special_161 :
    values13 (161 : Fin 264) < values13 (162 : Fin 264) := by
  have hleft : values13 (161 : Fin 264) < (2097 / 1000 : ℝ) := by
    rw [show values13 (161 : Fin 264) = 1 + values11 (13 : Fin 91) by rfl]
    change 1 + values11 (13 : Fin 91) < (2097 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (13 : Fin 91) < (5483 / 5000 : ℝ) := by
      rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (13 : Fin 54)) < (5483 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5483 / 5000 : ℝ))]
      norm_num
      change values10 (13 : Fin 54) < (30063289 / 25000000 : ℝ)
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (13 : Fin 33)) < (30063289 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (30063289 / 25000000 : ℝ))]
      norm_num
      change values9 (13 : Fin 33) < (903801345497521 / 625000000000000 : ℝ)
      rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (13 : Fin 20)) < (903801345497521 / 625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (903801345497521 / 625000000000000 : ℝ))]
      norm_num
      change values8 (13 : Fin 20) < (816856872123129323179017145441 / 390625000000000000000000000000 : ℝ)
      rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (1 : Fin 8) < (816856872123129323179017145441 / 390625000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values6 (1 : Fin 8) < (5453 / 5000 : ℝ) := by
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
    linarith
  have hright : (2097 / 1000 : ℝ) < values13 (162 : Fin 264) := by
    rw [show values13 (162 : Fin 264) = Real.sqrt (values12 (149 : Fin 154)) by rfl]
    change (2097 / 1000 : ℝ) < Real.sqrt (values12 (149 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (4397409 / 1000000 : ℝ) < values12 (149 : Fin 154)
    rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by a158415_twelve_table]
    change (4397409 / 1000000 : ℝ) < 1 + values10 (49 : Fin 54)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1707 / 500 : ℝ) < values10 (49 : Fin 54) := by
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change (1707 / 500 : ℝ) < 1 + values8 (15 : Fin 20)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (12071 / 5000 : ℝ) < values8 (15 : Fin 20) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change (12071 / 5000 : ℝ) < 1 + values6 (3 : Fin 8)
        have h9 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h10 : (141421 / 100000 : ℝ) < values6 (3 : Fin 8) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (141421 / 100000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (19999899241 / 10000000000 : ℝ) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (19999899241 / 10000000000 : ℝ) < 1 + 1
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
theorem values13_special_162 :
    values13 (162 : Fin 264) < values13 (163 : Fin 264) := by
  have hleft : values13 (162 : Fin 264) < (1051 / 500 : ℝ) := by
    rw [show values13 (162 : Fin 264) = Real.sqrt (values12 (149 : Fin 154)) by rfl]
    change Real.sqrt (values12 (149 : Fin 154)) < (1051 / 500 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (1051 / 500 : ℝ))]
    norm_num
    change values12 (149 : Fin 154) < (1104601 / 250000 : ℝ)
    rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (49 : Fin 54) < (1104601 / 250000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values10 (49 : Fin 54) < (683 / 200 : ℝ) := by
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (15 : Fin 20) < (683 / 200 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values8 (15 : Fin 20) < (24143 / 10000 : ℝ) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (3 : Fin 8) < (24143 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values6 (3 : Fin 8) < (70711 / 50000 : ℝ) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (70711 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
          norm_num
          change values5 (3 : Fin 5) < (5000045521 / 2500000000 : ℝ)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (5000045521 / 2500000000 : ℝ)
          have h7 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1051 / 500 : ℝ) < values13 (163 : Fin 264) := by
    rw [show values13 (163 : Fin 264) = 1 + values11 (14 : Fin 91) by rfl]
    change (1051 / 500 : ℝ) < 1 + values11 (14 : Fin 91)
    have h9 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h10 : (2757 / 2500 : ℝ) < values11 (14 : Fin 91) := by
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by a158415_twelve_table]
      change (2757 / 2500 : ℝ) < Real.sqrt (values10 (14 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (7601049 / 6250000 : ℝ) < values10 (14 : Fin 54)
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by a158415_twelve_table]
      change (7601049 / 6250000 : ℝ) < Real.sqrt (values9 (14 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (57775945900401 / 39062500000000 : ℝ) < values9 (14 : Fin 33)
      rw [show values9 (14 : Fin 33) = Real.sqrt (values8 (14 : Fin 20)) by a158415_twelve_table]
      change (57775945900401 / 39062500000000 : ℝ) < Real.sqrt (values8 (14 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3338059924686063118611960801 / 1525878906250000000000000000 : ℝ) < values8 (14 : Fin 20)
      rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
      change (3338059924686063118611960801 / 1525878906250000000000000000 : ℝ) < 1 + values6 (2 : Fin 8)
      have h11 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h12 : (1189 / 1000 : ℝ) < values6 (2 : Fin 8) := by
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
  linarith

set_option linter.unusedTactic false in
theorem values13_special_167 :
    values13 (167 : Fin 264) < values13 (168 : Fin 264) := by
  have hleft : values13 (167 : Fin 264) < (1083 / 500 : ℝ) := by
    rw [show values13 (167 : Fin 264) = 1 + values11 (18 : Fin 91) by rfl]
    change 1 + values11 (18 : Fin 91) < (1083 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (18 : Fin 91) < (116591 / 100000 : ℝ) := by
      rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (18 : Fin 54)) < (116591 / 100000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (116591 / 100000 : ℝ))]
      norm_num
      change values10 (18 : Fin 54) < (13593461281 / 10000000000 : ℝ)
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (18 : Fin 33)) < (13593461281 / 10000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (13593461281 / 10000000000 : ℝ))]
      norm_num
      change values9 (18 : Fin 33) < (184782189598046160961 / 100000000000000000000 : ℝ)
      rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (18 : Fin 20)) < (184782189598046160961 / 100000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (184782189598046160961 / 100000000000000000000 : ℝ))]
      norm_num
      change values8 (18 : Fin 20) < (34144457592648278848499057898190320443521 / 10000000000000000000000000000000000000000 : ℝ)
      rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (6 : Fin 8) < (34144457592648278848499057898190320443521 / 10000000000000000000000000000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values6 (6 : Fin 8) < (120711 / 50000 : ℝ) := by
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (120711 / 50000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : Real.sqrt 2 < (707107 / 500000 : ℝ) := by
          change Real.sqrt (2) < (707107 / 500000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1083 / 500 : ℝ) < values13 (168 : Fin 264) := by
    rw [show values13 (168 : Fin 264) = Real.sqrt (values12 (150 : Fin 154)) by rfl]
    change (1083 / 500 : ℝ) < Real.sqrt (values12 (150 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1172889 / 250000 : ℝ) < values12 (150 : Fin 154)
    rw [show values12 (150 : Fin 154) = 1 + values10 (50 : Fin 54) by a158415_twelve_table]
    change (1172889 / 250000 : ℝ) < 1 + values10 (50 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (933 / 250 : ℝ) < values10 (50 : Fin 54) := by
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change (933 / 250 : ℝ) < 1 + values8 (16 : Fin 20)
      have h9 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h10 : (54641 / 20000 : ℝ) < values8 (16 : Fin 20) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change (54641 / 20000 : ℝ) < 1 + values6 (4 : Fin 8)
        have h11 : (9999999 / 10000000 : ℝ) < 1 := by
          norm_num
        have h12 : (4330127 / 2500000 : ℝ) < values6 (4 : Fin 8) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change (4330127 / 2500000 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (18749999836129 / 6250000000000 : ℝ) < values5 (4 : Fin 5)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change (18749999836129 / 6250000000000 : ℝ) < 1 + 2
          have h13 : (999999999 / 1000000000 : ℝ) < 1 := by
            norm_num
          have h14 : (1999999999 / 1000000000 : ℝ) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_168 :
    values13 (168 : Fin 264) < values13 (169 : Fin 264) := by
  have hleft : values13 (168 : Fin 264) < (272 / 125 : ℝ) := by
    rw [show values13 (168 : Fin 264) = Real.sqrt (values12 (150 : Fin 154)) by rfl]
    change Real.sqrt (values12 (150 : Fin 154)) < (272 / 125 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (272 / 125 : ℝ))]
    norm_num
    change values12 (150 : Fin 154) < (73984 / 15625 : ℝ)
    rw [show values12 (150 : Fin 154) = 1 + values10 (50 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (50 : Fin 54) < (73984 / 15625 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (50 : Fin 54) < (3733 / 1000 : ℝ) := by
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (16 : Fin 20) < (3733 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values8 (16 : Fin 20) < (27321 / 10000 : ℝ) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (4 : Fin 8) < (27321 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values6 (4 : Fin 8) < (86603 / 50000 : ℝ) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (86603 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (86603 / 50000 : ℝ))]
          norm_num
          change values5 (4 : Fin 5) < (7500079609 / 2500000000 : ℝ)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (7500079609 / 2500000000 : ℝ)
          have h7 : 1 < (100001 / 100000 : ℝ) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (272 / 125 : ℝ) < values13 (169 : Fin 264) := by
    rw [show values13 (169 : Fin 264) = values6 (1 : Fin 8) + values6 (1 : Fin 8) by rfl]
    change (272 / 125 : ℝ) < values6 (1 : Fin 8) + values6 (1 : Fin 8)
    have h9 : (109 / 100 : ℝ) < values6 (1 : Fin 8) := by
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
    have h10 : (109 / 100 : ℝ) < values6 (1 : Fin 8) := by
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
theorem values13_special_169 :
    values13 (169 : Fin 264) < values13 (170 : Fin 264) := by
  have hleft : values13 (169 : Fin 264) < (1091 / 500 : ℝ) := by
    rw [show values13 (169 : Fin 264) = values6 (1 : Fin 8) + values6 (1 : Fin 8) by rfl]
    change values6 (1 : Fin 8) + values6 (1 : Fin 8) < (1091 / 500 : ℝ)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : ℝ) := by
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
  have hright : (1091 / 500 : ℝ) < values13 (170 : Fin 264) := by
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    change (1091 / 500 : ℝ) < 1 + values11 (19 : Fin 91)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (1189 / 1000 : ℝ) < values11 (19 : Fin 91) := by
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (values10 (19 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < values10 (19 : Fin 54)
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by a158415_twelve_table]
      change (1413721 / 1000000 : ℝ) < Real.sqrt (values9 (19 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : ℝ) < values9 (19 : Fin 33)
      rw [show values9 (19 : Fin 33) = Real.sqrt (values8 (19 : Fin 20)) by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : ℝ) < Real.sqrt (values8 (19 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3994430203629571309037281 / 1000000000000000000000000 : ℝ) < values8 (19 : Fin 20)
      rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
      change (3994430203629571309037281 / 1000000000000000000000000 : ℝ) < 1 + values6 (7 : Fin 8)
      have h5 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h6 : (2999 / 1000 : ℝ) < values6 (7 : Fin 8) := by
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (2999 / 1000 : ℝ) < 1 + 2
        have h7 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h8 : (19999 / 10000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_173 :
    values13 (173 : Fin 264) < values13 (174 : Fin 264) := by
  have hleft : values13 (173 : Fin 264) < (2217 / 1000 : ℝ) := by
    rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
    change 1 + values11 (22 : Fin 91) < (2217 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (22 : Fin 91) < (3041 / 2500 : ℝ) := by
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (22 : Fin 54)) < (3041 / 2500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (3041 / 2500 : ℝ))]
      norm_num
      change values10 (22 : Fin 54) < (9247681 / 6250000 : ℝ)
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (22 : Fin 33)) < (9247681 / 6250000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9247681 / 6250000 : ℝ))]
      norm_num
      change values9 (22 : Fin 33) < (85519603877761 / 39062500000000 : ℝ)
      rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (3 : Fin 13) < (85519603877761 / 39062500000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
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
  have hright : (2217 / 1000 : ℝ) < values13 (174 : Fin 264) := by
    rw [show values13 (174 : Fin 264) = values5 (1 : Fin 5) + values7 (1 : Fin 13) by rfl]
    change (2217 / 1000 : ℝ) < values5 (1 : Fin 5) + values7 (1 : Fin 13)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (261 / 250 : ℝ) < values7 (1 : Fin 13) := by
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
theorem values13_special_174 :
    values13 (174 : Fin 264) < values13 (175 : Fin 264) := by
  have hleft : values13 (174 : Fin 264) < (4467 / 2000 : ℝ) := by
    rw [show values13 (174 : Fin 264) = values5 (1 : Fin 5) + values7 (1 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (1 : Fin 13) < (4467 / 2000 : ℝ)
    have h1 : values5 (1 : Fin 5) < (118921 / 100000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118921 / 100000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (14142204241 / 10000000000 : ℝ)
      change Real.sqrt (2) < (14142204241 / 10000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142204241 / 10000000000 : ℝ))]
      norm_num
    have h2 : values7 (1 : Fin 13) < (26107 / 25000 : ℝ) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (26107 / 25000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (26107 / 25000 : ℝ))]
      norm_num
      change values6 (1 : Fin 8) < (681575449 / 625000000 : ℝ)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (681575449 / 625000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (681575449 / 625000000 : ℝ))]
      norm_num
      change values5 (1 : Fin 5) < (464545092679551601 / 390625000000000000 : ℝ)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (464545092679551601 / 390625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (464545092679551601 / 390625000000000000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ)
      change Real.sqrt (2) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (4467 / 2000 : ℝ) < values13 (175 : Fin 264) := by
    rw [show values13 (175 : Fin 264) = 1 + values11 (23 : Fin 91) by rfl]
    change (4467 / 2000 : ℝ) < 1 + values11 (23 : Fin 91)
    have h3 : (99999 / 100000 : ℝ) < 1 := by
      norm_num
    have h4 : (771 / 625 : ℝ) < values11 (23 : Fin 91) := by
      rw [show values11 (23 : Fin 91) = Real.sqrt (values10 (23 : Fin 54)) by a158415_twelve_table]
      change (771 / 625 : ℝ) < Real.sqrt (values10 (23 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (594441 / 390625 : ℝ) < values10 (23 : Fin 54)
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by a158415_twelve_table]
      change (594441 / 390625 : ℝ) < Real.sqrt (values9 (23 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (353360102481 / 152587890625 : ℝ) < values9 (23 : Fin 33)
      rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
      change (353360102481 / 152587890625 : ℝ) < 1 + values7 (4 : Fin 13)
      have h5 : (99999 / 100000 : ℝ) < 1 := by
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
theorem values13_special_175 :
    values13 (175 : Fin 264) < values13 (176 : Fin 264) := by
  have hleft : values13 (175 : Fin 264) < (1117 / 500 : ℝ) := by
    rw [show values13 (175 : Fin 264) = 1 + values11 (23 : Fin 91) by rfl]
    change 1 + values11 (23 : Fin 91) < (1117 / 500 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (23 : Fin 91) < (12337 / 10000 : ℝ) := by
      rw [show values11 (23 : Fin 91) = Real.sqrt (values10 (23 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (23 : Fin 54)) < (12337 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (12337 / 10000 : ℝ))]
      norm_num
      change values10 (23 : Fin 54) < (152201569 / 100000000 : ℝ)
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (23 : Fin 33)) < (152201569 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (152201569 / 100000000 : ℝ))]
      norm_num
      change values9 (23 : Fin 33) < (23165317606061761 / 10000000000000000 : ℝ)
      rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (4 : Fin 13) < (23165317606061761 / 10000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values7 (4 : Fin 13) < (13161 / 10000 : ℝ) := by
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
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : ℝ) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (1117 / 500 : ℝ) < values13 (176 : Fin 264) := by
    rw [show values13 (176 : Fin 264) = Real.sqrt (values12 (151 : Fin 154)) by rfl]
    change (1117 / 500 : ℝ) < Real.sqrt (values12 (151 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1247689 / 250000 : ℝ) < values12 (151 : Fin 154)
    rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by a158415_twelve_table]
    change (1247689 / 250000 : ℝ) < 1 + values10 (51 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (3999 / 1000 : ℝ) < values10 (51 : Fin 54) := by
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by a158415_twelve_table]
      change (3999 / 1000 : ℝ) < 1 + values8 (17 : Fin 20)
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (29999 / 10000 : ℝ) < values8 (17 : Fin 20) := by
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change (29999 / 10000 : ℝ) < 1 + values6 (5 : Fin 8)
        have h11 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : ℝ) < values6 (5 : Fin 8) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : ℝ) < 1 + 1
          have h13 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          have h14 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_176 :
    values13 (176 : Fin 264) < values13 (177 : Fin 264) := by
  have hleft : values13 (176 : Fin 264) < (2237 / 1000 : ℝ) := by
    rw [show values13 (176 : Fin 264) = Real.sqrt (values12 (151 : Fin 154)) by rfl]
    change Real.sqrt (values12 (151 : Fin 154)) < (2237 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2237 / 1000 : ℝ))]
    norm_num
    change values12 (151 : Fin 154) < (5004169 / 1000000 : ℝ)
    rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (51 : Fin 54) < (5004169 / 1000000 : ℝ)
    have h1 : 1 < (1001 / 1000 : ℝ) := by
      norm_num
    have h2 : values10 (51 : Fin 54) < (4001 / 1000 : ℝ) := by
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (17 : Fin 20) < (4001 / 1000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : values8 (17 : Fin 20) < (30001 / 10000 : ℝ) := by
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (5 : Fin 8) < (30001 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values6 (5 : Fin 8) < (200001 / 100000 : ℝ) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (200001 / 100000 : ℝ)
          have h7 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2237 / 1000 : ℝ) < values13 (177 : Fin 264) := by
    rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
    change (2237 / 1000 : ℝ) < 1 + values11 (24 : Fin 91)
    have h9 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h10 : (623 / 500 : ℝ) < values11 (24 : Fin 91) := by
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by a158415_twelve_table]
      change (623 / 500 : ℝ) < Real.sqrt (values10 (24 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : ℝ) < values10 (24 : Fin 54)
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by a158415_twelve_table]
      change (388129 / 250000 : ℝ) < Real.sqrt (values9 (24 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : ℝ) < values9 (24 : Fin 33)
      rw [show values9 (24 : Fin 33) = 1 + values7 (5 : Fin 13) by a158415_twelve_table]
      change (150644120641 / 62500000000 : ℝ) < 1 + values7 (5 : Fin 13)
      have h11 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h12 : (707 / 500 : ℝ) < values7 (5 : Fin 13) := by
        rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
        change (707 / 500 : ℝ) < Real.sqrt (values6 (5 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (499849 / 250000 : ℝ) < values6 (5 : Fin 8)
        rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
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
theorem values13_special_178 :
    values13 (178 : Fin 264) < values13 (179 : Fin 264) := by
  have hleft : values13 (178 : Fin 264) < (453 / 200 : ℝ) := by
    rw [show values13 (178 : Fin 264) = 1 + values11 (25 : Fin 91) by rfl]
    change 1 + values11 (25 : Fin 91) < (453 / 200 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (25 : Fin 91) < (6321 / 5000 : ℝ) := by
      rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (25 : Fin 54)) < (6321 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (6321 / 5000 : ℝ))]
      norm_num
      change values10 (25 : Fin 54) < (39955041 / 25000000 : ℝ)
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (25 : Fin 33)) < (39955041 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (39955041 / 25000000 : ℝ))]
      norm_num
      change values9 (25 : Fin 33) < (1596405301311681 / 625000000000000 : ℝ)
      rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (6 : Fin 13) < (1596405301311681 / 625000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
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
  have hright : (453 / 200 : ℝ) < values13 (179 : Fin 264) := by
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    change (453 / 200 : ℝ) < values5 (1 : Fin 5) + values7 (2 : Fin 13)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
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
theorem values13_special_179 :
    values13 (179 : Fin 264) < values13 (180 : Fin 264) := by
  have hleft : values13 (179 : Fin 264) < (57 / 25 : ℝ) := by
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (2 : Fin 13) < (57 / 25 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
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
  have hright : (57 / 25 : ℝ) < values13 (180 : Fin 264) := by
    rw [show values13 (180 : Fin 264) = 1 + values11 (26 : Fin 91) by rfl]
    change (57 / 25 : ℝ) < 1 + values11 (26 : Fin 91)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (257 / 200 : ℝ) < values11 (26 : Fin 91) := by
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by a158415_twelve_table]
      change (257 / 200 : ℝ) < Real.sqrt (values10 (26 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (66049 / 40000 : ℝ) < values10 (26 : Fin 54)
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by a158415_twelve_table]
      change (66049 / 40000 : ℝ) < Real.sqrt (values9 (26 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4362470401 / 1600000000 : ℝ) < values9 (26 : Fin 33)
      rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
      change (4362470401 / 1600000000 : ℝ) < 1 + values7 (7 : Fin 13)
      have h5 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h6 : (433 / 250 : ℝ) < values7 (7 : Fin 13) := by
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (433 / 250 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : ℝ) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
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
theorem values13_special_182 :
    values13 (182 : Fin 264) < values13 (183 : Fin 264) := by
  have hleft : values13 (182 : Fin 264) < (2317 / 1000 : ℝ) := by
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    change 1 + values11 (28 : Fin 91) < (2317 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (28 : Fin 91) < (13161 / 10000 : ℝ) := by
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (28 : Fin 54)) < (13161 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (13161 / 10000 : ℝ))]
      norm_num
      change values10 (28 : Fin 54) < (173211921 / 100000000 : ℝ)
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (28 : Fin 33)) < (173211921 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (173211921 / 100000000 : ℝ))]
      norm_num
      change values9 (28 : Fin 33) < (30002369576510241 / 10000000000000000 : ℝ)
      rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (8 : Fin 13) < (30002369576510241 / 10000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values7 (8 : Fin 13) < (200001 / 100000 : ℝ) := by
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (0 : Fin 5) < (200001 / 100000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values5 (0 : Fin 5) < (1000001 / 1000000 : ℝ) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change Real.sqrt (1) < (1000001 / 1000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (1000001 / 1000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2317 / 1000 : ℝ) < values13 (183 : Fin 264) := by
    rw [show values13 (183 : Fin 264) = Real.sqrt (values12 (152 : Fin 154)) by rfl]
    change (2317 / 1000 : ℝ) < Real.sqrt (values12 (152 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (5368489 / 1000000 : ℝ) < values12 (152 : Fin 154)
    rw [show values12 (152 : Fin 154) = 1 + values10 (52 : Fin 54) by a158415_twelve_table]
    change (5368489 / 1000000 : ℝ) < 1 + values10 (52 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (2207 / 500 : ℝ) < values10 (52 : Fin 54) := by
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by a158415_twelve_table]
      change (2207 / 500 : ℝ) < 1 + values8 (18 : Fin 20)
      have h9 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h10 : (17071 / 5000 : ℝ) < values8 (18 : Fin 20) := by
        rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
        change (17071 / 5000 : ℝ) < 1 + values6 (6 : Fin 8)
        have h11 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h12 : (241421 / 100000 : ℝ) < values6 (6 : Fin 8) := by
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change (241421 / 100000 : ℝ) < 1 + Real.sqrt 2
          have h13 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          have h14 : (1414213 / 1000000 : ℝ) < Real.sqrt 2 := by
            change (1414213 / 1000000 : ℝ) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_183 :
    values13 (183 : Fin 264) < values13 (184 : Fin 264) := by
  have hleft : values13 (183 : Fin 264) < (2327 / 1000 : ℝ) := by
    rw [show values13 (183 : Fin 264) = Real.sqrt (values12 (152 : Fin 154)) by rfl]
    change Real.sqrt (values12 (152 : Fin 154)) < (2327 / 1000 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (2327 / 1000 : ℝ))]
    norm_num
    change values12 (152 : Fin 154) < (5414929 / 1000000 : ℝ)
    rw [show values12 (152 : Fin 154) = 1 + values10 (52 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (52 : Fin 54) < (5414929 / 1000000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (52 : Fin 54) < (44143 / 10000 : ℝ) := by
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (18 : Fin 20) < (44143 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (18 : Fin 20) < (170711 / 50000 : ℝ) := by
        rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (6 : Fin 8) < (170711 / 50000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values6 (6 : Fin 8) < (1207107 / 500000 : ℝ) := by
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change 1 + Real.sqrt 2 < (1207107 / 500000 : ℝ)
          have h7 : 1 < (10000001 / 10000000 : ℝ) := by
            norm_num
          have h8 : Real.sqrt 2 < (1767767 / 1250000 : ℝ) := by
            change Real.sqrt (2) < (1767767 / 1250000 : ℝ)
            rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (1767767 / 1250000 : ℝ))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2327 / 1000 : ℝ) < values13 (184 : Fin 264) := by
    rw [show values13 (184 : Fin 264) = 1 + values11 (29 : Fin 91) by rfl]
    change (2327 / 1000 : ℝ) < 1 + values11 (29 : Fin 91)
    have h9 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h10 : (167 / 125 : ℝ) < values11 (29 : Fin 91) := by
      rw [show values11 (29 : Fin 91) = Real.sqrt (values10 (29 : Fin 54)) by a158415_twelve_table]
      change (167 / 125 : ℝ) < Real.sqrt (values10 (29 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (27889 / 15625 : ℝ) < values10 (29 : Fin 54)
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by a158415_twelve_table]
      change (27889 / 15625 : ℝ) < Real.sqrt (values9 (29 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (777796321 / 244140625 : ℝ) < values9 (29 : Fin 33)
      rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
      change (777796321 / 244140625 : ℝ) < 1 + values7 (9 : Fin 13)
      have h11 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h12 : (2189 / 1000 : ℝ) < values7 (9 : Fin 13) := by
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change (2189 / 1000 : ℝ) < 1 + values5 (1 : Fin 5)
        have h13 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h14 : (2973 / 2500 : ℝ) < values5 (1 : Fin 5) := by
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (2973 / 2500 : ℝ) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (8838729 / 6250000 : ℝ) < Real.sqrt 2
          change (8838729 / 6250000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_185 :
    values13 (185 : Fin 264) < values13 (186 : Fin 264) := by
  have hleft : values13 (185 : Fin 264) < (59 / 25 : ℝ) := by
    rw [show values13 (185 : Fin 264) = 1 + values11 (30 : Fin 91) by rfl]
    change 1 + values11 (30 : Fin 91) < (59 / 25 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (30 : Fin 91) < (6797 / 5000 : ℝ) := by
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (30 : Fin 54)) < (6797 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (6797 / 5000 : ℝ))]
      norm_num
      change values10 (30 : Fin 54) < (46199209 / 25000000 : ℝ)
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (30 : Fin 33)) < (46199209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (46199209 / 25000000 : ℝ))]
      norm_num
      change values9 (30 : Fin 33) < (2134366912225681 / 625000000000000 : ℝ)
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (10 : Fin 13) < (2134366912225681 / 625000000000000 : ℝ)
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
  have hright : (59 / 25 : ℝ) < values13 (186 : Fin 264) := by
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    change (59 / 25 : ℝ) < values5 (1 : Fin 5) + values7 (3 : Fin 13)
    have h7 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
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
theorem values13_special_186 :
    values13 (186 : Fin 264) < values13 (187 : Fin 264) := by
  have hleft : values13 (186 : Fin 264) < (2379 / 1000 : ℝ) := by
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (3 : Fin 13) < (2379 / 1000 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
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
  have hright : (2379 / 1000 : ℝ) < values13 (187 : Fin 264) := by
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    change (2379 / 1000 : ℝ) < 1 + values11 (31 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (707 / 500 : ℝ) < values11 (31 : Fin 91) := by
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by a158415_twelve_table]
      change (707 / 500 : ℝ) < Real.sqrt (values10 (31 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : ℝ) < values10 (31 : Fin 54)
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by a158415_twelve_table]
      change (499849 / 250000 : ℝ) < Real.sqrt (values9 (31 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (249849022801 / 62500000000 : ℝ) < values9 (31 : Fin 33)
      rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
      change (249849022801 / 62500000000 : ℝ) < 1 + values7 (11 : Fin 13)
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
theorem values13_special_189 :
    values13 (189 : Fin 264) < values13 (190 : Fin 264) := by
  have hleft : values13 (189 : Fin 264) < (243 / 100 : ℝ) := by
    rw [show values13 (189 : Fin 264) = 1 + values11 (33 : Fin 91) by rfl]
    change 1 + values11 (33 : Fin 91) < (243 / 100 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (33 : Fin 91) < (7149 / 5000 : ℝ) := by
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (33 : Fin 54)) < (7149 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (7149 / 5000 : ℝ))]
      norm_num
      change values10 (33 : Fin 54) < (51108201 / 25000000 : ℝ)
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (2 : Fin 20) < (51108201 / 25000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (2 : Fin 20) < (26107 / 25000 : ℝ) := by
        rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (2 : Fin 13)) < (26107 / 25000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (26107 / 25000 : ℝ))]
        norm_num
        change values7 (2 : Fin 13) < (681575449 / 625000000 : ℝ)
        rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (2 : Fin 8)) < (681575449 / 625000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (681575449 / 625000000 : ℝ))]
        norm_num
        change values6 (2 : Fin 8) < (464545092679551601 / 390625000000000000 : ℝ)
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (464545092679551601 / 390625000000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (464545092679551601 / 390625000000000000 : ℝ))]
        norm_num
        change values5 (2 : Fin 5) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (243 / 100 : ℝ) < values13 (190 : Fin 264) := by
    rw [show values13 (190 : Fin 264) = Real.sqrt 2 + values8 (1 : Fin 20) by rfl]
    change (243 / 100 : ℝ) < Real.sqrt 2 + values8 (1 : Fin 20)
    have h5 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (1021 / 1000 : ℝ) < values8 (1 : Fin 20) := by
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (1021 / 1000 : ℝ) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1042441 / 1000000 : ℝ) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (1042441 / 1000000 : ℝ) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1086683238481 / 1000000000000 : ℝ) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (1086683238481 / 1000000000000 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1180880460795553919187361 / 1000000000000000000000000 : ℝ) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1180880460795553919187361 / 1000000000000000000000000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1394478662688719756722453406066490116670622144321 / 1000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt 2
      change (1394478662688719756722453406066490116670622144321 / 1000000000000000000000000000000000000000000000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_190 :
    values13 (190 : Fin 264) < values13 (191 : Fin 264) := by
  have hleft : values13 (190 : Fin 264) < (2437 / 1000 : ℝ) := by
    rw [show values13 (190 : Fin 264) = Real.sqrt 2 + values8 (1 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (1 : Fin 20) < (2437 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (1 : Fin 20) < (511 / 500 : ℝ) := by
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (1 : Fin 13)) < (511 / 500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (511 / 500 : ℝ))]
      norm_num
      change values7 (1 : Fin 13) < (261121 / 250000 : ℝ)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (261121 / 250000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (261121 / 250000 : ℝ))]
      norm_num
      change values6 (1 : Fin 8) < (68184176641 / 62500000000 : ℝ)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (68184176641 / 62500000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (68184176641 / 62500000000 : ℝ))]
      norm_num
      change values5 (1 : Fin 5) < (4649081944211090042881 / 3906250000000000000000 : ℝ)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (4649081944211090042881 / 3906250000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (4649081944211090042881 / 3906250000000000000000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : ℝ)
      change Real.sqrt (2) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (2437 / 1000 : ℝ) < values13 (191 : Fin 264) := by
    rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
    change (2437 / 1000 : ℝ) < 1 + values11 (34 : Fin 91)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (289 / 200 : ℝ) < values11 (34 : Fin 91) := by
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by a158415_twelve_table]
      change (289 / 200 : ℝ) < Real.sqrt (values10 (34 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (83521 / 40000 : ℝ) < values10 (34 : Fin 54)
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by a158415_twelve_table]
      change (83521 / 40000 : ℝ) < 1 + values8 (3 : Fin 20)
      have h5 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h6 : (109 / 100 : ℝ) < values8 (3 : Fin 20) := by
        rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
        change (109 / 100 : ℝ) < Real.sqrt (values7 (3 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11881 / 10000 : ℝ) < values7 (3 : Fin 13)
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change (11881 / 10000 : ℝ) < Real.sqrt (values6 (3 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (141158161 / 100000000 : ℝ) < values6 (3 : Fin 8)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (141158161 / 100000000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (19925626416901921 / 10000000000000000 : ℝ) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (19925626416901921 / 10000000000000000 : ℝ) < 1 + 1
        have h7 : (999 / 1000 : ℝ) < 1 := by
          norm_num
        have h8 : (999 / 1000 : ℝ) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_191 :
    values13 (191 : Fin 264) < values13 (192 : Fin 264) := by
  have hleft : values13 (191 : Fin 264) < (1223 / 500 : ℝ) := by
    rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
    change 1 + values11 (34 : Fin 91) < (1223 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (34 : Fin 91) < (14459 / 10000 : ℝ) := by
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (34 : Fin 54)) < (14459 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14459 / 10000 : ℝ))]
      norm_num
      change values10 (34 : Fin 54) < (209062681 / 100000000 : ℝ)
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (3 : Fin 20) < (209062681 / 100000000 : ℝ)
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
  have hright : (1223 / 500 : ℝ) < values13 (192 : Fin 264) := by
    rw [show values13 (192 : Fin 264) = Real.sqrt (values12 (153 : Fin 154)) by rfl]
    change (1223 / 500 : ℝ) < Real.sqrt (values12 (153 : Fin 154))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1495729 / 250000 : ℝ) < values12 (153 : Fin 154)
    rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by a158415_twelve_table]
    change (1495729 / 250000 : ℝ) < 1 + values10 (53 : Fin 54)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (4999 / 1000 : ℝ) < values10 (53 : Fin 54) := by
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by a158415_twelve_table]
      change (4999 / 1000 : ℝ) < 1 + values8 (19 : Fin 20)
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (39999 / 10000 : ℝ) < values8 (19 : Fin 20) := by
        rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
        change (39999 / 10000 : ℝ) < 1 + values6 (7 : Fin 8)
        have h11 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h12 : (299999 / 100000 : ℝ) < values6 (7 : Fin 8) := by
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change (299999 / 100000 : ℝ) < 1 + 2
          have h13 : (999999 / 1000000 : ℝ) < 1 := by
            norm_num
          have h14 : (1999999 / 1000000 : ℝ) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_192 :
    values13 (192 : Fin 264) < values13 (193 : Fin 264) := by
  have hleft : values13 (192 : Fin 264) < (49 / 20 : ℝ) := by
    rw [show values13 (192 : Fin 264) = Real.sqrt (values12 (153 : Fin 154)) by rfl]
    change Real.sqrt (values12 (153 : Fin 154)) < (49 / 20 : ℝ)
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (49 / 20 : ℝ))]
    norm_num
    change values12 (153 : Fin 154) < (2401 / 400 : ℝ)
    rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by a158415_twelve_table]
    change 1 + values10 (53 : Fin 54) < (2401 / 400 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values10 (53 : Fin 54) < (50001 / 10000 : ℝ) := by
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (19 : Fin 20) < (50001 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (19 : Fin 20) < (400001 / 100000 : ℝ) := by
        rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (7 : Fin 8) < (400001 / 100000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values6 (7 : Fin 8) < (3000001 / 1000000 : ℝ) := by
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (3000001 / 1000000 : ℝ)
          have h7 : 1 < (10000001 / 10000000 : ℝ) := by
            norm_num
          have h8 : 2 < (20000001 / 10000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (49 / 20 : ℝ) < values13 (193 : Fin 264) := by
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    change (49 / 20 : ℝ) < Real.sqrt 2 + values8 (2 : Fin 20)
    have h9 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (261 / 250 : ℝ) < values8 (2 : Fin 20) := by
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change (261 / 250 : ℝ) < Real.sqrt (values7 (2 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : ℝ) < values7 (2 : Fin 13)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change (68121 / 62500 : ℝ) < Real.sqrt (values6 (2 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : ℝ) < values6 (2 : Fin 8)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (4640470641 / 3906250000 : ℝ) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : ℝ) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (21533967769982950881 / 15258789062500000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_193 :
    values13 (193 : Fin 264) < values13 (194 : Fin 264) := by
  have hleft : values13 (193 : Fin 264) < (2459 / 1000 : ℝ) := by
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (2 : Fin 20) < (2459 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (2 : Fin 20) < (10443 / 10000 : ℝ) := by
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (2 : Fin 13)) < (10443 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (10443 / 10000 : ℝ))]
      norm_num
      change values7 (2 : Fin 13) < (109056249 / 100000000 : ℝ)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (2 : Fin 8)) < (109056249 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (109056249 / 100000000 : ℝ))]
      norm_num
      change values6 (2 : Fin 8) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (11893265445950001 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893265445950001 / 10000000000000000 : ℝ))]
      norm_num
      change values5 (2 : Fin 5) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : ℝ))]
      norm_num
    linarith
  have hright : (2459 / 1000 : ℝ) < values13 (194 : Fin 264) := by
    rw [show values13 (194 : Fin 264) = 1 + values11 (35 : Fin 91) by rfl]
    change (2459 / 1000 : ℝ) < 1 + values11 (35 : Fin 91)
    have h3 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h4 : (293 / 200 : ℝ) < values11 (35 : Fin 91) := by
      rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by a158415_twelve_table]
      change (293 / 200 : ℝ) < Real.sqrt (values10 (35 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (85849 / 40000 : ℝ) < values10 (35 : Fin 54)
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by a158415_twelve_table]
      change (85849 / 40000 : ℝ) < 1 + values8 (4 : Fin 20)
      have h5 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h6 : (1147 / 1000 : ℝ) < values8 (4 : Fin 20) := by
        rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
        change (1147 / 1000 : ℝ) < Real.sqrt (values7 (4 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1315609 / 1000000 : ℝ) < values7 (4 : Fin 13)
        rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
        change (1315609 / 1000000 : ℝ) < Real.sqrt (values6 (4 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1730827040881 / 1000000000000 : ℝ) < values6 (4 : Fin 8)
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (1730827040881 / 1000000000000 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (2995762245444878845256161 / 1000000000000000000000000 : ℝ) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (2995762245444878845256161 / 1000000000000000000000000 : ℝ) < 1 + 2
        have h7 : (999 / 1000 : ℝ) < 1 := by
          norm_num
        have h8 : (1999 / 1000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_197 :
    values13 (197 : Fin 264) < values13 (198 : Fin 264) := by
  have hleft : values13 (197 : Fin 264) < (2499 / 1000 : ℝ) := by
    rw [show values13 (197 : Fin 264) = 1 + values11 (38 : Fin 91) by rfl]
    change 1 + values11 (38 : Fin 91) < (2499 / 1000 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (38 : Fin 91) < (37471 / 25000 : ℝ) := by
      rw [show values11 (38 : Fin 91) = Real.sqrt (values10 (38 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (38 : Fin 54)) < (37471 / 25000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (37471 / 25000 : ℝ))]
      norm_num
      change values10 (38 : Fin 54) < (1404075841 / 625000000 : ℝ)
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (6 : Fin 20) < (1404075841 / 625000000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values8 (6 : Fin 20) < (124651 / 100000 : ℝ) := by
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (6 : Fin 13)) < (124651 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (124651 / 100000 : ℝ))]
        norm_num
        change values7 (6 : Fin 13) < (15537871801 / 10000000000 : ℝ)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (15537871801 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (15537871801 / 10000000000 : ℝ))]
        norm_num
        change values6 (6 : Fin 8) < (241425460104310983601 / 100000000000000000000 : ℝ)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (241425460104310983601 / 100000000000000000000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
          change Real.sqrt (2) < (70711 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2499 / 1000 : ℝ) < values13 (198 : Fin 264) := by
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    change (2499 / 1000 : ℝ) < Real.sqrt 2 + values8 (3 : Fin 20)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (109 / 100 : ℝ) < values8 (3 : Fin 20) := by
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change (109 / 100 : ℝ) < Real.sqrt (values7 (3 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : ℝ) < values7 (3 : Fin 13)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change (11881 / 10000 : ℝ) < Real.sqrt (values6 (3 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : ℝ) < values6 (3 : Fin 8)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change (141158161 / 100000000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (19925626416901921 / 10000000000000000 : ℝ) < values5 (3 : Fin 5)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change (19925626416901921 / 10000000000000000 : ℝ) < 1 + 1
      have h9 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h10 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_198 :
    values13 (198 : Fin 264) < values13 (199 : Fin 264) := by
  have hleft : values13 (198 : Fin 264) < (501 / 200 : ℝ) := by
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (3 : Fin 20) < (501 / 200 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (3 : Fin 20) < (5453 / 5000 : ℝ) := by
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (3 : Fin 13)) < (5453 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5453 / 5000 : ℝ))]
      norm_num
      change values7 (3 : Fin 13) < (29735209 / 25000000 : ℝ)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (3 : Fin 8)) < (29735209 / 25000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (29735209 / 25000000 : ℝ))]
      norm_num
      change values6 (3 : Fin 8) < (884182654273681 / 625000000000000 : ℝ)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (3 : Fin 5)) < (884182654273681 / 625000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (884182654273681 / 625000000000000 : ℝ))]
      norm_num
      change values5 (3 : Fin 5) < (781778966118451701933649289761 / 390625000000000000000000000000 : ℝ)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (781778966118451701933649289761 / 390625000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (501 / 200 : ℝ) < values13 (199 : Fin 264) := by
    rw [show values13 (199 : Fin 264) = values5 (1 : Fin 5) + values7 (4 : Fin 13) by rfl]
    change (501 / 200 : ℝ) < values5 (1 : Fin 5) + values7 (4 : Fin 13)
    have h5 : (2973 / 2500 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (2973 / 2500 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (8838729 / 6250000 : ℝ) < Real.sqrt 2
      change (8838729 / 6250000 : ℝ) < Real.sqrt (2)
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
theorem values13_special_199 :
    values13 (199 : Fin 264) < values13 (200 : Fin 264) := by
  have hleft : values13 (199 : Fin 264) < (1253 / 500 : ℝ) := by
    rw [show values13 (199 : Fin 264) = values5 (1 : Fin 5) + values7 (4 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (4 : Fin 13) < (1253 / 500 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
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
  have hright : (1253 / 500 : ℝ) < values13 (200 : Fin 264) := by
    rw [show values13 (200 : Fin 264) = 1 + values11 (39 : Fin 91) by rfl]
    change (1253 / 500 : ℝ) < 1 + values11 (39 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1521 / 1000 : ℝ) < values11 (39 : Fin 91) := by
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by a158415_twelve_table]
      change (1521 / 1000 : ℝ) < Real.sqrt (values10 (39 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2313441 / 1000000 : ℝ) < values10 (39 : Fin 54)
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by a158415_twelve_table]
      change (2313441 / 1000000 : ℝ) < 1 + values8 (7 : Fin 20)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (329 / 250 : ℝ) < values8 (7 : Fin 20) := by
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change (329 / 250 : ℝ) < Real.sqrt (values7 (7 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108241 / 62500 : ℝ) < values7 (7 : Fin 13)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (108241 / 62500 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11716114081 / 3906250000 : ℝ) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (11716114081 / 3906250000 : ℝ) < 1 + 2
        have h9 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h10 : (19999 / 10000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_201 :
    values13 (201 : Fin 264) < values13 (202 : Fin 264) := by
  have hleft : values13 (201 : Fin 264) < (1277 / 500 : ℝ) := by
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    change 1 + values11 (40 : Fin 91) < (1277 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (40 : Fin 91) < (7769 / 5000 : ℝ) := by
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (40 : Fin 54)) < (7769 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (7769 / 5000 : ℝ))]
      norm_num
      change values10 (40 : Fin 54) < (60357361 / 25000000 : ℝ)
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (8 : Fin 20) < (60357361 / 25000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (8 : Fin 20) < (70711 / 50000 : ℝ) := by
        rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (8 : Fin 13)) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
        change values7 (8 : Fin 13) < (5000045521 / 2500000000 : ℝ)
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (0 : Fin 5) < (5000045521 / 2500000000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values5 (0 : Fin 5) < (1000001 / 1000000 : ℝ) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change Real.sqrt (1) < (1000001 / 1000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (1000001 / 1000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1277 / 500 : ℝ) < values13 (202 : Fin 264) := by
    rw [show values13 (202 : Fin 264) = Real.sqrt 2 + values8 (4 : Fin 20) by rfl]
    change (1277 / 500 : ℝ) < Real.sqrt 2 + values8 (4 : Fin 20)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1147 / 1000 : ℝ) < values8 (4 : Fin 20) := by
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change (1147 / 1000 : ℝ) < Real.sqrt (values7 (4 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1315609 / 1000000 : ℝ) < values7 (4 : Fin 13)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (1315609 / 1000000 : ℝ) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1730827040881 / 1000000000000 : ℝ) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (1730827040881 / 1000000000000 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2995762245444878845256161 / 1000000000000000000000000 : ℝ) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (2995762245444878845256161 / 1000000000000000000000000 : ℝ) < 1 + 2
      have h9 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h10 : (1999 / 1000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_202 :
    values13 (202 : Fin 264) < values13 (203 : Fin 264) := by
  have hleft : values13 (202 : Fin 264) < (1281 / 500 : ℝ) := by
    rw [show values13 (202 : Fin 264) = Real.sqrt 2 + values8 (4 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (4 : Fin 20) < (1281 / 500 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (4 : Fin 20) < (11473 / 10000 : ℝ) := by
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (4 : Fin 13)) < (11473 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11473 / 10000 : ℝ))]
      norm_num
      change values7 (4 : Fin 13) < (131629729 / 100000000 : ℝ)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (131629729 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (131629729 / 100000000 : ℝ))]
      norm_num
      change values6 (4 : Fin 8) < (17326385556613441 / 10000000000000000 : ℝ)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17326385556613441 / 10000000000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17326385556613441 / 10000000000000000 : ℝ))]
      norm_num
      change values5 (4 : Fin 5) < (300203636456422859700092701860481 / 100000000000000000000000000000000 : ℝ)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300203636456422859700092701860481 / 100000000000000000000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : 2 < (20001 / 10000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (1281 / 500 : ℝ) < values13 (203 : Fin 264) := by
    rw [show values13 (203 : Fin 264) = 1 + values11 (41 : Fin 91) by rfl]
    change (1281 / 500 : ℝ) < 1 + values11 (41 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (787 / 500 : ℝ) < values11 (41 : Fin 91) := by
      rw [show values11 (41 : Fin 91) = Real.sqrt (values10 (41 : Fin 54)) by a158415_twelve_table]
      change (787 / 500 : ℝ) < Real.sqrt (values10 (41 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (619369 / 250000 : ℝ) < values10 (41 : Fin 54)
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by a158415_twelve_table]
      change (619369 / 250000 : ℝ) < 1 + values8 (9 : Fin 20)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (1479 / 1000 : ℝ) < values8 (9 : Fin 20) := by
        rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
        change (1479 / 1000 : ℝ) < Real.sqrt (values7 (9 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (2187441 / 1000000 : ℝ) < values7 (9 : Fin 13)
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change (2187441 / 1000000 : ℝ) < 1 + values5 (1 : Fin 5)
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
  linarith

set_option linter.unusedTactic false in
theorem values13_special_204 :
    values13 (204 : Fin 264) < values13 (205 : Fin 264) := by
  have hleft : values13 (204 : Fin 264) < (2599 / 1000 : ℝ) := by
    rw [show values13 (204 : Fin 264) = 1 + values11 (42 : Fin 91) by rfl]
    change 1 + values11 (42 : Fin 91) < (2599 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (42 : Fin 91) < (15981 / 10000 : ℝ) := by
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (42 : Fin 54)) < (15981 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (15981 / 10000 : ℝ))]
      norm_num
      change values10 (42 : Fin 54) < (255392361 / 100000000 : ℝ)
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (10 : Fin 20) < (255392361 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (10 : Fin 20) < (7769 / 5000 : ℝ) := by
        rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (10 : Fin 13)) < (7769 / 5000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (7769 / 5000 : ℝ))]
        norm_num
        change values7 (10 : Fin 13) < (60357361 / 25000000 : ℝ)
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (60357361 / 25000000 : ℝ)
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
  have hright : (2599 / 1000 : ℝ) < values13 (205 : Fin 264) := by
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    change (2599 / 1000 : ℝ) < Real.sqrt 2 + values8 (5 : Fin 20)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1189 / 1000 : ℝ) < values8 (5 : Fin 20) := by
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (values7 (5 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < values7 (5 : Fin 13)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change (1413721 / 1000000 : ℝ) < Real.sqrt (values6 (5 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : ℝ) < values6 (5 : Fin 8)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : ℝ) < 1 + 1
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_205 :
    values13 (205 : Fin 264) < values13 (206 : Fin 264) := by
  have hleft : values13 (205 : Fin 264) < (651 / 250 : ℝ) := by
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (5 : Fin 20) < (651 / 250 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (5 : Fin 20) < (11893 / 10000 : ℝ) := by
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change values7 (5 : Fin 13) < (141443449 / 100000000 : ℝ)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
      norm_num
      change values6 (5 : Fin 8) < (20006249265015601 / 10000000000000000 : ℝ)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20006249265015601 / 10000000000000000 : ℝ)
      have h3 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (651 / 250 : ℝ) < values13 (206 : Fin 264) := by
    rw [show values13 (206 : Fin 264) = 1 + values11 (43 : Fin 91) by rfl]
    change (651 / 250 : ℝ) < 1 + values11 (43 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1613 / 1000 : ℝ) < values11 (43 : Fin 91) := by
      rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by a158415_twelve_table]
      change (1613 / 1000 : ℝ) < Real.sqrt (values10 (43 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2601769 / 1000000 : ℝ) < values10 (43 : Fin 54)
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (2601769 / 1000000 : ℝ) < Real.sqrt 2 + values5 (1 : Fin 5)
      have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h8 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
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
theorem values13_special_207 :
    values13 (207 : Fin 264) < values13 (208 : Fin 264) := by
  have hleft : values13 (207 : Fin 264) < (2653 / 1000 : ℝ) := by
    rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
    change 1 + values11 (44 : Fin 91) < (2653 / 1000 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (44 : Fin 91) < (16529 / 10000 : ℝ) := by
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (44 : Fin 54)) < (16529 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (16529 / 10000 : ℝ))]
      norm_num
      change values10 (44 : Fin 54) < (273207841 / 100000000 : ℝ)
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (11 : Fin 20) < (273207841 / 100000000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values8 (11 : Fin 20) < (86603 / 50000 : ℝ) := by
        rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (11 : Fin 13)) < (86603 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (86603 / 50000 : ℝ))]
        norm_num
        change values7 (11 : Fin 13) < (7500079609 / 2500000000 : ℝ)
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (3 : Fin 5) < (7500079609 / 2500000000 : ℝ)
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
  have hright : (2653 / 1000 : ℝ) < values13 (208 : Fin 264) := by
    rw [show values13 (208 : Fin 264) = Real.sqrt 2 + values8 (6 : Fin 20) by rfl]
    change (2653 / 1000 : ℝ) < Real.sqrt 2 + values8 (6 : Fin 20)
    have h9 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (623 / 500 : ℝ) < values8 (6 : Fin 20) := by
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (623 / 500 : ℝ) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : ℝ) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (388129 / 250000 : ℝ) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : ℝ) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (150644120641 / 62500000000 : ℝ) < 1 + Real.sqrt 2
      have h11 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h12 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_208 :
    values13 (208 : Fin 264) < values13 (209 : Fin 264) := by
  have hleft : values13 (208 : Fin 264) < (2661 / 1000 : ℝ) := by
    rw [show values13 (208 : Fin 264) = Real.sqrt 2 + values8 (6 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (6 : Fin 20) < (2661 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (6 : Fin 20) < (124651 / 100000 : ℝ) := by
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (6 : Fin 13)) < (124651 / 100000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (124651 / 100000 : ℝ))]
      norm_num
      change values7 (6 : Fin 13) < (15537871801 / 10000000000 : ℝ)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (15537871801 / 10000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (15537871801 / 10000000000 : ℝ))]
      norm_num
      change values6 (6 : Fin 8) < (241425460104310983601 / 100000000000000000000 : ℝ)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (241425460104310983601 / 100000000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
        change Real.sqrt (2) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (2661 / 1000 : ℝ) < values13 (209 : Fin 264) := by
    rw [show values13 (209 : Fin 264) = 1 + values11 (45 : Fin 91) by rfl]
    change (2661 / 1000 : ℝ) < 1 + values11 (45 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1681 / 1000 : ℝ) < values11 (45 : Fin 91) := by
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by a158415_twelve_table]
      change (1681 / 1000 : ℝ) < Real.sqrt (values10 (45 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2825761 / 1000000 : ℝ) < values10 (45 : Fin 54)
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by a158415_twelve_table]
      change (2825761 / 1000000 : ℝ) < Real.sqrt 2 + values5 (2 : Fin 5)
      have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h8 : (707 / 500 : ℝ) < values5 (2 : Fin 5) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_209 :
    values13 (209 : Fin 264) < values13 (210 : Fin 264) := by
  have hleft : values13 (209 : Fin 264) < (1341 / 500 : ℝ) := by
    rw [show values13 (209 : Fin 264) = 1 + values11 (45 : Fin 91) by rfl]
    change 1 + values11 (45 : Fin 91) < (1341 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (45 : Fin 91) < (8409 / 5000 : ℝ) := by
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (45 : Fin 54)) < (8409 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (8409 / 5000 : ℝ))]
      norm_num
      change values10 (45 : Fin 54) < (70711281 / 25000000 : ℝ)
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by a158415_twelve_table]
      change Real.sqrt 2 + values5 (2 : Fin 5) < (70711281 / 25000000 : ℝ)
      have h3 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
        change Real.sqrt (2) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
      have h4 : values5 (2 : Fin 5) < (70711 / 50000 : ℝ) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (70711 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (1341 / 500 : ℝ) < values13 (210 : Fin 264) := by
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    change (1341 / 500 : ℝ) < Real.sqrt 2 + values8 (7 : Fin 20)
    have h5 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (329 / 250 : ℝ) < values8 (7 : Fin 20) := by
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change (329 / 250 : ℝ) < Real.sqrt (values7 (7 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : ℝ) < values7 (7 : Fin 13)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (108241 / 62500 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : ℝ) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (11716114081 / 3906250000 : ℝ) < 1 + 2
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (19999 / 10000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_210 :
    values13 (210 : Fin 264) < values13 (211 : Fin 264) := by
  have hleft : values13 (210 : Fin 264) < (2731 / 1000 : ℝ) := by
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (7 : Fin 20) < (2731 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (7 : Fin 20) < (13161 / 10000 : ℝ) := by
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (7 : Fin 13)) < (13161 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (13161 / 10000 : ℝ))]
      norm_num
      change values7 (7 : Fin 13) < (173211921 / 100000000 : ℝ)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (173211921 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (173211921 / 100000000 : ℝ))]
      norm_num
      change values6 (7 : Fin 8) < (30002369576510241 / 10000000000000000 : ℝ)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30002369576510241 / 10000000000000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (2731 / 1000 : ℝ) < values13 (211 : Fin 264) := by
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    change (2731 / 1000 : ℝ) < 1 + values11 (46 : Fin 91)
    have h5 : (9999 / 10000 : ℝ) < 1 := by
      norm_num
    have h6 : (433 / 250 : ℝ) < values11 (46 : Fin 91) := by
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values10 (46 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values10 (46 : Fin 54)
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + values8 (12 : Fin 20)
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (199999 / 100000 : ℝ) < values8 (12 : Fin 20) := by
        rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
        change (199999 / 100000 : ℝ) < Real.sqrt (values7 (12 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (39999600001 / 10000000000 : ℝ) < values7 (12 : Fin 13)
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change (39999600001 / 10000000000 : ℝ) < 1 + values5 (4 : Fin 5)
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
theorem values13_special_211 :
    values13 (211 : Fin 264) < values13 (212 : Fin 264) := by
  have hleft : values13 (211 : Fin 264) < (2733 / 1000 : ℝ) := by
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    change 1 + values11 (46 : Fin 91) < (2733 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (46 : Fin 91) < (17321 / 10000 : ℝ) := by
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (46 : Fin 54)) < (17321 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17321 / 10000 : ℝ))]
      norm_num
      change values10 (46 : Fin 54) < (300017041 / 100000000 : ℝ)
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (12 : Fin 20) < (300017041 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (12 : Fin 20) < (200001 / 100000 : ℝ) := by
        rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (12 : Fin 13)) < (200001 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (200001 / 100000 : ℝ))]
        norm_num
        change values7 (12 : Fin 13) < (40000400001 / 10000000000 : ℝ)
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (4 : Fin 5) < (40000400001 / 10000000000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values5 (4 : Fin 5) < (300001 / 100000 : ℝ) := by
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (300001 / 100000 : ℝ)
          have h7 : 1 < (1000001 / 1000000 : ℝ) := by
            norm_num
          have h8 : 2 < (2000001 / 1000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2733 / 1000 : ℝ) < values13 (212 : Fin 264) := by
    rw [show values13 (212 : Fin 264) = values5 (1 : Fin 5) + values7 (6 : Fin 13) by rfl]
    change (2733 / 1000 : ℝ) < values5 (1 : Fin 5) + values7 (6 : Fin 13)
    have h9 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1553 / 1000 : ℝ) < values7 (6 : Fin 13) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (1553 / 1000 : ℝ) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : ℝ) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (2411809 / 1000000 : ℝ) < 1 + Real.sqrt 2
      have h11 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h12 : (707 / 500 : ℝ) < Real.sqrt 2 := by
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_212 :
    values13 (212 : Fin 264) < values13 (213 : Fin 264) := by
  have hleft : values13 (212 : Fin 264) < (2743 / 1000 : ℝ) := by
    rw [show values13 (212 : Fin 264) = values5 (1 : Fin 5) + values7 (6 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (6 : Fin 13) < (2743 / 1000 : ℝ)
    have h1 : values5 (1 : Fin 5) < (118921 / 100000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118921 / 100000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (14142204241 / 10000000000 : ℝ)
      change Real.sqrt (2) < (14142204241 / 10000000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142204241 / 10000000000 : ℝ))]
      norm_num
    have h2 : values7 (6 : Fin 13) < (77689 / 50000 : ℝ) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (77689 / 50000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (77689 / 50000 : ℝ))]
      norm_num
      change values6 (6 : Fin 8) < (6035580721 / 2500000000 : ℝ)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (6035580721 / 2500000000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : Real.sqrt 2 < (707107 / 500000 : ℝ) := by
        change Real.sqrt (2) < (707107 / 500000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (2743 / 1000 : ℝ) < values13 (213 : Fin 264) := by
    rw [show values13 (213 : Fin 264) = 1 + values11 (47 : Fin 91) by rfl]
    change (2743 / 1000 : ℝ) < 1 + values11 (47 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1757 / 1000 : ℝ) < values11 (47 : Fin 91) := by
      rw [show values11 (47 : Fin 91) = Real.sqrt (values10 (47 : Fin 54)) by a158415_twelve_table]
      change (1757 / 1000 : ℝ) < Real.sqrt (values10 (47 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3087049 / 1000000 : ℝ) < values10 (47 : Fin 54)
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by a158415_twelve_table]
      change (3087049 / 1000000 : ℝ) < 1 + values8 (13 : Fin 20)
      have h7 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h8 : (209 / 100 : ℝ) < values8 (13 : Fin 20) := by
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change (209 / 100 : ℝ) < 1 + values6 (1 : Fin 8)
        have h9 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h10 : (2181 / 2000 : ℝ) < values6 (1 : Fin 8) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change (2181 / 2000 : ℝ) < Real.sqrt (values5 (1 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (4756761 / 4000000 : ℝ) < values5 (1 : Fin 5)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (4756761 / 4000000 : ℝ) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (22626775211121 / 16000000000000 : ℝ) < Real.sqrt 2
          change (22626775211121 / 16000000000000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_214 :
    values13 (214 : Fin 264) < values13 (215 : Fin 264) := by
  have hleft : values13 (214 : Fin 264) < (1393 / 500 : ℝ) := by
    rw [show values13 (214 : Fin 264) = 1 + values11 (48 : Fin 91) by rfl]
    change 1 + values11 (48 : Fin 91) < (1393 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (48 : Fin 91) < (22323 / 12500 : ℝ) := by
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (48 : Fin 54)) < (22323 / 12500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22323 / 12500 : ℝ))]
      norm_num
      change values10 (48 : Fin 54) < (498316329 / 156250000 : ℝ)
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (14 : Fin 20) < (498316329 / 156250000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values8 (14 : Fin 20) < (218921 / 100000 : ℝ) := by
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (2 : Fin 8) < (218921 / 100000 : ℝ)
        have h5 : 1 < (10000001 / 10000000 : ℝ) := by
          norm_num
        have h6 : values6 (2 : Fin 8) < (148651 / 125000 : ℝ) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (2 : Fin 5)) < (148651 / 125000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (148651 / 125000 : ℝ))]
          norm_num
          change values5 (2 : Fin 5) < (22097119801 / 15625000000 : ℝ)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (22097119801 / 15625000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (22097119801 / 15625000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1393 / 500 : ℝ) < values13 (215 : Fin 264) := by
    rw [show values13 (215 : Fin 264) = values6 (1 : Fin 8) + values6 (4 : Fin 8) by rfl]
    change (1393 / 500 : ℝ) < values6 (1 : Fin 8) + values6 (4 : Fin 8)
    have h7 : (109 / 100 : ℝ) < values6 (1 : Fin 8) := by
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
theorem values13_special_215 :
    values13 (215 : Fin 264) < values13 (216 : Fin 264) := by
  have hleft : values13 (215 : Fin 264) < (2823 / 1000 : ℝ) := by
    rw [show values13 (215 : Fin 264) = values6 (1 : Fin 8) + values6 (4 : Fin 8) by rfl]
    change values6 (1 : Fin 8) + values6 (4 : Fin 8) < (2823 / 1000 : ℝ)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : ℝ) := by
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
  have hright : (2823 / 1000 : ℝ) < values13 (216 : Fin 264) := by
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    change (2823 / 1000 : ℝ) < Real.sqrt 2 + values8 (8 : Fin 20)
    have h5 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (707 / 500 : ℝ) < values8 (8 : Fin 20) := by
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change (707 / 500 : ℝ) < Real.sqrt (values7 (8 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : ℝ) < values7 (8 : Fin 13)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change (499849 / 250000 : ℝ) < 1 + values5 (0 : Fin 5)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (9999 / 10000 : ℝ) < values5 (0 : Fin 5) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change (9999 / 10000 : ℝ) < Real.sqrt (1)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_216 :
    values13 (216 : Fin 264) < values13 (217 : Fin 264) := by
  have hleft : values13 (216 : Fin 264) < (2829 / 1000 : ℝ) := by
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (8 : Fin 20) < (2829 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (8 : Fin 20) < (14143 / 10000 : ℝ) := by
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (8 : Fin 13)) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
      change values7 (8 : Fin 13) < (200024449 / 100000000 : ℝ)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (0 : Fin 5) < (200024449 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values5 (0 : Fin 5) < (100001 / 100000 : ℝ) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change Real.sqrt (1) < (100001 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (100001 / 100000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (2829 / 1000 : ℝ) < values13 (217 : Fin 264) := by
    rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
    change (2829 / 1000 : ℝ) < 1 + values11 (49 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1847 / 1000 : ℝ) < values11 (49 : Fin 91) := by
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by a158415_twelve_table]
      change (1847 / 1000 : ℝ) < Real.sqrt (values10 (49 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3411409 / 1000000 : ℝ) < values10 (49 : Fin 54)
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change (3411409 / 1000000 : ℝ) < 1 + values8 (15 : Fin 20)
      have h7 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h8 : (1207 / 500 : ℝ) < values8 (15 : Fin 20) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change (1207 / 500 : ℝ) < 1 + values6 (3 : Fin 8)
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (7071 / 5000 : ℝ) < values6 (3 : Fin 8) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (7071 / 5000 : ℝ) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (49999041 / 25000000 : ℝ) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (49999041 / 25000000 : ℝ) < 1 + 1
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
theorem values13_special_217 :
    values13 (217 : Fin 264) < values13 (218 : Fin 264) := by
  have hleft : values13 (217 : Fin 264) < (356 / 125 : ℝ) := by
    rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
    change 1 + values11 (49 : Fin 91) < (356 / 125 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (49 : Fin 91) < (9239 / 5000 : ℝ) := by
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (49 : Fin 54)) < (9239 / 5000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (9239 / 5000 : ℝ))]
      norm_num
      change values10 (49 : Fin 54) < (85359121 / 25000000 : ℝ)
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (15 : Fin 20) < (85359121 / 25000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (15 : Fin 20) < (120711 / 50000 : ℝ) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (3 : Fin 8) < (120711 / 50000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values6 (3 : Fin 8) < (707107 / 500000 : ℝ) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (707107 / 500000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
          norm_num
          change values5 (3 : Fin 5) < (500000309449 / 250000000000 : ℝ)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (500000309449 / 250000000000 : ℝ)
          have h7 : 1 < (10000001 / 10000000 : ℝ) := by
            norm_num
          have h8 : 1 < (10000001 / 10000000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (356 / 125 : ℝ) < values13 (218 : Fin 264) := by
    rw [show values13 (218 : Fin 264) = Real.sqrt 2 + values8 (9 : Fin 20) by rfl]
    change (356 / 125 : ℝ) < Real.sqrt 2 + values8 (9 : Fin 20)
    have h9 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1479 / 1000 : ℝ) < values8 (9 : Fin 20) := by
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (1479 / 1000 : ℝ) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2187441 / 1000000 : ℝ) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (2187441 / 1000000 : ℝ) < 1 + values5 (1 : Fin 5)
      have h11 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h12 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
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
theorem values13_special_218 :
    values13 (218 : Fin 264) < values13 (219 : Fin 264) := by
  have hleft : values13 (218 : Fin 264) < (1447 / 500 : ℝ) := by
    rw [show values13 (218 : Fin 264) = Real.sqrt 2 + values8 (9 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (9 : Fin 20) < (1447 / 500 : ℝ)
    have h1 : Real.sqrt 2 < (70711 / 50000 : ℝ) := by
      change Real.sqrt (2) < (70711 / 50000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (70711 / 50000 : ℝ))]
      norm_num
    have h2 : values8 (9 : Fin 20) < (3699 / 2500 : ℝ) := by
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (9 : Fin 13)) < (3699 / 2500 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (3699 / 2500 : ℝ))]
      norm_num
      change values7 (9 : Fin 13) < (13682601 / 6250000 : ℝ)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (1 : Fin 5) < (13682601 / 6250000 : ℝ)
      have h3 : 1 < (1000001 / 1000000 : ℝ) := by
        norm_num
      have h4 : values5 (1 : Fin 5) < (118921 / 100000 : ℝ) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (118921 / 100000 : ℝ))]
        norm_num
        change Real.sqrt 2 < (14142204241 / 10000000000 : ℝ)
        change Real.sqrt (2) < (14142204241 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14142204241 / 10000000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (1447 / 500 : ℝ) < values13 (219 : Fin 264) := by
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    change (1447 / 500 : ℝ) < values5 (1 : Fin 5) + values7 (7 : Fin 13)
    have h5 : (1189 / 1000 : ℝ) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : ℝ) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : ℝ) < Real.sqrt 2
      change (1413721 / 1000000 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (433 / 250 : ℝ) < values7 (7 : Fin 13) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + 2
      have h7 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h8 : (199999 / 100000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_219 :
    values13 (219 : Fin 264) < values13 (220 : Fin 264) := by
  have hleft : values13 (219 : Fin 264) < (1461 / 500 : ℝ) := by
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    change values5 (1 : Fin 5) + values7 (7 : Fin 13) < (1461 / 500 : ℝ)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : ℝ) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (11893 / 10000 : ℝ))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : ℝ)
      change Real.sqrt (2) < (141443449 / 100000000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141443449 / 100000000 : ℝ))]
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
  have hright : (1461 / 500 : ℝ) < values13 (220 : Fin 264) := by
    rw [show values13 (220 : Fin 264) = 1 + values11 (50 : Fin 91) by rfl]
    change (1461 / 500 : ℝ) < 1 + values11 (50 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1931 / 1000 : ℝ) < values11 (50 : Fin 91) := by
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by a158415_twelve_table]
      change (1931 / 1000 : ℝ) < Real.sqrt (values10 (50 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3728761 / 1000000 : ℝ) < values10 (50 : Fin 54)
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change (3728761 / 1000000 : ℝ) < 1 + values8 (16 : Fin 20)
      have h7 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h8 : (683 / 250 : ℝ) < values8 (16 : Fin 20) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change (683 / 250 : ℝ) < 1 + values6 (4 : Fin 8)
        have h9 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h10 : (34641 / 20000 : ℝ) < values6 (4 : Fin 8) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change (34641 / 20000 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1199998881 / 400000000 : ℝ) < values5 (4 : Fin 5)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change (1199998881 / 400000000 : ℝ) < 1 + 2
          have h11 : (9999999 / 10000000 : ℝ) < 1 := by
            norm_num
          have h12 : (19999999 / 10000000 : ℝ) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_220 :
    values13 (220 : Fin 264) < values13 (221 : Fin 264) := by
  have hleft : values13 (220 : Fin 264) < (733 / 250 : ℝ) := by
    rw [show values13 (220 : Fin 264) = 1 + values11 (50 : Fin 91) by rfl]
    change 1 + values11 (50 : Fin 91) < (733 / 250 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (50 : Fin 91) < (19319 / 10000 : ℝ) := by
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (50 : Fin 54)) < (19319 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (19319 / 10000 : ℝ))]
      norm_num
      change values10 (50 : Fin 54) < (373223761 / 100000000 : ℝ)
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (16 : Fin 20) < (373223761 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values8 (16 : Fin 20) < (27321 / 10000 : ℝ) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (4 : Fin 8) < (27321 / 10000 : ℝ)
        have h5 : 1 < (100001 / 100000 : ℝ) := by
          norm_num
        have h6 : values6 (4 : Fin 8) < (86603 / 50000 : ℝ) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (86603 / 50000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (86603 / 50000 : ℝ))]
          norm_num
          change values5 (4 : Fin 5) < (7500079609 / 2500000000 : ℝ)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (7500079609 / 2500000000 : ℝ)
          have h7 : 1 < (100001 / 100000 : ℝ) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : ℝ) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (733 / 250 : ℝ) < values13 (221 : Fin 264) := by
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    change (733 / 250 : ℝ) < Real.sqrt 2 + values8 (10 : Fin 20)
    have h9 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1553 / 1000 : ℝ) < values8 (10 : Fin 20) := by
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change (1553 / 1000 : ℝ) < Real.sqrt (values7 (10 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : ℝ) < values7 (10 : Fin 13)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change (2411809 / 1000000 : ℝ) < 1 + values5 (2 : Fin 5)
      have h11 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h12 : (707 / 500 : ℝ) < values5 (2 : Fin 5) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (707 / 500 : ℝ) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_221 :
    values13 (221 : Fin 264) < values13 (222 : Fin 264) := by
  have hleft : values13 (221 : Fin 264) < (371 / 125 : ℝ) := by
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (10 : Fin 20) < (371 / 125 : ℝ)
    have h1 : Real.sqrt 2 < (707107 / 500000 : ℝ) := by
      change Real.sqrt (2) < (707107 / 500000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
      norm_num
    have h2 : values8 (10 : Fin 20) < (776887 / 500000 : ℝ) := by
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (10 : Fin 13)) < (776887 / 500000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (776887 / 500000 : ℝ))]
      norm_num
      change values7 (10 : Fin 13) < (603553410769 / 250000000000 : ℝ)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (2 : Fin 5) < (603553410769 / 250000000000 : ℝ)
      have h3 : 1 < (100000001 / 100000000 : ℝ) := by
        norm_num
      have h4 : values5 (2 : Fin 5) < (141421357 / 100000000 : ℝ) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (141421357 / 100000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (141421357 / 100000000 : ℝ))]
        norm_num
      linarith
    linarith
  have hright : (371 / 125 : ℝ) < values13 (222 : Fin 264) := by
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    change (371 / 125 : ℝ) < 1 + values11 (51 : Fin 91)
    have h5 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h6 : (1999 / 1000 : ℝ) < values11 (51 : Fin 91) := by
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by a158415_twelve_table]
      change (1999 / 1000 : ℝ) < Real.sqrt (values10 (51 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3996001 / 1000000 : ℝ) < values10 (51 : Fin 54)
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by a158415_twelve_table]
      change (3996001 / 1000000 : ℝ) < 1 + values8 (17 : Fin 20)
      have h7 : (999 / 1000 : ℝ) < 1 := by
        norm_num
      have h8 : (2999 / 1000 : ℝ) < values8 (17 : Fin 20) := by
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change (2999 / 1000 : ℝ) < 1 + values6 (5 : Fin 8)
        have h9 : (9999 / 10000 : ℝ) < 1 := by
          norm_num
        have h10 : (19999 / 10000 : ℝ) < values6 (5 : Fin 8) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
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
theorem values13_special_229 :
    values13 (229 : Fin 264) < values13 (230 : Fin 264) := by
  have hleft : values13 (229 : Fin 264) < (3117 / 1000 : ℝ) := by
    rw [show values13 (229 : Fin 264) = 1 + values11 (58 : Fin 91) by rfl]
    change 1 + values11 (58 : Fin 91) < (3117 / 1000 : ℝ)
    have h1 : 1 < (10001 / 10000 : ℝ) := by
      norm_num
    have h2 : values11 (58 : Fin 91) < (4233 / 2000 : ℝ) := by
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (6 : Fin 33) < (4233 / 2000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values9 (6 : Fin 33) < (111647 / 100000 : ℝ) := by
        rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (6 : Fin 20)) < (111647 / 100000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (111647 / 100000 : ℝ))]
        norm_num
        change values8 (6 : Fin 20) < (12465052609 / 10000000000 : ℝ)
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (6 : Fin 13)) < (12465052609 / 10000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (12465052609 / 10000000000 : ℝ))]
        norm_num
        change values7 (6 : Fin 13) < (155377536545137706881 / 100000000000000000000 : ℝ)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (155377536545137706881 / 100000000000000000000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (155377536545137706881 / 100000000000000000000 : ℝ))]
        norm_num
        change values6 (6 : Fin 8) < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : ℝ)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : Real.sqrt 2 < (707107 / 500000 : ℝ) := by
          change Real.sqrt (2) < (707107 / 500000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (707107 / 500000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (3117 / 1000 : ℝ) < values13 (230 : Fin 264) := by
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    change (3117 / 1000 : ℝ) < Real.sqrt 2 + values8 (11 : Fin 20)
    have h7 : (707 / 500 : ℝ) < Real.sqrt 2 := by
      change (707 / 500 : ℝ) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (433 / 250 : ℝ) < values8 (11 : Fin 20) := by
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values7 (11 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values7 (11 : Fin 13)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + values5 (3 : Fin 5)
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

set_option linter.unusedTactic false in
theorem values13_special_230 :
    values13 (230 : Fin 264) < values13 (231 : Fin 264) := by
  have hleft : values13 (230 : Fin 264) < (3147 / 1000 : ℝ) := by
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    change Real.sqrt 2 + values8 (11 : Fin 20) < (3147 / 1000 : ℝ)
    have h1 : Real.sqrt 2 < (14143 / 10000 : ℝ) := by
      change Real.sqrt (2) < (14143 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (14143 / 10000 : ℝ))]
      norm_num
    have h2 : values8 (11 : Fin 20) < (17321 / 10000 : ℝ) := by
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (11 : Fin 13)) < (17321 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17321 / 10000 : ℝ))]
      norm_num
      change values7 (11 : Fin 13) < (300017041 / 100000000 : ℝ)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (3 : Fin 5) < (300017041 / 100000000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values5 (3 : Fin 5) < (200001 / 100000 : ℝ) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001 / 100000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (3147 / 1000 : ℝ) < values13 (231 : Fin 264) := by
    rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
    change (3147 / 1000 : ℝ) < 1 + values11 (59 : Fin 91)
    have h7 : (99999 / 100000 : ℝ) < 1 := by
      norm_num
    have h8 : (1342 / 625 : ℝ) < values11 (59 : Fin 91) := by
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by a158415_twelve_table]
      change (1342 / 625 : ℝ) < 1 + values9 (7 : Fin 33)
      have h9 : (9999999 / 10000000 : ℝ) < 1 := by
        norm_num
      have h10 : (573601 / 500000 : ℝ) < values9 (7 : Fin 33) := by
        rw [show values9 (7 : Fin 33) = Real.sqrt (values8 (7 : Fin 20)) by a158415_twelve_table]
        change (573601 / 500000 : ℝ) < Real.sqrt (values8 (7 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (329018107201 / 250000000000 : ℝ) < values8 (7 : Fin 20)
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change (329018107201 / 250000000000 : ℝ) < Real.sqrt (values7 (7 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108252914866128728054401 / 62500000000000000000000 : ℝ) < values7 (7 : Fin 13)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (108252914866128728054401 / 62500000000000000000000 : ℝ) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : ℝ) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : ℝ) < 1 + 2
        have h11 : (999999 / 1000000 : ℝ) < 1 := by
          norm_num
        have h12 : (1999999 / 1000000 : ℝ) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_239 :
    values13 (239 : Fin 264) < values13 (240 : Fin 264) := by
  have hleft : values13 (239 : Fin 264) < (1723 / 500 : ℝ) := by
    rw [show values13 (239 : Fin 264) = 1 + values11 (67 : Fin 91) by rfl]
    change 1 + values11 (67 : Fin 91) < (1723 / 500 : ℝ)
    have h1 : 1 < (100001 / 100000 : ℝ) := by
      norm_num
    have h2 : values11 (67 : Fin 91) < (24459 / 10000 : ℝ) := by
      rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (13 : Fin 33) < (24459 / 10000 : ℝ)
      have h3 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h4 : values9 (13 : Fin 33) < (72293 / 50000 : ℝ) := by
        rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (13 : Fin 20)) < (72293 / 50000 : ℝ)
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (72293 / 50000 : ℝ))]
        norm_num
        change values8 (13 : Fin 20) < (5226277849 / 2500000000 : ℝ)
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (1 : Fin 8) < (5226277849 / 2500000000 : ℝ)
        have h5 : 1 < (1000001 / 1000000 : ℝ) := by
          norm_num
        have h6 : values6 (1 : Fin 8) < (272627 / 250000 : ℝ) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (1 : Fin 5)) < (272627 / 250000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (272627 / 250000 : ℝ))]
          norm_num
          change values5 (1 : Fin 5) < (74325481129 / 62500000000 : ℝ)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (74325481129 / 62500000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (74325481129 / 62500000000 : ℝ))]
          norm_num
          change Real.sqrt 2 < (5524277145057335114641 / 3906250000000000000000 : ℝ)
          change Real.sqrt (2) < (5524277145057335114641 / 3906250000000000000000 : ℝ)
          rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (5524277145057335114641 / 3906250000000000000000 : ℝ))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1723 / 500 : ℝ) < values13 (240 : Fin 264) := by
    rw [show values13 (240 : Fin 264) = values6 (4 : Fin 8) + values6 (4 : Fin 8) by rfl]
    change (1723 / 500 : ℝ) < values6 (4 : Fin 8) + values6 (4 : Fin 8)
    have h7 : (433 / 250 : ℝ) < values6 (4 : Fin 8) := by
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
    have h8 : (433 / 250 : ℝ) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (433 / 250 : ℝ) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : ℝ) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : ℝ) < 1 + 2
      have h11 : (99999 / 100000 : ℝ) < 1 := by
        norm_num
      have h12 : (199999 / 100000 : ℝ) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values13_special_240 :
    values13 (240 : Fin 264) < values13 (241 : Fin 264) := by
  have hleft : values13 (240 : Fin 264) < (693 / 200 : ℝ) := by
    rw [show values13 (240 : Fin 264) = values6 (4 : Fin 8) + values6 (4 : Fin 8) by rfl]
    change values6 (4 : Fin 8) + values6 (4 : Fin 8) < (693 / 200 : ℝ)
    have h1 : values6 (4 : Fin 8) < (17321 / 10000 : ℝ) := by
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
    have h2 : values6 (4 : Fin 8) < (17321 / 10000 : ℝ) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : ℝ)
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < (17321 / 10000 : ℝ))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : ℝ)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : ℝ)
      have h5 : 1 < (100001 / 100000 : ℝ) := by
        norm_num
      have h6 : 2 < (200001 / 100000 : ℝ) := by
        norm_num
      linarith
    linarith
  have hright : (693 / 200 : ℝ) < values13 (241 : Fin 264) := by
    rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
    change (693 / 200 : ℝ) < 1 + values11 (68 : Fin 91)
    have h7 : (999 / 1000 : ℝ) < 1 := by
      norm_num
    have h8 : (2479 / 1000 : ℝ) < values11 (68 : Fin 91) := by
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by a158415_twelve_table]
      change (2479 / 1000 : ℝ) < 1 + values9 (14 : Fin 33)
      have h9 : (9999 / 10000 : ℝ) < 1 := by
        norm_num
      have h10 : (2959 / 2000 : ℝ) < values9 (14 : Fin 33) := by
        rw [show values9 (14 : Fin 33) = Real.sqrt (values8 (14 : Fin 20)) by a158415_twelve_table]
        change (2959 / 2000 : ℝ) < Real.sqrt (values8 (14 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (8755681 / 4000000 : ℝ) < values8 (14 : Fin 20)
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change (8755681 / 4000000 : ℝ) < 1 + values6 (2 : Fin 8)
        have h11 : (99999 / 100000 : ℝ) < 1 := by
          norm_num
        have h12 : (2973 / 2500 : ℝ) < values6 (2 : Fin 8) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change (2973 / 2500 : ℝ) < Real.sqrt (values5 (2 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (8838729 / 6250000 : ℝ) < values5 (2 : Fin 5)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (8838729 / 6250000 : ℝ) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option maxHeartbeats 2000000 in
theorem values13_strictMono : StrictMono values13 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact sqrt_values12_strictMono (by decide)
  · exact values13_special_146
  · change 1 + values11 (1 : Fin 91) < 1 + values11 (2 : Fin 91)
    linarith [values11_strictMono (by native_decide : (1 : Fin 91) < 2)]
  · change 1 + values11 (2 : Fin 91) < 1 + values11 (3 : Fin 91)
    linarith [values11_strictMono (by native_decide : (2 : Fin 91) < 3)]
  · change 1 + values11 (3 : Fin 91) < 1 + values11 (4 : Fin 91)
    linarith [values11_strictMono (by native_decide : (3 : Fin 91) < 4)]
  · change 1 + values11 (4 : Fin 91) < 1 + values11 (5 : Fin 91)
    linarith [values11_strictMono (by native_decide : (4 : Fin 91) < 5)]
  · exact values13_special_151
  · exact values13_special_152
  · change 1 + values11 (6 : Fin 91) < 1 + values11 (7 : Fin 91)
    linarith [values11_strictMono (by native_decide : (6 : Fin 91) < 7)]
  · change 1 + values11 (7 : Fin 91) < 1 + values11 (8 : Fin 91)
    linarith [values11_strictMono (by native_decide : (7 : Fin 91) < 8)]
  · exact values13_special_155
  · exact values13_special_156
  · change 1 + values11 (9 : Fin 91) < 1 + values11 (10 : Fin 91)
    linarith [values11_strictMono (by native_decide : (9 : Fin 91) < 10)]
  · change 1 + values11 (10 : Fin 91) < 1 + values11 (11 : Fin 91)
    linarith [values11_strictMono (by native_decide : (10 : Fin 91) < 11)]
  · change 1 + values11 (11 : Fin 91) < 1 + values11 (12 : Fin 91)
    linarith [values11_strictMono (by native_decide : (11 : Fin 91) < 12)]
  · change 1 + values11 (12 : Fin 91) < 1 + values11 (13 : Fin 91)
    linarith [values11_strictMono (by native_decide : (12 : Fin 91) < 13)]
  · exact values13_special_161
  · exact values13_special_162
  · change 1 + values11 (14 : Fin 91) < 1 + values11 (15 : Fin 91)
    linarith [values11_strictMono (by native_decide : (14 : Fin 91) < 15)]
  · change 1 + values11 (15 : Fin 91) < 1 + values11 (16 : Fin 91)
    linarith [values11_strictMono (by native_decide : (15 : Fin 91) < 16)]
  · change 1 + values11 (16 : Fin 91) < 1 + values11 (17 : Fin 91)
    linarith [values11_strictMono (by native_decide : (16 : Fin 91) < 17)]
  · change 1 + values11 (17 : Fin 91) < 1 + values11 (18 : Fin 91)
    linarith [values11_strictMono (by native_decide : (17 : Fin 91) < 18)]
  · exact values13_special_167
  · exact values13_special_168
  · exact values13_special_169
  · change 1 + values11 (19 : Fin 91) < 1 + values11 (20 : Fin 91)
    linarith [values11_strictMono (by native_decide : (19 : Fin 91) < 20)]
  · change 1 + values11 (20 : Fin 91) < 1 + values11 (21 : Fin 91)
    linarith [values11_strictMono (by native_decide : (20 : Fin 91) < 21)]
  · change 1 + values11 (21 : Fin 91) < 1 + values11 (22 : Fin 91)
    linarith [values11_strictMono (by native_decide : (21 : Fin 91) < 22)]
  · exact values13_special_173
  · exact values13_special_174
  · exact values13_special_175
  · exact values13_special_176
  · change 1 + values11 (24 : Fin 91) < 1 + values11 (25 : Fin 91)
    linarith [values11_strictMono (by native_decide : (24 : Fin 91) < 25)]
  · exact values13_special_178
  · exact values13_special_179
  · change 1 + values11 (26 : Fin 91) < 1 + values11 (27 : Fin 91)
    linarith [values11_strictMono (by native_decide : (26 : Fin 91) < 27)]
  · change 1 + values11 (27 : Fin 91) < 1 + values11 (28 : Fin 91)
    linarith [values11_strictMono (by native_decide : (27 : Fin 91) < 28)]
  · exact values13_special_182
  · exact values13_special_183
  · change 1 + values11 (29 : Fin 91) < 1 + values11 (30 : Fin 91)
    linarith [values11_strictMono (by native_decide : (29 : Fin 91) < 30)]
  · exact values13_special_185
  · exact values13_special_186
  · change 1 + values11 (31 : Fin 91) < 1 + values11 (32 : Fin 91)
    linarith [values11_strictMono (by native_decide : (31 : Fin 91) < 32)]
  · change 1 + values11 (32 : Fin 91) < 1 + values11 (33 : Fin 91)
    linarith [values11_strictMono (by native_decide : (32 : Fin 91) < 33)]
  · exact values13_special_189
  · exact values13_special_190
  · exact values13_special_191
  · exact values13_special_192
  · exact values13_special_193
  · change 1 + values11 (35 : Fin 91) < 1 + values11 (36 : Fin 91)
    linarith [values11_strictMono (by native_decide : (35 : Fin 91) < 36)]
  · change 1 + values11 (36 : Fin 91) < 1 + values11 (37 : Fin 91)
    linarith [values11_strictMono (by native_decide : (36 : Fin 91) < 37)]
  · change 1 + values11 (37 : Fin 91) < 1 + values11 (38 : Fin 91)
    linarith [values11_strictMono (by native_decide : (37 : Fin 91) < 38)]
  · exact values13_special_197
  · exact values13_special_198
  · exact values13_special_199
  · change 1 + values11 (39 : Fin 91) < 1 + values11 (40 : Fin 91)
    linarith [values11_strictMono (by native_decide : (39 : Fin 91) < 40)]
  · exact values13_special_201
  · exact values13_special_202
  · change 1 + values11 (41 : Fin 91) < 1 + values11 (42 : Fin 91)
    linarith [values11_strictMono (by native_decide : (41 : Fin 91) < 42)]
  · exact values13_special_204
  · exact values13_special_205
  · change 1 + values11 (43 : Fin 91) < 1 + values11 (44 : Fin 91)
    linarith [values11_strictMono (by native_decide : (43 : Fin 91) < 44)]
  · exact values13_special_207
  · exact values13_special_208
  · exact values13_special_209
  · exact values13_special_210
  · exact values13_special_211
  · exact values13_special_212
  · change 1 + values11 (47 : Fin 91) < 1 + values11 (48 : Fin 91)
    linarith [values11_strictMono (by native_decide : (47 : Fin 91) < 48)]
  · exact values13_special_214
  · exact values13_special_215
  · exact values13_special_216
  · exact values13_special_217
  · exact values13_special_218
  · exact values13_special_219
  · exact values13_special_220
  · exact values13_special_221
  · change 1 + values11 (51 : Fin 91) < 1 + values11 (52 : Fin 91)
    linarith [values11_strictMono (by native_decide : (51 : Fin 91) < 52)]
  · change 1 + values11 (52 : Fin 91) < 1 + values11 (53 : Fin 91)
    linarith [values11_strictMono (by native_decide : (52 : Fin 91) < 53)]
  · change 1 + values11 (53 : Fin 91) < 1 + values11 (54 : Fin 91)
    linarith [values11_strictMono (by native_decide : (53 : Fin 91) < 54)]
  · change 1 + values11 (54 : Fin 91) < 1 + values11 (55 : Fin 91)
    linarith [values11_strictMono (by native_decide : (54 : Fin 91) < 55)]
  · change 1 + values11 (55 : Fin 91) < 1 + values11 (56 : Fin 91)
    linarith [values11_strictMono (by native_decide : (55 : Fin 91) < 56)]
  · change 1 + values11 (56 : Fin 91) < 1 + values11 (57 : Fin 91)
    linarith [values11_strictMono (by native_decide : (56 : Fin 91) < 57)]
  · change 1 + values11 (57 : Fin 91) < 1 + values11 (58 : Fin 91)
    linarith [values11_strictMono (by native_decide : (57 : Fin 91) < 58)]
  · exact values13_special_229
  · exact values13_special_230
  · change 1 + values11 (59 : Fin 91) < 1 + values11 (60 : Fin 91)
    linarith [values11_strictMono (by native_decide : (59 : Fin 91) < 60)]
  · change 1 + values11 (60 : Fin 91) < 1 + values11 (61 : Fin 91)
    linarith [values11_strictMono (by native_decide : (60 : Fin 91) < 61)]
  · change 1 + values11 (61 : Fin 91) < 1 + values11 (62 : Fin 91)
    linarith [values11_strictMono (by native_decide : (61 : Fin 91) < 62)]
  · change 1 + values11 (62 : Fin 91) < 1 + values11 (63 : Fin 91)
    linarith [values11_strictMono (by native_decide : (62 : Fin 91) < 63)]
  · change 1 + values11 (63 : Fin 91) < 1 + values11 (64 : Fin 91)
    linarith [values11_strictMono (by native_decide : (63 : Fin 91) < 64)]
  · change 1 + values11 (64 : Fin 91) < 1 + values11 (65 : Fin 91)
    linarith [values11_strictMono (by native_decide : (64 : Fin 91) < 65)]
  · change 1 + values11 (65 : Fin 91) < 1 + values11 (66 : Fin 91)
    linarith [values11_strictMono (by native_decide : (65 : Fin 91) < 66)]
  · change 1 + values11 (66 : Fin 91) < 1 + values11 (67 : Fin 91)
    linarith [values11_strictMono (by native_decide : (66 : Fin 91) < 67)]
  · exact values13_special_239
  · exact values13_special_240
  · change 1 + values11 (68 : Fin 91) < 1 + values11 (69 : Fin 91)
    linarith [values11_strictMono (by native_decide : (68 : Fin 91) < 69)]
  · change 1 + values11 (69 : Fin 91) < 1 + values11 (70 : Fin 91)
    linarith [values11_strictMono (by native_decide : (69 : Fin 91) < 70)]
  · change 1 + values11 (70 : Fin 91) < 1 + values11 (71 : Fin 91)
    linarith [values11_strictMono (by native_decide : (70 : Fin 91) < 71)]
  · change 1 + values11 (71 : Fin 91) < 1 + values11 (72 : Fin 91)
    linarith [values11_strictMono (by native_decide : (71 : Fin 91) < 72)]
  · change 1 + values11 (72 : Fin 91) < 1 + values11 (73 : Fin 91)
    linarith [values11_strictMono (by native_decide : (72 : Fin 91) < 73)]
  · change 1 + values11 (73 : Fin 91) < 1 + values11 (74 : Fin 91)
    linarith [values11_strictMono (by native_decide : (73 : Fin 91) < 74)]
  · change 1 + values11 (74 : Fin 91) < 1 + values11 (75 : Fin 91)
    linarith [values11_strictMono (by native_decide : (74 : Fin 91) < 75)]
  · change 1 + values11 (75 : Fin 91) < 1 + values11 (76 : Fin 91)
    linarith [values11_strictMono (by native_decide : (75 : Fin 91) < 76)]
  · change 1 + values11 (76 : Fin 91) < 1 + values11 (77 : Fin 91)
    linarith [values11_strictMono (by native_decide : (76 : Fin 91) < 77)]
  · change 1 + values11 (77 : Fin 91) < 1 + values11 (78 : Fin 91)
    linarith [values11_strictMono (by native_decide : (77 : Fin 91) < 78)]
  · change 1 + values11 (78 : Fin 91) < 1 + values11 (79 : Fin 91)
    linarith [values11_strictMono (by native_decide : (78 : Fin 91) < 79)]
  · change 1 + values11 (79 : Fin 91) < 1 + values11 (80 : Fin 91)
    linarith [values11_strictMono (by native_decide : (79 : Fin 91) < 80)]
  · change 1 + values11 (80 : Fin 91) < 1 + values11 (81 : Fin 91)
    linarith [values11_strictMono (by native_decide : (80 : Fin 91) < 81)]
  · change 1 + values11 (81 : Fin 91) < 1 + values11 (82 : Fin 91)
    linarith [values11_strictMono (by native_decide : (81 : Fin 91) < 82)]
  · change 1 + values11 (82 : Fin 91) < 1 + values11 (83 : Fin 91)
    linarith [values11_strictMono (by native_decide : (82 : Fin 91) < 83)]
  · change 1 + values11 (83 : Fin 91) < 1 + values11 (84 : Fin 91)
    linarith [values11_strictMono (by native_decide : (83 : Fin 91) < 84)]
  · change 1 + values11 (84 : Fin 91) < 1 + values11 (85 : Fin 91)
    linarith [values11_strictMono (by native_decide : (84 : Fin 91) < 85)]
  · change 1 + values11 (85 : Fin 91) < 1 + values11 (86 : Fin 91)
    linarith [values11_strictMono (by native_decide : (85 : Fin 91) < 86)]
  · change 1 + values11 (86 : Fin 91) < 1 + values11 (87 : Fin 91)
    linarith [values11_strictMono (by native_decide : (86 : Fin 91) < 87)]
  · change 1 + values11 (87 : Fin 91) < 1 + values11 (88 : Fin 91)
    linarith [values11_strictMono (by native_decide : (87 : Fin 91) < 88)]
  · change 1 + values11 (88 : Fin 91) < 1 + values11 (89 : Fin 91)
    linarith [values11_strictMono (by native_decide : (88 : Fin 91) < 89)]
  · change 1 + values11 (89 : Fin 91) < 1 + values11 (90 : Fin 91)
    linarith [values11_strictMono (by native_decide : (89 : Fin 91) < 90)]

theorem values13_range_ncard :
    (Set.range values13).ncard = 264 := by
  rw [Set.ncard_range_of_injective values13_strictMono.injective]
  norm_num

@[simp] theorem sqrt_values12_mem_recursiveValueSet_thirteen (i : Fin 154) :
    Real.sqrt (values12 i) ∈ recursiveValueSet 13 := by
  rw [recursiveValueSet]
  exact Or.inl ⟨values12 i, values12_mem_recursiveValueSet i, rfl⟩

@[simp] theorem one_add_values11_mem_recursiveValueSet_thirteen (i : Fin 91) :
    1 + values11 i ∈ recursiveValueSet 13 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨0, by decide⟩, 1, ?_, values11 i, ?_, rfl⟩
  · simp [recursiveValueSet]
  · change values11 i ∈ recursiveValueSet 11
    rw [recursiveValueSet_eleven]
    exact ⟨i, rfl⟩

@[simp] theorem values6_add_values6_mem_recursiveValueSet_thirteen
    (i j : Fin 8) :
    values6 i + values6 j ∈ recursiveValueSet 13 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨5, by decide⟩, values6 i, ?_, values6 j, ?_, rfl⟩
  · change values6 i ∈ recursiveValueSet 6
    rw [recursiveValueSet_six_eq_range_values6]
    exact ⟨i, rfl⟩
  · change values6 j ∈ recursiveValueSet 6
    rw [recursiveValueSet_six_eq_range_values6]
    exact ⟨j, rfl⟩

@[simp] theorem values5_add_values7_mem_recursiveValueSet_thirteen
    (i : Fin 5) (j : Fin 13) :
    values5 i + values7 j ∈ recursiveValueSet 13 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨4, by decide⟩, values5 i, ?_, values7 j, ?_, rfl⟩
  · change values5 i ∈ recursiveValueSet 5
    rw [recursiveValueSet_five_eq_range_values5]
    exact ⟨i, rfl⟩
  · change values7 j ∈ recursiveValueSet 7
    rw [recursiveValueSet_seven]
    exact ⟨j, rfl⟩

@[simp] theorem sqrt_two_add_values8_mem_recursiveValueSet_thirteen (i : Fin 20) :
    Real.sqrt 2 + values8 i ∈ recursiveValueSet 13 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, values8 i, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change values8 i ∈ recursiveValueSet 8
    rw [recursiveValueSet_eight]
    exact ⟨i, rfl⟩

set_option maxHeartbeats 1000000 in
theorem values13_mem_recursiveValueSet (i : Fin 264) :
    values13 i ∈ recursiveValueSet 13 := by
  fin_cases i
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (0 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (1 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (2 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (3 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (4 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (5 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (6 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (7 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (8 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (9 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (10 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (11 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (12 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (13 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (14 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (15 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (16 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (17 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (18 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (19 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (20 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (21 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (22 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (23 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (24 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (25 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (26 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (27 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (28 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (29 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (30 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (31 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (32 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (33 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (34 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (35 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (36 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (37 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (38 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (39 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (40 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (41 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (42 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (43 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (44 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (45 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (46 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (47 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (48 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (49 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (50 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (51 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (52 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (53 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (54 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (55 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (56 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (57 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (58 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (59 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (60 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (61 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (62 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (63 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (64 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (65 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (66 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (67 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (68 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (69 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (70 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (71 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (72 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (73 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (74 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (75 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (76 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (77 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (78 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (79 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (80 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (81 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (82 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (83 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (84 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (85 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (86 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (87 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (88 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (89 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (90 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (91 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (92 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (93 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (94 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (95 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (96 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (97 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (98 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (99 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (100 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (101 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (102 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (103 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (104 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (105 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (106 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (107 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (108 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (109 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (110 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (111 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (112 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (113 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (114 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (115 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (116 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (117 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (118 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (119 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (120 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (121 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (122 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (123 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (124 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (125 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (126 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (127 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (128 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (129 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (130 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (131 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (132 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (133 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (134 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (135 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (136 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (137 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (138 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (139 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (140 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (141 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (142 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (143 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (144 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (145 : Fin 154)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (146 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (1 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (2 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (3 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (4 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (5 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (147 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (6 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (7 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (8 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (148 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (9 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (10 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (11 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (12 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (13 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (149 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (14 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (15 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (16 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (17 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (18 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (150 : Fin 154)
  · exact values6_add_values6_mem_recursiveValueSet_thirteen (1 : Fin 8) (1 : Fin 8)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (19 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (20 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (21 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (22 : Fin 91)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (1 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (23 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (151 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (24 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (25 : Fin 91)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (2 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (26 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (27 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (28 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (152 : Fin 154)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (29 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (30 : Fin 91)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (3 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (31 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (32 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (33 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (1 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (34 : Fin 91)
  · exact sqrt_values12_mem_recursiveValueSet_thirteen (153 : Fin 154)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (2 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (35 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (36 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (37 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (38 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (3 : Fin 20)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (4 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (39 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (40 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (4 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (41 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (42 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (5 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (43 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (44 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (6 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (45 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (7 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (46 : Fin 91)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (6 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (47 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (48 : Fin 91)
  · exact values6_add_values6_mem_recursiveValueSet_thirteen (1 : Fin 8) (4 : Fin 8)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (8 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (49 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (9 : Fin 20)
  · exact values5_add_values7_mem_recursiveValueSet_thirteen (1 : Fin 5) (7 : Fin 13)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (50 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (10 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (51 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (52 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (53 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (54 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (55 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (56 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (57 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (58 : Fin 91)
  · exact sqrt_two_add_values8_mem_recursiveValueSet_thirteen (11 : Fin 20)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (59 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (60 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (61 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (62 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (63 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (64 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (65 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (66 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (67 : Fin 91)
  · exact values6_add_values6_mem_recursiveValueSet_thirteen (4 : Fin 8) (4 : Fin 8)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (68 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (69 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (70 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (71 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (72 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (73 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (74 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (75 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (76 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (77 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (78 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (79 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (80 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (81 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (82 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (83 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (84 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (85 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (86 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (87 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (88 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (89 : Fin 91)
  · exact one_add_values11_mem_recursiveValueSet_thirteen (90 : Fin 91)
theorem values13_range_subset_recursiveValueSet_thirteen :
    Set.range values13 ⊆ recursiveValueSet 13 := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact values13_mem_recursiveValueSet i

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_values12_mem_range_values13 (i : Fin 154) :
    Real.sqrt (values12 i) ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(0 : Fin 264), by
      change Real.sqrt (values12 (0 : Fin 154)) = Real.sqrt (values12 (0 : Fin 154))
      rfl
    ⟩
  · exact ⟨(1 : Fin 264), by
      change Real.sqrt (values12 (1 : Fin 154)) = Real.sqrt (values12 (1 : Fin 154))
      rfl
    ⟩
  · exact ⟨(2 : Fin 264), by
      change Real.sqrt (values12 (2 : Fin 154)) = Real.sqrt (values12 (2 : Fin 154))
      rfl
    ⟩
  · exact ⟨(3 : Fin 264), by
      change Real.sqrt (values12 (3 : Fin 154)) = Real.sqrt (values12 (3 : Fin 154))
      rfl
    ⟩
  · exact ⟨(4 : Fin 264), by
      change Real.sqrt (values12 (4 : Fin 154)) = Real.sqrt (values12 (4 : Fin 154))
      rfl
    ⟩
  · exact ⟨(5 : Fin 264), by
      change Real.sqrt (values12 (5 : Fin 154)) = Real.sqrt (values12 (5 : Fin 154))
      rfl
    ⟩
  · exact ⟨(6 : Fin 264), by
      change Real.sqrt (values12 (6 : Fin 154)) = Real.sqrt (values12 (6 : Fin 154))
      rfl
    ⟩
  · exact ⟨(7 : Fin 264), by
      change Real.sqrt (values12 (7 : Fin 154)) = Real.sqrt (values12 (7 : Fin 154))
      rfl
    ⟩
  · exact ⟨(8 : Fin 264), by
      change Real.sqrt (values12 (8 : Fin 154)) = Real.sqrt (values12 (8 : Fin 154))
      rfl
    ⟩
  · exact ⟨(9 : Fin 264), by
      change Real.sqrt (values12 (9 : Fin 154)) = Real.sqrt (values12 (9 : Fin 154))
      rfl
    ⟩
  · exact ⟨(10 : Fin 264), by
      change Real.sqrt (values12 (10 : Fin 154)) = Real.sqrt (values12 (10 : Fin 154))
      rfl
    ⟩
  · exact ⟨(11 : Fin 264), by
      change Real.sqrt (values12 (11 : Fin 154)) = Real.sqrt (values12 (11 : Fin 154))
      rfl
    ⟩
  · exact ⟨(12 : Fin 264), by
      change Real.sqrt (values12 (12 : Fin 154)) = Real.sqrt (values12 (12 : Fin 154))
      rfl
    ⟩
  · exact ⟨(13 : Fin 264), by
      change Real.sqrt (values12 (13 : Fin 154)) = Real.sqrt (values12 (13 : Fin 154))
      rfl
    ⟩
  · exact ⟨(14 : Fin 264), by
      change Real.sqrt (values12 (14 : Fin 154)) = Real.sqrt (values12 (14 : Fin 154))
      rfl
    ⟩
  · exact ⟨(15 : Fin 264), by
      change Real.sqrt (values12 (15 : Fin 154)) = Real.sqrt (values12 (15 : Fin 154))
      rfl
    ⟩
  · exact ⟨(16 : Fin 264), by
      change Real.sqrt (values12 (16 : Fin 154)) = Real.sqrt (values12 (16 : Fin 154))
      rfl
    ⟩
  · exact ⟨(17 : Fin 264), by
      change Real.sqrt (values12 (17 : Fin 154)) = Real.sqrt (values12 (17 : Fin 154))
      rfl
    ⟩
  · exact ⟨(18 : Fin 264), by
      change Real.sqrt (values12 (18 : Fin 154)) = Real.sqrt (values12 (18 : Fin 154))
      rfl
    ⟩
  · exact ⟨(19 : Fin 264), by
      change Real.sqrt (values12 (19 : Fin 154)) = Real.sqrt (values12 (19 : Fin 154))
      rfl
    ⟩
  · exact ⟨(20 : Fin 264), by
      change Real.sqrt (values12 (20 : Fin 154)) = Real.sqrt (values12 (20 : Fin 154))
      rfl
    ⟩
  · exact ⟨(21 : Fin 264), by
      change Real.sqrt (values12 (21 : Fin 154)) = Real.sqrt (values12 (21 : Fin 154))
      rfl
    ⟩
  · exact ⟨(22 : Fin 264), by
      change Real.sqrt (values12 (22 : Fin 154)) = Real.sqrt (values12 (22 : Fin 154))
      rfl
    ⟩
  · exact ⟨(23 : Fin 264), by
      change Real.sqrt (values12 (23 : Fin 154)) = Real.sqrt (values12 (23 : Fin 154))
      rfl
    ⟩
  · exact ⟨(24 : Fin 264), by
      change Real.sqrt (values12 (24 : Fin 154)) = Real.sqrt (values12 (24 : Fin 154))
      rfl
    ⟩
  · exact ⟨(25 : Fin 264), by
      change Real.sqrt (values12 (25 : Fin 154)) = Real.sqrt (values12 (25 : Fin 154))
      rfl
    ⟩
  · exact ⟨(26 : Fin 264), by
      change Real.sqrt (values12 (26 : Fin 154)) = Real.sqrt (values12 (26 : Fin 154))
      rfl
    ⟩
  · exact ⟨(27 : Fin 264), by
      change Real.sqrt (values12 (27 : Fin 154)) = Real.sqrt (values12 (27 : Fin 154))
      rfl
    ⟩
  · exact ⟨(28 : Fin 264), by
      change Real.sqrt (values12 (28 : Fin 154)) = Real.sqrt (values12 (28 : Fin 154))
      rfl
    ⟩
  · exact ⟨(29 : Fin 264), by
      change Real.sqrt (values12 (29 : Fin 154)) = Real.sqrt (values12 (29 : Fin 154))
      rfl
    ⟩
  · exact ⟨(30 : Fin 264), by
      change Real.sqrt (values12 (30 : Fin 154)) = Real.sqrt (values12 (30 : Fin 154))
      rfl
    ⟩
  · exact ⟨(31 : Fin 264), by
      change Real.sqrt (values12 (31 : Fin 154)) = Real.sqrt (values12 (31 : Fin 154))
      rfl
    ⟩
  · exact ⟨(32 : Fin 264), by
      change Real.sqrt (values12 (32 : Fin 154)) = Real.sqrt (values12 (32 : Fin 154))
      rfl
    ⟩
  · exact ⟨(33 : Fin 264), by
      change Real.sqrt (values12 (33 : Fin 154)) = Real.sqrt (values12 (33 : Fin 154))
      rfl
    ⟩
  · exact ⟨(34 : Fin 264), by
      change Real.sqrt (values12 (34 : Fin 154)) = Real.sqrt (values12 (34 : Fin 154))
      rfl
    ⟩
  · exact ⟨(35 : Fin 264), by
      change Real.sqrt (values12 (35 : Fin 154)) = Real.sqrt (values12 (35 : Fin 154))
      rfl
    ⟩
  · exact ⟨(36 : Fin 264), by
      change Real.sqrt (values12 (36 : Fin 154)) = Real.sqrt (values12 (36 : Fin 154))
      rfl
    ⟩
  · exact ⟨(37 : Fin 264), by
      change Real.sqrt (values12 (37 : Fin 154)) = Real.sqrt (values12 (37 : Fin 154))
      rfl
    ⟩
  · exact ⟨(38 : Fin 264), by
      change Real.sqrt (values12 (38 : Fin 154)) = Real.sqrt (values12 (38 : Fin 154))
      rfl
    ⟩
  · exact ⟨(39 : Fin 264), by
      change Real.sqrt (values12 (39 : Fin 154)) = Real.sqrt (values12 (39 : Fin 154))
      rfl
    ⟩
  · exact ⟨(40 : Fin 264), by
      change Real.sqrt (values12 (40 : Fin 154)) = Real.sqrt (values12 (40 : Fin 154))
      rfl
    ⟩
  · exact ⟨(41 : Fin 264), by
      change Real.sqrt (values12 (41 : Fin 154)) = Real.sqrt (values12 (41 : Fin 154))
      rfl
    ⟩
  · exact ⟨(42 : Fin 264), by
      change Real.sqrt (values12 (42 : Fin 154)) = Real.sqrt (values12 (42 : Fin 154))
      rfl
    ⟩
  · exact ⟨(43 : Fin 264), by
      change Real.sqrt (values12 (43 : Fin 154)) = Real.sqrt (values12 (43 : Fin 154))
      rfl
    ⟩
  · exact ⟨(44 : Fin 264), by
      change Real.sqrt (values12 (44 : Fin 154)) = Real.sqrt (values12 (44 : Fin 154))
      rfl
    ⟩
  · exact ⟨(45 : Fin 264), by
      change Real.sqrt (values12 (45 : Fin 154)) = Real.sqrt (values12 (45 : Fin 154))
      rfl
    ⟩
  · exact ⟨(46 : Fin 264), by
      change Real.sqrt (values12 (46 : Fin 154)) = Real.sqrt (values12 (46 : Fin 154))
      rfl
    ⟩
  · exact ⟨(47 : Fin 264), by
      change Real.sqrt (values12 (47 : Fin 154)) = Real.sqrt (values12 (47 : Fin 154))
      rfl
    ⟩
  · exact ⟨(48 : Fin 264), by
      change Real.sqrt (values12 (48 : Fin 154)) = Real.sqrt (values12 (48 : Fin 154))
      rfl
    ⟩
  · exact ⟨(49 : Fin 264), by
      change Real.sqrt (values12 (49 : Fin 154)) = Real.sqrt (values12 (49 : Fin 154))
      rfl
    ⟩
  · exact ⟨(50 : Fin 264), by
      change Real.sqrt (values12 (50 : Fin 154)) = Real.sqrt (values12 (50 : Fin 154))
      rfl
    ⟩
  · exact ⟨(51 : Fin 264), by
      change Real.sqrt (values12 (51 : Fin 154)) = Real.sqrt (values12 (51 : Fin 154))
      rfl
    ⟩
  · exact ⟨(52 : Fin 264), by
      change Real.sqrt (values12 (52 : Fin 154)) = Real.sqrt (values12 (52 : Fin 154))
      rfl
    ⟩
  · exact ⟨(53 : Fin 264), by
      change Real.sqrt (values12 (53 : Fin 154)) = Real.sqrt (values12 (53 : Fin 154))
      rfl
    ⟩
  · exact ⟨(54 : Fin 264), by
      change Real.sqrt (values12 (54 : Fin 154)) = Real.sqrt (values12 (54 : Fin 154))
      rfl
    ⟩
  · exact ⟨(55 : Fin 264), by
      change Real.sqrt (values12 (55 : Fin 154)) = Real.sqrt (values12 (55 : Fin 154))
      rfl
    ⟩
  · exact ⟨(56 : Fin 264), by
      change Real.sqrt (values12 (56 : Fin 154)) = Real.sqrt (values12 (56 : Fin 154))
      rfl
    ⟩
  · exact ⟨(57 : Fin 264), by
      change Real.sqrt (values12 (57 : Fin 154)) = Real.sqrt (values12 (57 : Fin 154))
      rfl
    ⟩
  · exact ⟨(58 : Fin 264), by
      change Real.sqrt (values12 (58 : Fin 154)) = Real.sqrt (values12 (58 : Fin 154))
      rfl
    ⟩
  · exact ⟨(59 : Fin 264), by
      change Real.sqrt (values12 (59 : Fin 154)) = Real.sqrt (values12 (59 : Fin 154))
      rfl
    ⟩
  · exact ⟨(60 : Fin 264), by
      change Real.sqrt (values12 (60 : Fin 154)) = Real.sqrt (values12 (60 : Fin 154))
      rfl
    ⟩
  · exact ⟨(61 : Fin 264), by
      change Real.sqrt (values12 (61 : Fin 154)) = Real.sqrt (values12 (61 : Fin 154))
      rfl
    ⟩
  · exact ⟨(62 : Fin 264), by
      change Real.sqrt (values12 (62 : Fin 154)) = Real.sqrt (values12 (62 : Fin 154))
      rfl
    ⟩
  · exact ⟨(63 : Fin 264), by
      change Real.sqrt (values12 (63 : Fin 154)) = Real.sqrt (values12 (63 : Fin 154))
      rfl
    ⟩
  · exact ⟨(64 : Fin 264), by
      change Real.sqrt (values12 (64 : Fin 154)) = Real.sqrt (values12 (64 : Fin 154))
      rfl
    ⟩
  · exact ⟨(65 : Fin 264), by
      change Real.sqrt (values12 (65 : Fin 154)) = Real.sqrt (values12 (65 : Fin 154))
      rfl
    ⟩
  · exact ⟨(66 : Fin 264), by
      change Real.sqrt (values12 (66 : Fin 154)) = Real.sqrt (values12 (66 : Fin 154))
      rfl
    ⟩
  · exact ⟨(67 : Fin 264), by
      change Real.sqrt (values12 (67 : Fin 154)) = Real.sqrt (values12 (67 : Fin 154))
      rfl
    ⟩
  · exact ⟨(68 : Fin 264), by
      change Real.sqrt (values12 (68 : Fin 154)) = Real.sqrt (values12 (68 : Fin 154))
      rfl
    ⟩
  · exact ⟨(69 : Fin 264), by
      change Real.sqrt (values12 (69 : Fin 154)) = Real.sqrt (values12 (69 : Fin 154))
      rfl
    ⟩
  · exact ⟨(70 : Fin 264), by
      change Real.sqrt (values12 (70 : Fin 154)) = Real.sqrt (values12 (70 : Fin 154))
      rfl
    ⟩
  · exact ⟨(71 : Fin 264), by
      change Real.sqrt (values12 (71 : Fin 154)) = Real.sqrt (values12 (71 : Fin 154))
      rfl
    ⟩
  · exact ⟨(72 : Fin 264), by
      change Real.sqrt (values12 (72 : Fin 154)) = Real.sqrt (values12 (72 : Fin 154))
      rfl
    ⟩
  · exact ⟨(73 : Fin 264), by
      change Real.sqrt (values12 (73 : Fin 154)) = Real.sqrt (values12 (73 : Fin 154))
      rfl
    ⟩
  · exact ⟨(74 : Fin 264), by
      change Real.sqrt (values12 (74 : Fin 154)) = Real.sqrt (values12 (74 : Fin 154))
      rfl
    ⟩
  · exact ⟨(75 : Fin 264), by
      change Real.sqrt (values12 (75 : Fin 154)) = Real.sqrt (values12 (75 : Fin 154))
      rfl
    ⟩
  · exact ⟨(76 : Fin 264), by
      change Real.sqrt (values12 (76 : Fin 154)) = Real.sqrt (values12 (76 : Fin 154))
      rfl
    ⟩
  · exact ⟨(77 : Fin 264), by
      change Real.sqrt (values12 (77 : Fin 154)) = Real.sqrt (values12 (77 : Fin 154))
      rfl
    ⟩
  · exact ⟨(78 : Fin 264), by
      change Real.sqrt (values12 (78 : Fin 154)) = Real.sqrt (values12 (78 : Fin 154))
      rfl
    ⟩
  · exact ⟨(79 : Fin 264), by
      change Real.sqrt (values12 (79 : Fin 154)) = Real.sqrt (values12 (79 : Fin 154))
      rfl
    ⟩
  · exact ⟨(80 : Fin 264), by
      change Real.sqrt (values12 (80 : Fin 154)) = Real.sqrt (values12 (80 : Fin 154))
      rfl
    ⟩
  · exact ⟨(81 : Fin 264), by
      change Real.sqrt (values12 (81 : Fin 154)) = Real.sqrt (values12 (81 : Fin 154))
      rfl
    ⟩
  · exact ⟨(82 : Fin 264), by
      change Real.sqrt (values12 (82 : Fin 154)) = Real.sqrt (values12 (82 : Fin 154))
      rfl
    ⟩
  · exact ⟨(83 : Fin 264), by
      change Real.sqrt (values12 (83 : Fin 154)) = Real.sqrt (values12 (83 : Fin 154))
      rfl
    ⟩
  · exact ⟨(84 : Fin 264), by
      change Real.sqrt (values12 (84 : Fin 154)) = Real.sqrt (values12 (84 : Fin 154))
      rfl
    ⟩
  · exact ⟨(85 : Fin 264), by
      change Real.sqrt (values12 (85 : Fin 154)) = Real.sqrt (values12 (85 : Fin 154))
      rfl
    ⟩
  · exact ⟨(86 : Fin 264), by
      change Real.sqrt (values12 (86 : Fin 154)) = Real.sqrt (values12 (86 : Fin 154))
      rfl
    ⟩
  · exact ⟨(87 : Fin 264), by
      change Real.sqrt (values12 (87 : Fin 154)) = Real.sqrt (values12 (87 : Fin 154))
      rfl
    ⟩
  · exact ⟨(88 : Fin 264), by
      change Real.sqrt (values12 (88 : Fin 154)) = Real.sqrt (values12 (88 : Fin 154))
      rfl
    ⟩
  · exact ⟨(89 : Fin 264), by
      change Real.sqrt (values12 (89 : Fin 154)) = Real.sqrt (values12 (89 : Fin 154))
      rfl
    ⟩
  · exact ⟨(90 : Fin 264), by
      change Real.sqrt (values12 (90 : Fin 154)) = Real.sqrt (values12 (90 : Fin 154))
      rfl
    ⟩
  · exact ⟨(91 : Fin 264), by
      change Real.sqrt (values12 (91 : Fin 154)) = Real.sqrt (values12 (91 : Fin 154))
      rfl
    ⟩
  · exact ⟨(92 : Fin 264), by
      change Real.sqrt (values12 (92 : Fin 154)) = Real.sqrt (values12 (92 : Fin 154))
      rfl
    ⟩
  · exact ⟨(93 : Fin 264), by
      change Real.sqrt (values12 (93 : Fin 154)) = Real.sqrt (values12 (93 : Fin 154))
      rfl
    ⟩
  · exact ⟨(94 : Fin 264), by
      change Real.sqrt (values12 (94 : Fin 154)) = Real.sqrt (values12 (94 : Fin 154))
      rfl
    ⟩
  · exact ⟨(95 : Fin 264), by
      change Real.sqrt (values12 (95 : Fin 154)) = Real.sqrt (values12 (95 : Fin 154))
      rfl
    ⟩
  · exact ⟨(96 : Fin 264), by
      change Real.sqrt (values12 (96 : Fin 154)) = Real.sqrt (values12 (96 : Fin 154))
      rfl
    ⟩
  · exact ⟨(97 : Fin 264), by
      change Real.sqrt (values12 (97 : Fin 154)) = Real.sqrt (values12 (97 : Fin 154))
      rfl
    ⟩
  · exact ⟨(98 : Fin 264), by
      change Real.sqrt (values12 (98 : Fin 154)) = Real.sqrt (values12 (98 : Fin 154))
      rfl
    ⟩
  · exact ⟨(99 : Fin 264), by
      change Real.sqrt (values12 (99 : Fin 154)) = Real.sqrt (values12 (99 : Fin 154))
      rfl
    ⟩
  · exact ⟨(100 : Fin 264), by
      change Real.sqrt (values12 (100 : Fin 154)) = Real.sqrt (values12 (100 : Fin 154))
      rfl
    ⟩
  · exact ⟨(101 : Fin 264), by
      change Real.sqrt (values12 (101 : Fin 154)) = Real.sqrt (values12 (101 : Fin 154))
      rfl
    ⟩
  · exact ⟨(102 : Fin 264), by
      change Real.sqrt (values12 (102 : Fin 154)) = Real.sqrt (values12 (102 : Fin 154))
      rfl
    ⟩
  · exact ⟨(103 : Fin 264), by
      change Real.sqrt (values12 (103 : Fin 154)) = Real.sqrt (values12 (103 : Fin 154))
      rfl
    ⟩
  · exact ⟨(104 : Fin 264), by
      change Real.sqrt (values12 (104 : Fin 154)) = Real.sqrt (values12 (104 : Fin 154))
      rfl
    ⟩
  · exact ⟨(105 : Fin 264), by
      change Real.sqrt (values12 (105 : Fin 154)) = Real.sqrt (values12 (105 : Fin 154))
      rfl
    ⟩
  · exact ⟨(106 : Fin 264), by
      change Real.sqrt (values12 (106 : Fin 154)) = Real.sqrt (values12 (106 : Fin 154))
      rfl
    ⟩
  · exact ⟨(107 : Fin 264), by
      change Real.sqrt (values12 (107 : Fin 154)) = Real.sqrt (values12 (107 : Fin 154))
      rfl
    ⟩
  · exact ⟨(108 : Fin 264), by
      change Real.sqrt (values12 (108 : Fin 154)) = Real.sqrt (values12 (108 : Fin 154))
      rfl
    ⟩
  · exact ⟨(109 : Fin 264), by
      change Real.sqrt (values12 (109 : Fin 154)) = Real.sqrt (values12 (109 : Fin 154))
      rfl
    ⟩
  · exact ⟨(110 : Fin 264), by
      change Real.sqrt (values12 (110 : Fin 154)) = Real.sqrt (values12 (110 : Fin 154))
      rfl
    ⟩
  · exact ⟨(111 : Fin 264), by
      change Real.sqrt (values12 (111 : Fin 154)) = Real.sqrt (values12 (111 : Fin 154))
      rfl
    ⟩
  · exact ⟨(112 : Fin 264), by
      change Real.sqrt (values12 (112 : Fin 154)) = Real.sqrt (values12 (112 : Fin 154))
      rfl
    ⟩
  · exact ⟨(113 : Fin 264), by
      change Real.sqrt (values12 (113 : Fin 154)) = Real.sqrt (values12 (113 : Fin 154))
      rfl
    ⟩
  · exact ⟨(114 : Fin 264), by
      change Real.sqrt (values12 (114 : Fin 154)) = Real.sqrt (values12 (114 : Fin 154))
      rfl
    ⟩
  · exact ⟨(115 : Fin 264), by
      change Real.sqrt (values12 (115 : Fin 154)) = Real.sqrt (values12 (115 : Fin 154))
      rfl
    ⟩
  · exact ⟨(116 : Fin 264), by
      change Real.sqrt (values12 (116 : Fin 154)) = Real.sqrt (values12 (116 : Fin 154))
      rfl
    ⟩
  · exact ⟨(117 : Fin 264), by
      change Real.sqrt (values12 (117 : Fin 154)) = Real.sqrt (values12 (117 : Fin 154))
      rfl
    ⟩
  · exact ⟨(118 : Fin 264), by
      change Real.sqrt (values12 (118 : Fin 154)) = Real.sqrt (values12 (118 : Fin 154))
      rfl
    ⟩
  · exact ⟨(119 : Fin 264), by
      change Real.sqrt (values12 (119 : Fin 154)) = Real.sqrt (values12 (119 : Fin 154))
      rfl
    ⟩
  · exact ⟨(120 : Fin 264), by
      change Real.sqrt (values12 (120 : Fin 154)) = Real.sqrt (values12 (120 : Fin 154))
      rfl
    ⟩
  · exact ⟨(121 : Fin 264), by
      change Real.sqrt (values12 (121 : Fin 154)) = Real.sqrt (values12 (121 : Fin 154))
      rfl
    ⟩
  · exact ⟨(122 : Fin 264), by
      change Real.sqrt (values12 (122 : Fin 154)) = Real.sqrt (values12 (122 : Fin 154))
      rfl
    ⟩
  · exact ⟨(123 : Fin 264), by
      change Real.sqrt (values12 (123 : Fin 154)) = Real.sqrt (values12 (123 : Fin 154))
      rfl
    ⟩
  · exact ⟨(124 : Fin 264), by
      change Real.sqrt (values12 (124 : Fin 154)) = Real.sqrt (values12 (124 : Fin 154))
      rfl
    ⟩
  · exact ⟨(125 : Fin 264), by
      change Real.sqrt (values12 (125 : Fin 154)) = Real.sqrt (values12 (125 : Fin 154))
      rfl
    ⟩
  · exact ⟨(126 : Fin 264), by
      change Real.sqrt (values12 (126 : Fin 154)) = Real.sqrt (values12 (126 : Fin 154))
      rfl
    ⟩
  · exact ⟨(127 : Fin 264), by
      change Real.sqrt (values12 (127 : Fin 154)) = Real.sqrt (values12 (127 : Fin 154))
      rfl
    ⟩
  · exact ⟨(128 : Fin 264), by
      change Real.sqrt (values12 (128 : Fin 154)) = Real.sqrt (values12 (128 : Fin 154))
      rfl
    ⟩
  · exact ⟨(129 : Fin 264), by
      change Real.sqrt (values12 (129 : Fin 154)) = Real.sqrt (values12 (129 : Fin 154))
      rfl
    ⟩
  · exact ⟨(130 : Fin 264), by
      change Real.sqrt (values12 (130 : Fin 154)) = Real.sqrt (values12 (130 : Fin 154))
      rfl
    ⟩
  · exact ⟨(131 : Fin 264), by
      change Real.sqrt (values12 (131 : Fin 154)) = Real.sqrt (values12 (131 : Fin 154))
      rfl
    ⟩
  · exact ⟨(132 : Fin 264), by
      change Real.sqrt (values12 (132 : Fin 154)) = Real.sqrt (values12 (132 : Fin 154))
      rfl
    ⟩
  · exact ⟨(133 : Fin 264), by
      change Real.sqrt (values12 (133 : Fin 154)) = Real.sqrt (values12 (133 : Fin 154))
      rfl
    ⟩
  · exact ⟨(134 : Fin 264), by
      change Real.sqrt (values12 (134 : Fin 154)) = Real.sqrt (values12 (134 : Fin 154))
      rfl
    ⟩
  · exact ⟨(135 : Fin 264), by
      change Real.sqrt (values12 (135 : Fin 154)) = Real.sqrt (values12 (135 : Fin 154))
      rfl
    ⟩
  · exact ⟨(136 : Fin 264), by
      change Real.sqrt (values12 (136 : Fin 154)) = Real.sqrt (values12 (136 : Fin 154))
      rfl
    ⟩
  · exact ⟨(137 : Fin 264), by
      change Real.sqrt (values12 (137 : Fin 154)) = Real.sqrt (values12 (137 : Fin 154))
      rfl
    ⟩
  · exact ⟨(138 : Fin 264), by
      change Real.sqrt (values12 (138 : Fin 154)) = Real.sqrt (values12 (138 : Fin 154))
      rfl
    ⟩
  · exact ⟨(139 : Fin 264), by
      change Real.sqrt (values12 (139 : Fin 154)) = Real.sqrt (values12 (139 : Fin 154))
      rfl
    ⟩
  · exact ⟨(140 : Fin 264), by
      change Real.sqrt (values12 (140 : Fin 154)) = Real.sqrt (values12 (140 : Fin 154))
      rfl
    ⟩
  · exact ⟨(141 : Fin 264), by
      change Real.sqrt (values12 (141 : Fin 154)) = Real.sqrt (values12 (141 : Fin 154))
      rfl
    ⟩
  · exact ⟨(142 : Fin 264), by
      change Real.sqrt (values12 (142 : Fin 154)) = Real.sqrt (values12 (142 : Fin 154))
      rfl
    ⟩
  · exact ⟨(143 : Fin 264), by
      change Real.sqrt (values12 (143 : Fin 154)) = Real.sqrt (values12 (143 : Fin 154))
      rfl
    ⟩
  · exact ⟨(144 : Fin 264), by
      change Real.sqrt (values12 (144 : Fin 154)) = Real.sqrt (values12 (144 : Fin 154))
      rfl
    ⟩
  · exact ⟨(145 : Fin 264), by
      change Real.sqrt (values12 (145 : Fin 154)) = Real.sqrt (values12 (145 : Fin 154))
      rfl
    ⟩
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = Real.sqrt (values12 (146 : Fin 154))
      rfl
    ⟩
  · exact ⟨(152 : Fin 264), by
      change Real.sqrt (values12 (147 : Fin 154)) = Real.sqrt (values12 (147 : Fin 154))
      rfl
    ⟩
  · exact ⟨(156 : Fin 264), by
      change Real.sqrt (values12 (148 : Fin 154)) = Real.sqrt (values12 (148 : Fin 154))
      rfl
    ⟩
  · exact ⟨(162 : Fin 264), by
      change Real.sqrt (values12 (149 : Fin 154)) = Real.sqrt (values12 (149 : Fin 154))
      rfl
    ⟩
  · exact ⟨(168 : Fin 264), by
      change Real.sqrt (values12 (150 : Fin 154)) = Real.sqrt (values12 (150 : Fin 154))
      rfl
    ⟩
  · exact ⟨(176 : Fin 264), by
      change Real.sqrt (values12 (151 : Fin 154)) = Real.sqrt (values12 (151 : Fin 154))
      rfl
    ⟩
  · exact ⟨(183 : Fin 264), by
      change Real.sqrt (values12 (152 : Fin 154)) = Real.sqrt (values12 (152 : Fin 154))
      rfl
    ⟩
  · exact ⟨(192 : Fin 264), by
      change Real.sqrt (values12 (153 : Fin 154)) = Real.sqrt (values12 (153 : Fin 154))
      rfl
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values11_mem_range_values13 (i : Fin 91) :
    1 + values11 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = 1 + values11 (0 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(147 : Fin 264), by
      change 1 + values11 (1 : Fin 91) = 1 + values11 (1 : Fin 91)
      rfl
    ⟩
  · exact ⟨(148 : Fin 264), by
      change 1 + values11 (2 : Fin 91) = 1 + values11 (2 : Fin 91)
      rfl
    ⟩
  · exact ⟨(149 : Fin 264), by
      change 1 + values11 (3 : Fin 91) = 1 + values11 (3 : Fin 91)
      rfl
    ⟩
  · exact ⟨(150 : Fin 264), by
      change 1 + values11 (4 : Fin 91) = 1 + values11 (4 : Fin 91)
      rfl
    ⟩
  · exact ⟨(151 : Fin 264), by
      change 1 + values11 (5 : Fin 91) = 1 + values11 (5 : Fin 91)
      rfl
    ⟩
  · exact ⟨(153 : Fin 264), by
      change 1 + values11 (6 : Fin 91) = 1 + values11 (6 : Fin 91)
      rfl
    ⟩
  · exact ⟨(154 : Fin 264), by
      change 1 + values11 (7 : Fin 91) = 1 + values11 (7 : Fin 91)
      rfl
    ⟩
  · exact ⟨(155 : Fin 264), by
      change 1 + values11 (8 : Fin 91) = 1 + values11 (8 : Fin 91)
      rfl
    ⟩
  · exact ⟨(157 : Fin 264), by
      change 1 + values11 (9 : Fin 91) = 1 + values11 (9 : Fin 91)
      rfl
    ⟩
  · exact ⟨(158 : Fin 264), by
      change 1 + values11 (10 : Fin 91) = 1 + values11 (10 : Fin 91)
      rfl
    ⟩
  · exact ⟨(159 : Fin 264), by
      change 1 + values11 (11 : Fin 91) = 1 + values11 (11 : Fin 91)
      rfl
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = 1 + values11 (12 : Fin 91)
      rfl
    ⟩
  · exact ⟨(161 : Fin 264), by
      change 1 + values11 (13 : Fin 91) = 1 + values11 (13 : Fin 91)
      rfl
    ⟩
  · exact ⟨(163 : Fin 264), by
      change 1 + values11 (14 : Fin 91) = 1 + values11 (14 : Fin 91)
      rfl
    ⟩
  · exact ⟨(164 : Fin 264), by
      change 1 + values11 (15 : Fin 91) = 1 + values11 (15 : Fin 91)
      rfl
    ⟩
  · exact ⟨(165 : Fin 264), by
      change 1 + values11 (16 : Fin 91) = 1 + values11 (16 : Fin 91)
      rfl
    ⟩
  · exact ⟨(166 : Fin 264), by
      change 1 + values11 (17 : Fin 91) = 1 + values11 (17 : Fin 91)
      rfl
    ⟩
  · exact ⟨(167 : Fin 264), by
      change 1 + values11 (18 : Fin 91) = 1 + values11 (18 : Fin 91)
      rfl
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = 1 + values11 (19 : Fin 91)
      rfl
    ⟩
  · exact ⟨(171 : Fin 264), by
      change 1 + values11 (20 : Fin 91) = 1 + values11 (20 : Fin 91)
      rfl
    ⟩
  · exact ⟨(172 : Fin 264), by
      change 1 + values11 (21 : Fin 91) = 1 + values11 (21 : Fin 91)
      rfl
    ⟩
  · exact ⟨(173 : Fin 264), by
      change 1 + values11 (22 : Fin 91) = 1 + values11 (22 : Fin 91)
      rfl
    ⟩
  · exact ⟨(175 : Fin 264), by
      change 1 + values11 (23 : Fin 91) = 1 + values11 (23 : Fin 91)
      rfl
    ⟩
  · exact ⟨(177 : Fin 264), by
      change 1 + values11 (24 : Fin 91) = 1 + values11 (24 : Fin 91)
      rfl
    ⟩
  · exact ⟨(178 : Fin 264), by
      change 1 + values11 (25 : Fin 91) = 1 + values11 (25 : Fin 91)
      rfl
    ⟩
  · exact ⟨(180 : Fin 264), by
      change 1 + values11 (26 : Fin 91) = 1 + values11 (26 : Fin 91)
      rfl
    ⟩
  · exact ⟨(181 : Fin 264), by
      change 1 + values11 (27 : Fin 91) = 1 + values11 (27 : Fin 91)
      rfl
    ⟩
  · exact ⟨(182 : Fin 264), by
      change 1 + values11 (28 : Fin 91) = 1 + values11 (28 : Fin 91)
      rfl
    ⟩
  · exact ⟨(184 : Fin 264), by
      change 1 + values11 (29 : Fin 91) = 1 + values11 (29 : Fin 91)
      rfl
    ⟩
  · exact ⟨(185 : Fin 264), by
      change 1 + values11 (30 : Fin 91) = 1 + values11 (30 : Fin 91)
      rfl
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = 1 + values11 (31 : Fin 91)
      rfl
    ⟩
  · exact ⟨(188 : Fin 264), by
      change 1 + values11 (32 : Fin 91) = 1 + values11 (32 : Fin 91)
      rfl
    ⟩
  · exact ⟨(189 : Fin 264), by
      change 1 + values11 (33 : Fin 91) = 1 + values11 (33 : Fin 91)
      rfl
    ⟩
  · exact ⟨(191 : Fin 264), by
      change 1 + values11 (34 : Fin 91) = 1 + values11 (34 : Fin 91)
      rfl
    ⟩
  · exact ⟨(194 : Fin 264), by
      change 1 + values11 (35 : Fin 91) = 1 + values11 (35 : Fin 91)
      rfl
    ⟩
  · exact ⟨(195 : Fin 264), by
      change 1 + values11 (36 : Fin 91) = 1 + values11 (36 : Fin 91)
      rfl
    ⟩
  · exact ⟨(196 : Fin 264), by
      change 1 + values11 (37 : Fin 91) = 1 + values11 (37 : Fin 91)
      rfl
    ⟩
  · exact ⟨(197 : Fin 264), by
      change 1 + values11 (38 : Fin 91) = 1 + values11 (38 : Fin 91)
      rfl
    ⟩
  · exact ⟨(200 : Fin 264), by
      change 1 + values11 (39 : Fin 91) = 1 + values11 (39 : Fin 91)
      rfl
    ⟩
  · exact ⟨(201 : Fin 264), by
      change 1 + values11 (40 : Fin 91) = 1 + values11 (40 : Fin 91)
      rfl
    ⟩
  · exact ⟨(203 : Fin 264), by
      change 1 + values11 (41 : Fin 91) = 1 + values11 (41 : Fin 91)
      rfl
    ⟩
  · exact ⟨(204 : Fin 264), by
      change 1 + values11 (42 : Fin 91) = 1 + values11 (42 : Fin 91)
      rfl
    ⟩
  · exact ⟨(206 : Fin 264), by
      change 1 + values11 (43 : Fin 91) = 1 + values11 (43 : Fin 91)
      rfl
    ⟩
  · exact ⟨(207 : Fin 264), by
      change 1 + values11 (44 : Fin 91) = 1 + values11 (44 : Fin 91)
      rfl
    ⟩
  · exact ⟨(209 : Fin 264), by
      change 1 + values11 (45 : Fin 91) = 1 + values11 (45 : Fin 91)
      rfl
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = 1 + values11 (46 : Fin 91)
      rfl
    ⟩
  · exact ⟨(213 : Fin 264), by
      change 1 + values11 (47 : Fin 91) = 1 + values11 (47 : Fin 91)
      rfl
    ⟩
  · exact ⟨(214 : Fin 264), by
      change 1 + values11 (48 : Fin 91) = 1 + values11 (48 : Fin 91)
      rfl
    ⟩
  · exact ⟨(217 : Fin 264), by
      change 1 + values11 (49 : Fin 91) = 1 + values11 (49 : Fin 91)
      rfl
    ⟩
  · exact ⟨(220 : Fin 264), by
      change 1 + values11 (50 : Fin 91) = 1 + values11 (50 : Fin 91)
      rfl
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 1 + values11 (51 : Fin 91)
      rfl
    ⟩
  · exact ⟨(223 : Fin 264), by
      change 1 + values11 (52 : Fin 91) = 1 + values11 (52 : Fin 91)
      rfl
    ⟩
  · exact ⟨(224 : Fin 264), by
      change 1 + values11 (53 : Fin 91) = 1 + values11 (53 : Fin 91)
      rfl
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = 1 + values11 (54 : Fin 91)
      rfl
    ⟩
  · exact ⟨(226 : Fin 264), by
      change 1 + values11 (55 : Fin 91) = 1 + values11 (55 : Fin 91)
      rfl
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 1 + values11 (56 : Fin 91)
      rfl
    ⟩
  · exact ⟨(228 : Fin 264), by
      change 1 + values11 (57 : Fin 91) = 1 + values11 (57 : Fin 91)
      rfl
    ⟩
  · exact ⟨(229 : Fin 264), by
      change 1 + values11 (58 : Fin 91) = 1 + values11 (58 : Fin 91)
      rfl
    ⟩
  · exact ⟨(231 : Fin 264), by
      change 1 + values11 (59 : Fin 91) = 1 + values11 (59 : Fin 91)
      rfl
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 1 + values11 (60 : Fin 91)
      rfl
    ⟩
  · exact ⟨(233 : Fin 264), by
      change 1 + values11 (61 : Fin 91) = 1 + values11 (61 : Fin 91)
      rfl
    ⟩
  · exact ⟨(234 : Fin 264), by
      change 1 + values11 (62 : Fin 91) = 1 + values11 (62 : Fin 91)
      rfl
    ⟩
  · exact ⟨(235 : Fin 264), by
      change 1 + values11 (63 : Fin 91) = 1 + values11 (63 : Fin 91)
      rfl
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = 1 + values11 (64 : Fin 91)
      rfl
    ⟩
  · exact ⟨(237 : Fin 264), by
      change 1 + values11 (65 : Fin 91) = 1 + values11 (65 : Fin 91)
      rfl
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 1 + values11 (66 : Fin 91)
      rfl
    ⟩
  · exact ⟨(239 : Fin 264), by
      change 1 + values11 (67 : Fin 91) = 1 + values11 (67 : Fin 91)
      rfl
    ⟩
  · exact ⟨(241 : Fin 264), by
      change 1 + values11 (68 : Fin 91) = 1 + values11 (68 : Fin 91)
      rfl
    ⟩
  · exact ⟨(242 : Fin 264), by
      change 1 + values11 (69 : Fin 91) = 1 + values11 (69 : Fin 91)
      rfl
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = 1 + values11 (70 : Fin 91)
      rfl
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = 1 + values11 (71 : Fin 91)
      rfl
    ⟩
  · exact ⟨(245 : Fin 264), by
      change 1 + values11 (72 : Fin 91) = 1 + values11 (72 : Fin 91)
      rfl
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 1 + values11 (73 : Fin 91)
      rfl
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = 1 + values11 (74 : Fin 91)
      rfl
    ⟩
  · exact ⟨(248 : Fin 264), by
      change 1 + values11 (75 : Fin 91) = 1 + values11 (75 : Fin 91)
      rfl
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 1 + values11 (76 : Fin 91)
      rfl
    ⟩
  · exact ⟨(250 : Fin 264), by
      change 1 + values11 (77 : Fin 91) = 1 + values11 (77 : Fin 91)
      rfl
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = 1 + values11 (78 : Fin 91)
      rfl
    ⟩
  · exact ⟨(252 : Fin 264), by
      change 1 + values11 (79 : Fin 91) = 1 + values11 (79 : Fin 91)
      rfl
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = 1 + values11 (80 : Fin 91)
      rfl
    ⟩
  · exact ⟨(254 : Fin 264), by
      change 1 + values11 (81 : Fin 91) = 1 + values11 (81 : Fin 91)
      rfl
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 1 + values11 (82 : Fin 91)
      rfl
    ⟩
  · exact ⟨(256 : Fin 264), by
      change 1 + values11 (83 : Fin 91) = 1 + values11 (83 : Fin 91)
      rfl
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = 1 + values11 (84 : Fin 91)
      rfl
    ⟩
  · exact ⟨(258 : Fin 264), by
      change 1 + values11 (85 : Fin 91) = 1 + values11 (85 : Fin 91)
      rfl
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 1 + values11 (86 : Fin 91)
      rfl
    ⟩
  · exact ⟨(260 : Fin 264), by
      change 1 + values11 (87 : Fin 91) = 1 + values11 (87 : Fin 91)
      rfl
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = 1 + values11 (88 : Fin 91)
      rfl
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = 1 + values11 (89 : Fin 91)
      rfl
    ⟩
  · exact ⟨(263 : Fin 264), by
      change 1 + values11 (90 : Fin 91) = 1 + values11 (90 : Fin 91)
      rfl
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values10_mem_range_values13 (i : Fin 54) :
    1 + values10 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = 1 + values10 (0 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(148 : Fin 264), by
      change 1 + values11 (2 : Fin 91) = 1 + values10 (1 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(149 : Fin 264), by
      change 1 + values11 (3 : Fin 91) = 1 + values10 (2 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(151 : Fin 264), by
      change 1 + values11 (5 : Fin 91) = 1 + values10 (3 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(154 : Fin 264), by
      change 1 + values11 (7 : Fin 91) = 1 + values10 (4 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(155 : Fin 264), by
      change 1 + values11 (8 : Fin 91) = 1 + values10 (5 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(158 : Fin 264), by
      change 1 + values11 (10 : Fin 91) = 1 + values10 (6 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(159 : Fin 264), by
      change 1 + values11 (11 : Fin 91) = 1 + values10 (7 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = 1 + values10 (8 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(163 : Fin 264), by
      change 1 + values11 (14 : Fin 91) = 1 + values10 (9 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(164 : Fin 264), by
      change 1 + values11 (15 : Fin 91) = 1 + values10 (10 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(166 : Fin 264), by
      change 1 + values11 (17 : Fin 91) = 1 + values10 (11 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = 1 + values10 (12 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(172 : Fin 264), by
      change 1 + values11 (21 : Fin 91) = 1 + values10 (13 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(173 : Fin 264), by
      change 1 + values11 (22 : Fin 91) = 1 + values10 (14 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(177 : Fin 264), by
      change 1 + values11 (24 : Fin 91) = 1 + values10 (15 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(180 : Fin 264), by
      change 1 + values11 (26 : Fin 91) = 1 + values10 (16 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(182 : Fin 264), by
      change 1 + values11 (28 : Fin 91) = 1 + values10 (17 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(185 : Fin 264), by
      change 1 + values11 (30 : Fin 91) = 1 + values10 (18 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = 1 + values10 (19 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(189 : Fin 264), by
      change 1 + values11 (33 : Fin 91) = 1 + values10 (20 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(191 : Fin 264), by
      change 1 + values11 (34 : Fin 91) = 1 + values10 (21 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(195 : Fin 264), by
      change 1 + values11 (36 : Fin 91) = 1 + values10 (22 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(200 : Fin 264), by
      change 1 + values11 (39 : Fin 91) = 1 + values10 (23 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(201 : Fin 264), by
      change 1 + values11 (40 : Fin 91) = 1 + values10 (24 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(204 : Fin 264), by
      change 1 + values11 (42 : Fin 91) = 1 + values10 (25 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(207 : Fin 264), by
      change 1 + values11 (44 : Fin 91) = 1 + values10 (26 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(209 : Fin 264), by
      change 1 + values11 (45 : Fin 91) = 1 + values10 (27 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = 1 + values10 (28 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(214 : Fin 264), by
      change 1 + values11 (48 : Fin 91) = 1 + values10 (29 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(217 : Fin 264), by
      change 1 + values11 (49 : Fin 91) = 1 + values10 (30 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 1 + values10 (31 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(224 : Fin 264), by
      change 1 + values11 (53 : Fin 91) = 1 + values10 (32 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = 1 + values10 (33 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 1 + values10 (34 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(231 : Fin 264), by
      change 1 + values11 (59 : Fin 91) = 1 + values10 (35 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 1 + values10 (36 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(234 : Fin 264), by
      change 1 + values11 (62 : Fin 91) = 1 + values10 (37 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(235 : Fin 264), by
      change 1 + values11 (63 : Fin 91) = 1 + values10 (38 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = 1 + values10 (39 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 1 + values10 (40 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(241 : Fin 264), by
      change 1 + values11 (68 : Fin 91) = 1 + values10 (41 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = 1 + values10 (42 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = 1 + values10 (43 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 1 + values10 (44 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = 1 + values10 (45 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 1 + values10 (46 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = 1 + values10 (47 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = 1 + values10 (48 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 1 + values10 (49 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = 1 + values10 (50 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 1 + values10 (51 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = 1 + values10 (52 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = 1 + values10 (53 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values9_mem_range_values13 (i : Fin 33) :
    1 + values9 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = 1 + values9 (0 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(149 : Fin 264), by
      change 1 + values11 (3 : Fin 91) = 1 + values9 (1 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(151 : Fin 264), by
      change 1 + values11 (5 : Fin 91) = 1 + values9 (2 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(155 : Fin 264), by
      change 1 + values11 (8 : Fin 91) = 1 + values9 (3 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(159 : Fin 264), by
      change 1 + values11 (11 : Fin 91) = 1 + values9 (4 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = 1 + values9 (5 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(164 : Fin 264), by
      change 1 + values11 (15 : Fin 91) = 1 + values9 (6 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(166 : Fin 264), by
      change 1 + values11 (17 : Fin 91) = 1 + values9 (7 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = 1 + values9 (8 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(173 : Fin 264), by
      change 1 + values11 (22 : Fin 91) = 1 + values9 (9 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(177 : Fin 264), by
      change 1 + values11 (24 : Fin 91) = 1 + values9 (10 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(182 : Fin 264), by
      change 1 + values11 (28 : Fin 91) = 1 + values9 (11 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = 1 + values9 (12 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(191 : Fin 264), by
      change 1 + values11 (34 : Fin 91) = 1 + values9 (13 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(195 : Fin 264), by
      change 1 + values11 (36 : Fin 91) = 1 + values9 (14 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(201 : Fin 264), by
      change 1 + values11 (40 : Fin 91) = 1 + values9 (15 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(207 : Fin 264), by
      change 1 + values11 (44 : Fin 91) = 1 + values9 (16 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = 1 + values9 (17 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(217 : Fin 264), by
      change 1 + values11 (49 : Fin 91) = 1 + values9 (18 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 1 + values9 (19 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = 1 + values9 (20 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 1 + values9 (21 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 1 + values9 (22 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = 1 + values9 (23 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 1 + values9 (24 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = 1 + values9 (25 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 1 + values9 (26 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = 1 + values9 (27 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 1 + values9 (28 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = 1 + values9 (29 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 1 + values9 (30 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 1 + values9 (31 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = 1 + values9 (32 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values9_mem_range_values13 (i : Fin 33) :
    2 + values9 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 2 + values9 (0 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(223 : Fin 264), by
      change 1 + values11 (52 : Fin 91) = 2 + values9 (1 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(224 : Fin 264), by
      change 1 + values11 (53 : Fin 91) = 2 + values9 (2 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = 2 + values9 (3 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(226 : Fin 264), by
      change 1 + values11 (55 : Fin 91) = 2 + values9 (4 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 2 + values9 (5 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(229 : Fin 264), by
      change 1 + values11 (58 : Fin 91) = 2 + values9 (6 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(231 : Fin 264), by
      change 1 + values11 (59 : Fin 91) = 2 + values9 (7 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 2 + values9 (8 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(233 : Fin 264), by
      change 1 + values11 (61 : Fin 91) = 2 + values9 (9 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(235 : Fin 264), by
      change 1 + values11 (63 : Fin 91) = 2 + values9 (10 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = 2 + values9 (11 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 2 + values9 (12 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(239 : Fin 264), by
      change 1 + values11 (67 : Fin 91) = 2 + values9 (13 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(241 : Fin 264), by
      change 1 + values11 (68 : Fin 91) = 2 + values9 (14 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = 2 + values9 (15 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(245 : Fin 264), by
      change 1 + values11 (72 : Fin 91) = 2 + values9 (16 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 2 + values9 (17 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(248 : Fin 264), by
      change 1 + values11 (75 : Fin 91) = 2 + values9 (18 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 2 + values9 (19 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(250 : Fin 264), by
      change 1 + values11 (77 : Fin 91) = 2 + values9 (20 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = 2 + values9 (21 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = 2 + values9 (22 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(254 : Fin 264), by
      change 1 + values11 (81 : Fin 91) = 2 + values9 (23 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 2 + values9 (24 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(256 : Fin 264), by
      change 1 + values11 (83 : Fin 91) = 2 + values9 (25 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = 2 + values9 (26 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(258 : Fin 264), by
      change 1 + values11 (85 : Fin 91) = 2 + values9 (27 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 2 + values9 (28 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(260 : Fin 264), by
      change 1 + values11 (87 : Fin 91) = 2 + values9 (29 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = 2 + values9 (30 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = 2 + values9 (31 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(263 : Fin 264), by
      change 1 + values11 (90 : Fin 91) = 2 + values9 (32 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values8_mem_range_values13 (i : Fin 20) :
    1 + values8 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = 1 + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(151 : Fin 264), by
      change 1 + values11 (5 : Fin 91) = 1 + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(155 : Fin 264), by
      change 1 + values11 (8 : Fin 91) = 1 + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = 1 + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(166 : Fin 264), by
      change 1 + values11 (17 : Fin 91) = 1 + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = 1 + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(177 : Fin 264), by
      change 1 + values11 (24 : Fin 91) = 1 + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(182 : Fin 264), by
      change 1 + values11 (28 : Fin 91) = 1 + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = 1 + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(195 : Fin 264), by
      change 1 + values11 (36 : Fin 91) = 1 + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(201 : Fin 264), by
      change 1 + values11 (40 : Fin 91) = 1 + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = 1 + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 1 + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 1 + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 1 + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 1 + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 1 + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 1 + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 1 + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 1 + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_two_add_values8_mem_range_values13 (i : Fin 20) :
    Real.sqrt 2 + values8 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = Real.sqrt 2 + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(190 : Fin 264), by
      change Real.sqrt 2 + values8 (1 : Fin 20) = Real.sqrt 2 + values8 (1 : Fin 20)
      rfl
    ⟩
  · exact ⟨(193 : Fin 264), by
      change Real.sqrt 2 + values8 (2 : Fin 20) = Real.sqrt 2 + values8 (2 : Fin 20)
      rfl
    ⟩
  · exact ⟨(198 : Fin 264), by
      change Real.sqrt 2 + values8 (3 : Fin 20) = Real.sqrt 2 + values8 (3 : Fin 20)
      rfl
    ⟩
  · exact ⟨(202 : Fin 264), by
      change Real.sqrt 2 + values8 (4 : Fin 20) = Real.sqrt 2 + values8 (4 : Fin 20)
      rfl
    ⟩
  · exact ⟨(205 : Fin 264), by
      change Real.sqrt 2 + values8 (5 : Fin 20) = Real.sqrt 2 + values8 (5 : Fin 20)
      rfl
    ⟩
  · exact ⟨(208 : Fin 264), by
      change Real.sqrt 2 + values8 (6 : Fin 20) = Real.sqrt 2 + values8 (6 : Fin 20)
      rfl
    ⟩
  · exact ⟨(210 : Fin 264), by
      change Real.sqrt 2 + values8 (7 : Fin 20) = Real.sqrt 2 + values8 (7 : Fin 20)
      rfl
    ⟩
  · exact ⟨(216 : Fin 264), by
      change Real.sqrt 2 + values8 (8 : Fin 20) = Real.sqrt 2 + values8 (8 : Fin 20)
      rfl
    ⟩
  · exact ⟨(218 : Fin 264), by
      change Real.sqrt 2 + values8 (9 : Fin 20) = Real.sqrt 2 + values8 (9 : Fin 20)
      rfl
    ⟩
  · exact ⟨(221 : Fin 264), by
      change Real.sqrt 2 + values8 (10 : Fin 20) = Real.sqrt 2 + values8 (10 : Fin 20)
      rfl
    ⟩
  · exact ⟨(230 : Fin 264), by
      change Real.sqrt 2 + values8 (11 : Fin 20) = Real.sqrt 2 + values8 (11 : Fin 20)
      rfl
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = Real.sqrt 2 + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(242 : Fin 264), by
      change 1 + values11 (69 : Fin 91) = Real.sqrt 2 + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = Real.sqrt 2 + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = Real.sqrt 2 + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(252 : Fin 264), by
      change 1 + values11 (79 : Fin 91) = Real.sqrt 2 + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = Real.sqrt 2 + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(258 : Fin 264), by
      change 1 + values11 (85 : Fin 91) = Real.sqrt 2 + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = Real.sqrt 2 + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values8_mem_range_values13 (i : Fin 20) :
    2 + values8 i ∈ Set.range values13 := by
  fin_cases i
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = 2 + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(224 : Fin 264), by
      change 1 + values11 (53 : Fin 91) = 2 + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = 2 + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = 2 + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(231 : Fin 264), by
      change 1 + values11 (59 : Fin 91) = 2 + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = 2 + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(235 : Fin 264), by
      change 1 + values11 (63 : Fin 91) = 2 + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = 2 + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = 2 + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(241 : Fin 264), by
      change 1 + values11 (68 : Fin 91) = 2 + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = 2 + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = 2 + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = 2 + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = 2 + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = 2 + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = 2 + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = 2 + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = 2 + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = 2 + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = 2 + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values5_add_values7_mem_range_values13 (i : Fin 5) (j : Fin 13) :
    values5 i + values7 j ∈ Set.range values13 := by
  fin_cases i <;> fin_cases j
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = values5 (0 : Fin 5) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(155 : Fin 264), by
      change 1 + values11 (8 : Fin 91) = values5 (0 : Fin 5) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = values5 (0 : Fin 5) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = values5 (0 : Fin 5) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(182 : Fin 264), by
      change 1 + values11 (28 : Fin 91) = values5 (0 : Fin 5) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = values5 (0 : Fin 5) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(201 : Fin 264), by
      change 1 + values11 (40 : Fin 91) = values5 (0 : Fin 5) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = values5 (0 : Fin 5) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = values5 (0 : Fin 5) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = values5 (0 : Fin 5) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values5 (0 : Fin 5) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values5 (0 : Fin 5) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = values5 (0 : Fin 5) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = values5 (1 : Fin 5) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(174 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (1 : Fin 13) = values5 (1 : Fin 5) + values7 (1 : Fin 13)
      rfl
    ⟩
  · exact ⟨(179 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (2 : Fin 13) = values5 (1 : Fin 5) + values7 (2 : Fin 13)
      rfl
    ⟩
  · exact ⟨(186 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (3 : Fin 13) = values5 (1 : Fin 5) + values7 (3 : Fin 13)
      rfl
    ⟩
  · exact ⟨(199 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (4 : Fin 13) = values5 (1 : Fin 5) + values7 (4 : Fin 13)
      rfl
    ⟩
  · exact ⟨(205 : Fin 264), by
      change Real.sqrt 2 + values8 (5 : Fin 20) = values5 (1 : Fin 5) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(212 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (6 : Fin 13) = values5 (1 : Fin 5) + values7 (6 : Fin 13)
      rfl
    ⟩
  · exact ⟨(219 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (7 : Fin 13) = values5 (1 : Fin 5) + values7 (7 : Fin 13)
      rfl
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = values5 (1 : Fin 5) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(237 : Fin 264), by
      change 1 + values11 (65 : Fin 91) = values5 (1 : Fin 5) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = values5 (1 : Fin 5) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = values5 (1 : Fin 5) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(260 : Fin 264), by
      change 1 + values11 (87 : Fin 91) = values5 (1 : Fin 5) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = values5 (2 : Fin 5) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(193 : Fin 264), by
      change Real.sqrt 2 + values8 (2 : Fin 20) = values5 (2 : Fin 5) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(198 : Fin 264), by
      change Real.sqrt 2 + values8 (3 : Fin 20) = values5 (2 : Fin 5) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(205 : Fin 264), by
      change Real.sqrt 2 + values8 (5 : Fin 20) = values5 (2 : Fin 5) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(210 : Fin 264), by
      change Real.sqrt 2 + values8 (7 : Fin 20) = values5 (2 : Fin 5) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(216 : Fin 264), by
      change Real.sqrt 2 + values8 (8 : Fin 20) = values5 (2 : Fin 5) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(221 : Fin 264), by
      change Real.sqrt 2 + values8 (10 : Fin 20) = values5 (2 : Fin 5) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(230 : Fin 264), by
      change Real.sqrt 2 + values8 (11 : Fin 20) = values5 (2 : Fin 5) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values5 (2 : Fin 5) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = values5 (2 : Fin 5) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = values5 (2 : Fin 5) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values5 (2 : Fin 5) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = values5 (2 : Fin 5) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = values5 (3 : Fin 5) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(225 : Fin 264), by
      change 1 + values11 (54 : Fin 91) = values5 (3 : Fin 5) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = values5 (3 : Fin 5) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = values5 (3 : Fin 5) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(236 : Fin 264), by
      change 1 + values11 (64 : Fin 91) = values5 (3 : Fin 5) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values5 (3 : Fin 5) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(243 : Fin 264), by
      change 1 + values11 (70 : Fin 91) = values5 (3 : Fin 5) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = values5 (3 : Fin 5) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values5 (3 : Fin 5) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = values5 (3 : Fin 5) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values5 (3 : Fin 5) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = values5 (3 : Fin 5) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = values5 (3 : Fin 5) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values5 (4 : Fin 5) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(250 : Fin 264), by
      change 1 + values11 (77 : Fin 91) = values5 (4 : Fin 5) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = values5 (4 : Fin 5) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = values5 (4 : Fin 5) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(254 : Fin 264), by
      change 1 + values11 (81 : Fin 91) = values5 (4 : Fin 5) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values5 (4 : Fin 5) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(256 : Fin 264), by
      change 1 + values11 (83 : Fin 91) = values5 (4 : Fin 5) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = values5 (4 : Fin 5) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = values5 (4 : Fin 5) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(260 : Fin 264), by
      change 1 + values11 (87 : Fin 91) = values5 (4 : Fin 5) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = values5 (4 : Fin 5) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = values5 (4 : Fin 5) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(263 : Fin 264), by
      change 1 + values11 (90 : Fin 91) = values5 (4 : Fin 5) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values6_add_values6_mem_range_values13 (i : Fin 8) (j : Fin 8) :
    values6 i + values6 j ∈ Set.range values13 := by
  fin_cases i <;> fin_cases j
  · exact ⟨(146 : Fin 264), by
      change Real.sqrt (values12 (146 : Fin 154)) = values6 (0 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = values6 (0 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = values6 (0 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = values6 (0 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = values6 (0 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = values6 (0 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values6 (0 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values6 (0 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(160 : Fin 264), by
      change 1 + values11 (12 : Fin 91) = values6 (1 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(169 : Fin 264), by
      change values6 (1 : Fin 8) + values6 (1 : Fin 8) = values6 (1 : Fin 8) + values6 (1 : Fin 8)
      rfl
    ⟩
  · exact ⟨(179 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (2 : Fin 13) = values6 (1 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(198 : Fin 264), by
      change Real.sqrt 2 + values8 (3 : Fin 20) = values6 (1 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(215 : Fin 264), by
      change values6 (1 : Fin 8) + values6 (4 : Fin 8) = values6 (1 : Fin 8) + values6 (4 : Fin 8)
      rfl
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = values6 (1 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(242 : Fin 264), by
      change 1 + values11 (69 : Fin 91) = values6 (1 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = values6 (1 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(170 : Fin 264), by
      change 1 + values11 (19 : Fin 91) = values6 (2 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(179 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (2 : Fin 13) = values6 (2 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(186 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (3 : Fin 13) = values6 (2 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(205 : Fin 264), by
      change Real.sqrt 2 + values8 (5 : Fin 20) = values6 (2 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(219 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (7 : Fin 13) = values6 (2 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = values6 (2 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = values6 (2 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = values6 (2 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(187 : Fin 264), by
      change 1 + values11 (31 : Fin 91) = values6 (3 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(198 : Fin 264), by
      change Real.sqrt 2 + values8 (3 : Fin 20) = values6 (3 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(205 : Fin 264), by
      change Real.sqrt 2 + values8 (5 : Fin 20) = values6 (3 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(216 : Fin 264), by
      change Real.sqrt 2 + values8 (8 : Fin 20) = values6 (3 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(230 : Fin 264), by
      change Real.sqrt 2 + values8 (11 : Fin 20) = values6 (3 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values6 (3 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = values6 (3 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values6 (3 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(211 : Fin 264), by
      change 1 + values11 (46 : Fin 91) = values6 (4 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(215 : Fin 264), by
      change values6 (1 : Fin 8) + values6 (4 : Fin 8) = values6 (4 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(219 : Fin 264), by
      change values5 (1 : Fin 5) + values7 (7 : Fin 13) = values6 (4 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(230 : Fin 264), by
      change Real.sqrt 2 + values8 (11 : Fin 20) = values6 (4 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(240 : Fin 264), by
      change values6 (4 : Fin 8) + values6 (4 : Fin 8) = values6 (4 : Fin 8) + values6 (4 : Fin 8)
      rfl
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = values6 (4 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(252 : Fin 264), by
      change 1 + values11 (79 : Fin 91) = values6 (4 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = values6 (4 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(222 : Fin 264), by
      change 1 + values11 (51 : Fin 91) = values6 (5 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(227 : Fin 264), by
      change 1 + values11 (56 : Fin 91) = values6 (5 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(232 : Fin 264), by
      change 1 + values11 (60 : Fin 91) = values6 (5 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values6 (5 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(246 : Fin 264), by
      change 1 + values11 (73 : Fin 91) = values6 (5 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values6 (5 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values6 (5 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = values6 (5 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(238 : Fin 264), by
      change 1 + values11 (66 : Fin 91) = values6 (6 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(242 : Fin 264), by
      change 1 + values11 (69 : Fin 91) = values6 (6 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(244 : Fin 264), by
      change 1 + values11 (71 : Fin 91) = values6 (6 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(247 : Fin 264), by
      change 1 + values11 (74 : Fin 91) = values6 (6 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(252 : Fin 264), by
      change 1 + values11 (79 : Fin 91) = values6 (6 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values6 (6 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(258 : Fin 264), by
      change 1 + values11 (85 : Fin 91) = values6 (6 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = values6 (6 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(249 : Fin 264), by
      change 1 + values11 (76 : Fin 91) = values6 (7 : Fin 8) + values6 (0 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(251 : Fin 264), by
      change 1 + values11 (78 : Fin 91) = values6 (7 : Fin 8) + values6 (1 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(253 : Fin 264), by
      change 1 + values11 (80 : Fin 91) = values6 (7 : Fin 8) + values6 (2 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(255 : Fin 264), by
      change 1 + values11 (82 : Fin 91) = values6 (7 : Fin 8) + values6 (3 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(257 : Fin 264), by
      change 1 + values11 (84 : Fin 91) = values6 (7 : Fin 8) + values6 (4 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(259 : Fin 264), by
      change 1 + values11 (86 : Fin 91) = values6 (7 : Fin 8) + values6 (5 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(261 : Fin 264), by
      change 1 + values11 (88 : Fin 91) = values6 (7 : Fin 8) + values6 (6 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
  · exact ⟨(262 : Fin 264), by
      change 1 + values11 (89 : Fin 91) = values6 (7 : Fin 8) + values6 (7 : Fin 8)
      a158415_twelve_table <;> try rw [sqrt_four]
    ⟩
theorem recursiveValueSet_thirteen_unary_subset_range :
    ((fun x : ℝ => Real.sqrt x) '' recursiveValueSet 12) ⊆ Set.range values13 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_twelve] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values12_mem_range_values13 i

set_option maxHeartbeats 2000000 in
theorem recursiveValueSet_thirteen_subset_range :
    recursiveValueSet 13 ⊆ Set.range values13 := by
  intro x hx
  rw [recursiveValueSet] at hx
  rcases hx with hsqrt | hadd
  · exact recursiveValueSet_thirteen_unary_subset_range hsqrt
  · rcases hadd with ⟨k, a, ha, b, hb, rfl⟩
    fin_cases k
    · simp [recursiveValueSet] at ha
      have hb' : b ∈ recursiveValueSet 11 := by simpa using hb
      rw [recursiveValueSet_eleven] at hb'
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values11_mem_range_values13 i
    · rw [recursiveValueSet_two] at ha
      have hb' : b ∈ recursiveValueSet 10 := by simpa using hb
      rw [recursiveValueSet_ten] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values10_mem_range_values13 i
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rw [recursiveValueSet_nine] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl
      · exact one_add_values9_mem_range_values13 i
      · exact two_add_values9_mem_range_values13 i
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 8 := by simpa using hb
      rw [recursiveValueSet_eight] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_values8_mem_range_values13 i
      · exact sqrt_two_add_values8_mem_range_values13 i
      · exact two_add_values8_mem_range_values13 i
    · rw [recursiveValueSet_five_eq_range_values5] at ha
      have hb' : b ∈ recursiveValueSet 7 := by simpa using hb
      rw [recursiveValueSet_seven] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values5_add_values7_mem_range_values13 i j
    · rw [recursiveValueSet_six_eq_range_values6] at ha
      have hb' : b ∈ recursiveValueSet 6 := by simpa using hb
      rw [recursiveValueSet_six_eq_range_values6] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      exact values6_add_values6_mem_range_values13 i j
    · rw [recursiveValueSet_seven] at ha
      have hb' : b ∈ recursiveValueSet 5 := by simpa using hb
      rw [recursiveValueSet_five_eq_range_values5] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with ⟨j, rfl⟩
      simpa [add_comm] using values5_add_values7_mem_range_values13 j i
    · rw [recursiveValueSet_eight] at ha
      have hb' : b ∈ recursiveValueSet 4 := by simpa using hb
      rw [recursiveValueSet_four] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl | rfl
      · simpa [add_comm] using one_add_values8_mem_range_values13 i
      · simpa [add_comm] using sqrt_two_add_values8_mem_range_values13 i
      · simpa [add_comm] using two_add_values8_mem_range_values13 i
    · rw [recursiveValueSet_nine] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · simpa [add_comm] using one_add_values9_mem_range_values13 i
      · simpa [add_comm] using two_add_values9_mem_range_values13 i
    · rw [recursiveValueSet_ten] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      simpa [add_comm] using one_add_values10_mem_range_values13 i
    · rw [recursiveValueSet_eleven] at ha
      simp [recursiveValueSet] at hb
      rcases ha with ⟨i, rfl⟩
      rcases hb with rfl
      simpa [add_comm] using one_add_values11_mem_range_values13 i

theorem recursiveValueSet_thirteen :
    recursiveValueSet 13 = Set.range values13 := by
  apply Set.Subset.antisymm
  · exact recursiveValueSet_thirteen_subset_range
  · exact values13_range_subset_recursiveValueSet_thirteen

theorem recursiveValueSet_thirteen_ncard :
    (recursiveValueSet 13).ncard = 264 := by
  rw [recursiveValueSet_thirteen, values13_range_ncard]

theorem a158415_thirteen : a158415 13 = 264 := by
  rw [a158415_eq_recursiveValueSet_ncard]
  exact recursiveValueSet_thirteen_ncard

end Expr

end A158415

end LeanProofs
