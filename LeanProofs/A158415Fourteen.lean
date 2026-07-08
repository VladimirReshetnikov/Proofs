import LeanProofs.A158415Thirteen

/-!
# Size-fourteen certificate for OEIS A158415

This module records the 455 exact representatives discovered for size 14 and
proves that this table is exactly the split-recursive value set, yielding
`a158415 14 = 455`.
-/

namespace LeanProofs

namespace A158415

namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable def values14Nat : Nat -> Real
  | 0 => Real.sqrt (values13 (0 : Fin 264))
  | 1 => Real.sqrt (values13 (1 : Fin 264))
  | 2 => Real.sqrt (values13 (2 : Fin 264))
  | 3 => Real.sqrt (values13 (3 : Fin 264))
  | 4 => Real.sqrt (values13 (4 : Fin 264))
  | 5 => Real.sqrt (values13 (5 : Fin 264))
  | 6 => Real.sqrt (values13 (6 : Fin 264))
  | 7 => Real.sqrt (values13 (7 : Fin 264))
  | 8 => Real.sqrt (values13 (8 : Fin 264))
  | 9 => Real.sqrt (values13 (9 : Fin 264))
  | 10 => Real.sqrt (values13 (10 : Fin 264))
  | 11 => Real.sqrt (values13 (11 : Fin 264))
  | 12 => Real.sqrt (values13 (12 : Fin 264))
  | 13 => Real.sqrt (values13 (13 : Fin 264))
  | 14 => Real.sqrt (values13 (14 : Fin 264))
  | 15 => Real.sqrt (values13 (15 : Fin 264))
  | 16 => Real.sqrt (values13 (16 : Fin 264))
  | 17 => Real.sqrt (values13 (17 : Fin 264))
  | 18 => Real.sqrt (values13 (18 : Fin 264))
  | 19 => Real.sqrt (values13 (19 : Fin 264))
  | 20 => Real.sqrt (values13 (20 : Fin 264))
  | 21 => Real.sqrt (values13 (21 : Fin 264))
  | 22 => Real.sqrt (values13 (22 : Fin 264))
  | 23 => Real.sqrt (values13 (23 : Fin 264))
  | 24 => Real.sqrt (values13 (24 : Fin 264))
  | 25 => Real.sqrt (values13 (25 : Fin 264))
  | 26 => Real.sqrt (values13 (26 : Fin 264))
  | 27 => Real.sqrt (values13 (27 : Fin 264))
  | 28 => Real.sqrt (values13 (28 : Fin 264))
  | 29 => Real.sqrt (values13 (29 : Fin 264))
  | 30 => Real.sqrt (values13 (30 : Fin 264))
  | 31 => Real.sqrt (values13 (31 : Fin 264))
  | 32 => Real.sqrt (values13 (32 : Fin 264))
  | 33 => Real.sqrt (values13 (33 : Fin 264))
  | 34 => Real.sqrt (values13 (34 : Fin 264))
  | 35 => Real.sqrt (values13 (35 : Fin 264))
  | 36 => Real.sqrt (values13 (36 : Fin 264))
  | 37 => Real.sqrt (values13 (37 : Fin 264))
  | 38 => Real.sqrt (values13 (38 : Fin 264))
  | 39 => Real.sqrt (values13 (39 : Fin 264))
  | 40 => Real.sqrt (values13 (40 : Fin 264))
  | 41 => Real.sqrt (values13 (41 : Fin 264))
  | 42 => Real.sqrt (values13 (42 : Fin 264))
  | 43 => Real.sqrt (values13 (43 : Fin 264))
  | 44 => Real.sqrt (values13 (44 : Fin 264))
  | 45 => Real.sqrt (values13 (45 : Fin 264))
  | 46 => Real.sqrt (values13 (46 : Fin 264))
  | 47 => Real.sqrt (values13 (47 : Fin 264))
  | 48 => Real.sqrt (values13 (48 : Fin 264))
  | 49 => Real.sqrt (values13 (49 : Fin 264))
  | 50 => Real.sqrt (values13 (50 : Fin 264))
  | 51 => Real.sqrt (values13 (51 : Fin 264))
  | 52 => Real.sqrt (values13 (52 : Fin 264))
  | 53 => Real.sqrt (values13 (53 : Fin 264))
  | 54 => Real.sqrt (values13 (54 : Fin 264))
  | 55 => Real.sqrt (values13 (55 : Fin 264))
  | 56 => Real.sqrt (values13 (56 : Fin 264))
  | 57 => Real.sqrt (values13 (57 : Fin 264))
  | 58 => Real.sqrt (values13 (58 : Fin 264))
  | 59 => Real.sqrt (values13 (59 : Fin 264))
  | 60 => Real.sqrt (values13 (60 : Fin 264))
  | 61 => Real.sqrt (values13 (61 : Fin 264))
  | 62 => Real.sqrt (values13 (62 : Fin 264))
  | 63 => Real.sqrt (values13 (63 : Fin 264))
  | 64 => Real.sqrt (values13 (64 : Fin 264))
  | 65 => Real.sqrt (values13 (65 : Fin 264))
  | 66 => Real.sqrt (values13 (66 : Fin 264))
  | 67 => Real.sqrt (values13 (67 : Fin 264))
  | 68 => Real.sqrt (values13 (68 : Fin 264))
  | 69 => Real.sqrt (values13 (69 : Fin 264))
  | 70 => Real.sqrt (values13 (70 : Fin 264))
  | 71 => Real.sqrt (values13 (71 : Fin 264))
  | 72 => Real.sqrt (values13 (72 : Fin 264))
  | 73 => Real.sqrt (values13 (73 : Fin 264))
  | 74 => Real.sqrt (values13 (74 : Fin 264))
  | 75 => Real.sqrt (values13 (75 : Fin 264))
  | 76 => Real.sqrt (values13 (76 : Fin 264))
  | 77 => Real.sqrt (values13 (77 : Fin 264))
  | 78 => Real.sqrt (values13 (78 : Fin 264))
  | 79 => Real.sqrt (values13 (79 : Fin 264))
  | 80 => Real.sqrt (values13 (80 : Fin 264))
  | 81 => Real.sqrt (values13 (81 : Fin 264))
  | 82 => Real.sqrt (values13 (82 : Fin 264))
  | 83 => Real.sqrt (values13 (83 : Fin 264))
  | 84 => Real.sqrt (values13 (84 : Fin 264))
  | 85 => Real.sqrt (values13 (85 : Fin 264))
  | 86 => Real.sqrt (values13 (86 : Fin 264))
  | 87 => Real.sqrt (values13 (87 : Fin 264))
  | 88 => Real.sqrt (values13 (88 : Fin 264))
  | 89 => Real.sqrt (values13 (89 : Fin 264))
  | 90 => Real.sqrt (values13 (90 : Fin 264))
  | 91 => Real.sqrt (values13 (91 : Fin 264))
  | 92 => Real.sqrt (values13 (92 : Fin 264))
  | 93 => Real.sqrt (values13 (93 : Fin 264))
  | 94 => Real.sqrt (values13 (94 : Fin 264))
  | 95 => Real.sqrt (values13 (95 : Fin 264))
  | 96 => Real.sqrt (values13 (96 : Fin 264))
  | 97 => Real.sqrt (values13 (97 : Fin 264))
  | 98 => Real.sqrt (values13 (98 : Fin 264))
  | 99 => Real.sqrt (values13 (99 : Fin 264))
  | 100 => Real.sqrt (values13 (100 : Fin 264))
  | 101 => Real.sqrt (values13 (101 : Fin 264))
  | 102 => Real.sqrt (values13 (102 : Fin 264))
  | 103 => Real.sqrt (values13 (103 : Fin 264))
  | 104 => Real.sqrt (values13 (104 : Fin 264))
  | 105 => Real.sqrt (values13 (105 : Fin 264))
  | 106 => Real.sqrt (values13 (106 : Fin 264))
  | 107 => Real.sqrt (values13 (107 : Fin 264))
  | 108 => Real.sqrt (values13 (108 : Fin 264))
  | 109 => Real.sqrt (values13 (109 : Fin 264))
  | 110 => Real.sqrt (values13 (110 : Fin 264))
  | 111 => Real.sqrt (values13 (111 : Fin 264))
  | 112 => Real.sqrt (values13 (112 : Fin 264))
  | 113 => Real.sqrt (values13 (113 : Fin 264))
  | 114 => Real.sqrt (values13 (114 : Fin 264))
  | 115 => Real.sqrt (values13 (115 : Fin 264))
  | 116 => Real.sqrt (values13 (116 : Fin 264))
  | 117 => Real.sqrt (values13 (117 : Fin 264))
  | 118 => Real.sqrt (values13 (118 : Fin 264))
  | 119 => Real.sqrt (values13 (119 : Fin 264))
  | 120 => Real.sqrt (values13 (120 : Fin 264))
  | 121 => Real.sqrt (values13 (121 : Fin 264))
  | 122 => Real.sqrt (values13 (122 : Fin 264))
  | 123 => Real.sqrt (values13 (123 : Fin 264))
  | 124 => Real.sqrt (values13 (124 : Fin 264))
  | 125 => Real.sqrt (values13 (125 : Fin 264))
  | 126 => Real.sqrt (values13 (126 : Fin 264))
  | 127 => Real.sqrt (values13 (127 : Fin 264))
  | 128 => Real.sqrt (values13 (128 : Fin 264))
  | 129 => Real.sqrt (values13 (129 : Fin 264))
  | 130 => Real.sqrt (values13 (130 : Fin 264))
  | 131 => Real.sqrt (values13 (131 : Fin 264))
  | 132 => Real.sqrt (values13 (132 : Fin 264))
  | 133 => Real.sqrt (values13 (133 : Fin 264))
  | 134 => Real.sqrt (values13 (134 : Fin 264))
  | 135 => Real.sqrt (values13 (135 : Fin 264))
  | 136 => Real.sqrt (values13 (136 : Fin 264))
  | 137 => Real.sqrt (values13 (137 : Fin 264))
  | 138 => Real.sqrt (values13 (138 : Fin 264))
  | 139 => Real.sqrt (values13 (139 : Fin 264))
  | 140 => Real.sqrt (values13 (140 : Fin 264))
  | 141 => Real.sqrt (values13 (141 : Fin 264))
  | 142 => Real.sqrt (values13 (142 : Fin 264))
  | 143 => Real.sqrt (values13 (143 : Fin 264))
  | 144 => Real.sqrt (values13 (144 : Fin 264))
  | 145 => Real.sqrt (values13 (145 : Fin 264))
  | 146 => Real.sqrt (values13 (146 : Fin 264))
  | 147 => Real.sqrt (values13 (147 : Fin 264))
  | 148 => Real.sqrt (values13 (148 : Fin 264))
  | 149 => Real.sqrt (values13 (149 : Fin 264))
  | 150 => Real.sqrt (values13 (150 : Fin 264))
  | 151 => Real.sqrt (values13 (151 : Fin 264))
  | 152 => Real.sqrt (values13 (152 : Fin 264))
  | 153 => Real.sqrt (values13 (153 : Fin 264))
  | 154 => Real.sqrt (values13 (154 : Fin 264))
  | 155 => Real.sqrt (values13 (155 : Fin 264))
  | 156 => Real.sqrt (values13 (156 : Fin 264))
  | 157 => Real.sqrt (values13 (157 : Fin 264))
  | 158 => Real.sqrt (values13 (158 : Fin 264))
  | 159 => Real.sqrt (values13 (159 : Fin 264))
  | 160 => Real.sqrt (values13 (160 : Fin 264))
  | 161 => Real.sqrt (values13 (161 : Fin 264))
  | 162 => Real.sqrt (values13 (162 : Fin 264))
  | 163 => Real.sqrt (values13 (163 : Fin 264))
  | 164 => Real.sqrt (values13 (164 : Fin 264))
  | 165 => Real.sqrt (values13 (165 : Fin 264))
  | 166 => Real.sqrt (values13 (166 : Fin 264))
  | 167 => Real.sqrt (values13 (167 : Fin 264))
  | 168 => Real.sqrt (values13 (168 : Fin 264))
  | 169 => Real.sqrt (values13 (169 : Fin 264))
  | 170 => Real.sqrt (values13 (170 : Fin 264))
  | 171 => Real.sqrt (values13 (171 : Fin 264))
  | 172 => Real.sqrt (values13 (172 : Fin 264))
  | 173 => Real.sqrt (values13 (173 : Fin 264))
  | 174 => Real.sqrt (values13 (174 : Fin 264))
  | 175 => Real.sqrt (values13 (175 : Fin 264))
  | 176 => Real.sqrt (values13 (176 : Fin 264))
  | 177 => Real.sqrt (values13 (177 : Fin 264))
  | 178 => Real.sqrt (values13 (178 : Fin 264))
  | 179 => Real.sqrt (values13 (179 : Fin 264))
  | 180 => Real.sqrt (values13 (180 : Fin 264))
  | 181 => Real.sqrt (values13 (181 : Fin 264))
  | 182 => Real.sqrt (values13 (182 : Fin 264))
  | 183 => Real.sqrt (values13 (183 : Fin 264))
  | 184 => Real.sqrt (values13 (184 : Fin 264))
  | 185 => Real.sqrt (values13 (185 : Fin 264))
  | 186 => Real.sqrt (values13 (186 : Fin 264))
  | 187 => Real.sqrt (values13 (187 : Fin 264))
  | 188 => Real.sqrt (values13 (188 : Fin 264))
  | 189 => Real.sqrt (values13 (189 : Fin 264))
  | 190 => Real.sqrt (values13 (190 : Fin 264))
  | 191 => Real.sqrt (values13 (191 : Fin 264))
  | 192 => Real.sqrt (values13 (192 : Fin 264))
  | 193 => Real.sqrt (values13 (193 : Fin 264))
  | 194 => Real.sqrt (values13 (194 : Fin 264))
  | 195 => Real.sqrt (values13 (195 : Fin 264))
  | 196 => Real.sqrt (values13 (196 : Fin 264))
  | 197 => Real.sqrt (values13 (197 : Fin 264))
  | 198 => Real.sqrt (values13 (198 : Fin 264))
  | 199 => Real.sqrt (values13 (199 : Fin 264))
  | 200 => Real.sqrt (values13 (200 : Fin 264))
  | 201 => Real.sqrt (values13 (201 : Fin 264))
  | 202 => Real.sqrt (values13 (202 : Fin 264))
  | 203 => Real.sqrt (values13 (203 : Fin 264))
  | 204 => Real.sqrt (values13 (204 : Fin 264))
  | 205 => Real.sqrt (values13 (205 : Fin 264))
  | 206 => Real.sqrt (values13 (206 : Fin 264))
  | 207 => Real.sqrt (values13 (207 : Fin 264))
  | 208 => Real.sqrt (values13 (208 : Fin 264))
  | 209 => Real.sqrt (values13 (209 : Fin 264))
  | 210 => Real.sqrt (values13 (210 : Fin 264))
  | 211 => Real.sqrt (values13 (211 : Fin 264))
  | 212 => Real.sqrt (values13 (212 : Fin 264))
  | 213 => Real.sqrt (values13 (213 : Fin 264))
  | 214 => Real.sqrt (values13 (214 : Fin 264))
  | 215 => Real.sqrt (values13 (215 : Fin 264))
  | 216 => Real.sqrt (values13 (216 : Fin 264))
  | 217 => Real.sqrt (values13 (217 : Fin 264))
  | 218 => Real.sqrt (values13 (218 : Fin 264))
  | 219 => Real.sqrt (values13 (219 : Fin 264))
  | 220 => Real.sqrt (values13 (220 : Fin 264))
  | 221 => Real.sqrt (values13 (221 : Fin 264))
  | 222 => Real.sqrt (values13 (222 : Fin 264))
  | 223 => Real.sqrt (values13 (223 : Fin 264))
  | 224 => Real.sqrt (values13 (224 : Fin 264))
  | 225 => Real.sqrt (values13 (225 : Fin 264))
  | 226 => Real.sqrt (values13 (226 : Fin 264))
  | 227 => Real.sqrt (values13 (227 : Fin 264))
  | 228 => Real.sqrt (values13 (228 : Fin 264))
  | 229 => Real.sqrt (values13 (229 : Fin 264))
  | 230 => Real.sqrt (values13 (230 : Fin 264))
  | 231 => Real.sqrt (values13 (231 : Fin 264))
  | 232 => Real.sqrt (values13 (232 : Fin 264))
  | 233 => Real.sqrt (values13 (233 : Fin 264))
  | 234 => Real.sqrt (values13 (234 : Fin 264))
  | 235 => Real.sqrt (values13 (235 : Fin 264))
  | 236 => Real.sqrt (values13 (236 : Fin 264))
  | 237 => Real.sqrt (values13 (237 : Fin 264))
  | 238 => Real.sqrt (values13 (238 : Fin 264))
  | 239 => Real.sqrt (values13 (239 : Fin 264))
  | 240 => Real.sqrt (values13 (240 : Fin 264))
  | 241 => Real.sqrt (values13 (241 : Fin 264))
  | 242 => Real.sqrt (values13 (242 : Fin 264))
  | 243 => Real.sqrt (values13 (243 : Fin 264))
  | 244 => Real.sqrt (values13 (244 : Fin 264))
  | 245 => Real.sqrt (values13 (245 : Fin 264))
  | 246 => Real.sqrt (values13 (246 : Fin 264))
  | 247 => Real.sqrt (values13 (247 : Fin 264))
  | 248 => Real.sqrt (values13 (248 : Fin 264))
  | 249 => Real.sqrt (values13 (249 : Fin 264))
  | 250 => 1 + values12 (1 : Fin 154)
  | 251 => 1 + values12 (2 : Fin 154)
  | 252 => 1 + values12 (3 : Fin 154)
  | 253 => 1 + values12 (4 : Fin 154)
  | 254 => 1 + values12 (5 : Fin 154)
  | 255 => Real.sqrt (values13 (250 : Fin 264))
  | 256 => 1 + values12 (6 : Fin 154)
  | 257 => 1 + values12 (7 : Fin 154)
  | 258 => 1 + values12 (8 : Fin 154)
  | 259 => Real.sqrt (values13 (251 : Fin 264))
  | 260 => 1 + values12 (9 : Fin 154)
  | 261 => 1 + values12 (10 : Fin 154)
  | 262 => 1 + values12 (11 : Fin 154)
  | 263 => Real.sqrt (values13 (252 : Fin 264))
  | 264 => 1 + values12 (12 : Fin 154)
  | 265 => Real.sqrt (values13 (253 : Fin 264))
  | 266 => 1 + values12 (13 : Fin 154)
  | 267 => 1 + values12 (14 : Fin 154)
  | 268 => 1 + values12 (15 : Fin 154)
  | 269 => 1 + values12 (16 : Fin 154)
  | 270 => 1 + values12 (17 : Fin 154)
  | 271 => Real.sqrt (values13 (254 : Fin 264))
  | 272 => 1 + values12 (18 : Fin 154)
  | 273 => 1 + values12 (19 : Fin 154)
  | 274 => 1 + values12 (20 : Fin 154)
  | 275 => 1 + values12 (21 : Fin 154)
  | 276 => Real.sqrt (values13 (255 : Fin 264))
  | 277 => 1 + values12 (22 : Fin 154)
  | 278 => 1 + values12 (23 : Fin 154)
  | 279 => 1 + values12 (24 : Fin 154)
  | 280 => 1 + values12 (25 : Fin 154)
  | 281 => 1 + values12 (26 : Fin 154)
  | 282 => Real.sqrt (values13 (256 : Fin 264))
  | 283 => values6 (1 : Fin 8) + values7 (1 : Fin 13)
  | 284 => 1 + values12 (27 : Fin 154)
  | 285 => 1 + values12 (28 : Fin 154)
  | 286 => 1 + values12 (29 : Fin 154)
  | 287 => 1 + values12 (30 : Fin 154)
  | 288 => Real.sqrt (values13 (257 : Fin 264))
  | 289 => values6 (1 : Fin 8) + values7 (2 : Fin 13)
  | 290 => 1 + values12 (31 : Fin 154)
  | 291 => 1 + values12 (32 : Fin 154)
  | 292 => 1 + values12 (33 : Fin 154)
  | 293 => Real.sqrt (values13 (258 : Fin 264))
  | 294 => 1 + values12 (34 : Fin 154)
  | 295 => 1 + values12 (35 : Fin 154)
  | 296 => values5 (1 : Fin 5) + values8 (1 : Fin 20)
  | 297 => 1 + values12 (36 : Fin 154)
  | 298 => 1 + values12 (37 : Fin 154)
  | 299 => 1 + values12 (38 : Fin 154)
  | 300 => values5 (1 : Fin 5) + values8 (2 : Fin 20)
  | 301 => 1 + values12 (39 : Fin 154)
  | 302 => Real.sqrt (values13 (259 : Fin 264))
  | 303 => 1 + values12 (40 : Fin 154)
  | 304 => 1 + values12 (41 : Fin 154)
  | 305 => 1 + values12 (42 : Fin 154)
  | 306 => 1 + values12 (43 : Fin 154)
  | 307 => Real.sqrt (values13 (260 : Fin 264))
  | 308 => values5 (1 : Fin 5) + values8 (3 : Fin 20)
  | 309 => 1 + values12 (44 : Fin 154)
  | 310 => 1 + values12 (45 : Fin 154)
  | 311 => 1 + values12 (46 : Fin 154)
  | 312 => 1 + values12 (47 : Fin 154)
  | 313 => Real.sqrt (values13 (261 : Fin 264))
  | 314 => 1 + values12 (48 : Fin 154)
  | 315 => values5 (1 : Fin 5) + values8 (4 : Fin 20)
  | 316 => 1 + values12 (49 : Fin 154)
  | 317 => values5 (1 : Fin 5) + values8 (5 : Fin 20)
  | 318 => 1 + values12 (50 : Fin 154)
  | 319 => values6 (1 : Fin 8) + values7 (4 : Fin 13)
  | 320 => 1 + values12 (51 : Fin 154)
  | 321 => 1 + values12 (52 : Fin 154)
  | 322 => 1 + values12 (53 : Fin 154)
  | 323 => Real.sqrt 2 + values9 (1 : Fin 33)
  | 324 => 1 + values12 (54 : Fin 154)
  | 325 => values5 (1 : Fin 5) + values8 (6 : Fin 20)
  | 326 => Real.sqrt 2 + values9 (2 : Fin 33)
  | 327 => 1 + values12 (55 : Fin 154)
  | 328 => 1 + values12 (56 : Fin 154)
  | 329 => 1 + values12 (57 : Fin 154)
  | 330 => Real.sqrt (values13 (262 : Fin 264))
  | 331 => 1 + values12 (58 : Fin 154)
  | 332 => Real.sqrt 2 + values9 (3 : Fin 33)
  | 333 => 1 + values12 (59 : Fin 154)
  | 334 => 1 + values12 (60 : Fin 154)
  | 335 => Real.sqrt 2 + values9 (4 : Fin 33)
  | 336 => 1 + values12 (61 : Fin 154)
  | 337 => 1 + values12 (62 : Fin 154)
  | 338 => 1 + values12 (63 : Fin 154)
  | 339 => Real.sqrt 2 + values9 (5 : Fin 33)
  | 340 => values5 (1 : Fin 5) + values8 (7 : Fin 20)
  | 341 => 1 + values12 (64 : Fin 154)
  | 342 => Real.sqrt 2 + values9 (6 : Fin 33)
  | 343 => 1 + values12 (65 : Fin 154)
  | 344 => 1 + values12 (66 : Fin 154)
  | 345 => Real.sqrt 2 + values9 (7 : Fin 33)
  | 346 => 1 + values12 (67 : Fin 154)
  | 347 => 1 + values12 (68 : Fin 154)
  | 348 => 1 + values12 (69 : Fin 154)
  | 349 => 1 + values12 (70 : Fin 154)
  | 350 => Real.sqrt 2 + values9 (8 : Fin 33)
  | 351 => 1 + values12 (71 : Fin 154)
  | 352 => 1 + values12 (72 : Fin 154)
  | 353 => Real.sqrt 2 + values9 (9 : Fin 33)
  | 354 => values6 (1 : Fin 8) + values7 (6 : Fin 13)
  | 355 => Real.sqrt (values13 (263 : Fin 264))
  | 356 => 1 + values12 (73 : Fin 154)
  | 357 => Real.sqrt 2 + values9 (10 : Fin 33)
  | 358 => values5 (1 : Fin 5) + values8 (9 : Fin 20)
  | 359 => 1 + values12 (74 : Fin 154)
  | 360 => 1 + values12 (75 : Fin 154)
  | 361 => Real.sqrt 2 + values9 (11 : Fin 33)
  | 362 => 1 + values12 (76 : Fin 154)
  | 363 => values5 (1 : Fin 5) + values8 (10 : Fin 20)
  | 364 => 1 + values12 (77 : Fin 154)
  | 365 => 1 + values12 (78 : Fin 154)
  | 366 => 1 + values12 (79 : Fin 154)
  | 367 => values6 (4 : Fin 8) + values7 (1 : Fin 13)
  | 368 => 1 + values12 (80 : Fin 154)
  | 369 => 1 + values12 (81 : Fin 154)
  | 370 => values6 (1 : Fin 8) + values7 (7 : Fin 13)
  | 371 => Real.sqrt 2 + values9 (12 : Fin 33)
  | 372 => 1 + values12 (82 : Fin 154)
  | 373 => Real.sqrt 2 + values9 (13 : Fin 33)
  | 374 => 1 + values12 (83 : Fin 154)
  | 375 => Real.sqrt 2 + values9 (14 : Fin 33)
  | 376 => values5 (1 : Fin 5) + values8 (11 : Fin 20)
  | 377 => 1 + values12 (84 : Fin 154)
  | 378 => 1 + values12 (85 : Fin 154)
  | 379 => Real.sqrt 2 + values9 (15 : Fin 33)
  | 380 => 1 + values12 (86 : Fin 154)
  | 381 => 1 + values12 (87 : Fin 154)
  | 382 => 1 + values12 (88 : Fin 154)
  | 383 => 1 + values12 (89 : Fin 154)
  | 384 => 1 + values12 (90 : Fin 154)
  | 385 => 1 + values12 (91 : Fin 154)
  | 386 => 1 + values12 (92 : Fin 154)
  | 387 => values6 (4 : Fin 8) + values7 (4 : Fin 13)
  | 388 => 1 + values12 (93 : Fin 154)
  | 389 => Real.sqrt 2 + values9 (16 : Fin 33)
  | 390 => 1 + values12 (94 : Fin 154)
  | 391 => 1 + values12 (95 : Fin 154)
  | 392 => 1 + values12 (96 : Fin 154)
  | 393 => 1 + values12 (97 : Fin 154)
  | 394 => 1 + values12 (98 : Fin 154)
  | 395 => Real.sqrt 2 + values9 (17 : Fin 33)
  | 396 => 1 + values12 (99 : Fin 154)
  | 397 => 1 + values12 (100 : Fin 154)
  | 398 => 1 + values12 (101 : Fin 154)
  | 399 => 1 + values12 (102 : Fin 154)
  | 400 => 1 + values12 (103 : Fin 154)
  | 401 => 1 + values12 (104 : Fin 154)
  | 402 => Real.sqrt 2 + values9 (18 : Fin 33)
  | 403 => 1 + values12 (105 : Fin 154)
  | 404 => 1 + values12 (106 : Fin 154)
  | 405 => values6 (4 : Fin 8) + values7 (6 : Fin 13)
  | 406 => 1 + values12 (107 : Fin 154)
  | 407 => 1 + values12 (108 : Fin 154)
  | 408 => 1 + values12 (109 : Fin 154)
  | 409 => 1 + values12 (110 : Fin 154)
  | 410 => 1 + values12 (111 : Fin 154)
  | 411 => 1 + values12 (112 : Fin 154)
  | 412 => 1 + values12 (113 : Fin 154)
  | 413 => 1 + values12 (114 : Fin 154)
  | 414 => values6 (4 : Fin 8) + values7 (7 : Fin 13)
  | 415 => 1 + values12 (115 : Fin 154)
  | 416 => 1 + values12 (116 : Fin 154)
  | 417 => 1 + values12 (117 : Fin 154)
  | 418 => 1 + values12 (118 : Fin 154)
  | 419 => 1 + values12 (119 : Fin 154)
  | 420 => 1 + values12 (120 : Fin 154)
  | 421 => 1 + values12 (121 : Fin 154)
  | 422 => 1 + values12 (122 : Fin 154)
  | 423 => 1 + values12 (123 : Fin 154)
  | 424 => 1 + values12 (124 : Fin 154)
  | 425 => 1 + values12 (125 : Fin 154)
  | 426 => 1 + values12 (126 : Fin 154)
  | 427 => 1 + values12 (127 : Fin 154)
  | 428 => 1 + values12 (128 : Fin 154)
  | 429 => 1 + values12 (129 : Fin 154)
  | 430 => 1 + values12 (130 : Fin 154)
  | 431 => 1 + values12 (131 : Fin 154)
  | 432 => 1 + values12 (132 : Fin 154)
  | 433 => 1 + values12 (133 : Fin 154)
  | 434 => 1 + values12 (134 : Fin 154)
  | 435 => 1 + values12 (135 : Fin 154)
  | 436 => 1 + values12 (136 : Fin 154)
  | 437 => 1 + values12 (137 : Fin 154)
  | 438 => Real.sqrt 2 + values9 (27 : Fin 33)
  | 439 => 1 + values12 (138 : Fin 154)
  | 440 => 1 + values12 (139 : Fin 154)
  | 441 => 1 + values12 (140 : Fin 154)
  | 442 => 1 + values12 (141 : Fin 154)
  | 443 => 1 + values12 (142 : Fin 154)
  | 444 => 1 + values12 (143 : Fin 154)
  | 445 => 1 + values12 (144 : Fin 154)
  | 446 => 1 + values12 (145 : Fin 154)
  | 447 => 1 + values12 (146 : Fin 154)
  | 448 => 1 + values12 (147 : Fin 154)
  | 449 => 1 + values12 (148 : Fin 154)
  | 450 => 1 + values12 (149 : Fin 154)
  | 451 => 1 + values12 (150 : Fin 154)
  | 452 => 1 + values12 (151 : Fin 154)
  | 453 => 1 + values12 (152 : Fin 154)
  | 454 => 1 + values12 (153 : Fin 154)
  | _ => 0
noncomputable def values14 (i : Fin 455) : ℝ :=
  values14Nat i.1

theorem values13_nonneg (i : Fin 264) : (0 : ℝ) ≤ values13 i := by
  have h0 : (0 : ℝ) ≤ values13 (0 : Fin 264) := by
    change (0 : ℝ) ≤ Real.sqrt (values12 (0 : Fin 154))
    exact Real.sqrt_nonneg _
  exact h0.trans (values13_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values13_strictMono :
    StrictMono fun i : Fin 264 => Real.sqrt (values13 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values13_nonneg i) (values13_strictMono hij)
set_option linter.unusedTactic false in
theorem values14_special_249 :
    values14 (249 : Fin 455) < values14 (250 : Fin 455) := by
  have hleft : values14 (249 : Fin 455) < (2001 / 1000 : Real) := by
    rw [show values14 (249 : Fin 455) = Real.sqrt (values13 (249 : Fin 264)) by rfl]
    change Real.sqrt (values13 (249 : Fin 264)) < (2001 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2001 / 1000 : Real))]
    norm_num
    change values13 (249 : Fin 264) < (4004001 / 1000000 : Real)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    change 1 + values11 (76 : Fin 91) < (4004001 / 1000000 : Real)
    have h1 : 1 < (1001 / 1000 : Real) := by
      norm_num
    have h2 : values11 (76 : Fin 91) < (3001 / 1000 : Real) := by
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (19 : Fin 33) < (3001 / 1000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (19 : Fin 33) < (20001 / 10000 : Real) := by
        rw [show values9 (19 : Fin 33) = Real.sqrt (values8 (19 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (19 : Fin 20)) < (20001 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (20001 / 10000 : Real))]
        norm_num
        change values8 (19 : Fin 20) < (400040001 / 100000000 : Real)
        rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (7 : Fin 8) < (400040001 / 100000000 : Real)
        have h5 : 1 < (10001 / 10000 : Real) := by
          norm_num
        have h6 : values6 (7 : Fin 8) < (30001 / 10000 : Real) := by
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (30001 / 10000 : Real)
          have h7 : 1 < (100001 / 100000 : Real) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2001 / 1000 : Real) < values14 (250 : Fin 455) := by
    rw [show values14 (250 : Fin 455) = 1 + values12 (1 : Fin 154) by rfl]
    change (2001 / 1000 : Real) < 1 + values12 (1 : Fin 154)
    have h9 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h10 : (10013 / 10000 : Real) < values12 (1 : Fin 154) := by
      rw [show values12 (1 : Fin 154) = Real.sqrt (values11 (1 : Fin 91)) by a158415_twelve_table]
      change (10013 / 10000 : Real) < Real.sqrt (values11 (1 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (100260169 / 100000000 : Real) < values11 (1 : Fin 91)
      rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by a158415_twelve_table]
      change (100260169 / 100000000 : Real) < Real.sqrt (values10 (1 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10052101487908561 / 10000000000000000 : Real) < values10 (1 : Fin 54)
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by a158415_twelve_table]
      change (10052101487908561 / 10000000000000000 : Real) < Real.sqrt (values9 (1 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (101044744323213505928085897090721 / 100000000000000000000000000000000 : Real) < values9 (1 : Fin 33)
      rw [show values9 (1 : Fin 33) = Real.sqrt (values8 (1 : Fin 20)) by a158415_twelve_table]
      change (101044744323213505928085897090721 / 100000000000000000000000000000000 : Real) < Real.sqrt (values8 (1 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10210040355343588032158814177409313781713907152898370331704299841 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < values8 (1 : Fin 20)
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (10210040355343588032158814177409313781713907152898370331704299841 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (104244924057744621372791113776433212453678058096036347484184264323599978017937094158594971112458510906171219388060873008032625281 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (104244924057744621372791113776433212453678058096036347484184264323599978017937094158594971112458510906171219388060873008032625281 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10867004191804943336165211944486270739968289053951599015388702491954699567670845685334573127582495648935157298152203690290752947233079860217186284751331778645759114672650883826592718356133005163710443026534757798407673356665465064399236117983694904960328961 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (10867004191804943336165211944486270739968289053951599015388702491954699567670845685334573127582495648935157298152203690290752947233079860217186284751331778645759114672650883826592718356133005163710443026534757798407673356665465064399236117983694904960328961 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (118091780104706209696897693912707908349903082850642364078118593434674159509301594851406520026906836543280353300862895632540018223001231814569452248006884085500727508698290549064802796120674315978668758138179569450478058176486688958167433661666700298255733088449227196990967629327056382151102815182065202835304598765986991359607440067482419644444119883046658780755950650136635626923980497139626037689591208667017904150291677643450936519925697186135270622890741220184104464215449291584220909479501120861201335339521 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (118091780104706209696897693912707908349903082850642364078118593434674159509301594851406520026906836543280353300862895632540018223001231814569452248006884085500727508698290549064802796120674315978668758138179569450478058176486688958167433661666700298255733088449227196990967629327056382151102815182065202835304598765986991359607440067482419644444119883046658780755950650136635626923980497139626037689591208667017904150291677643450936519925697186135270622890741220184104464215449291584220909479501120861201335339521 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (13945668528298285371283208653184395700784275558765577737035034203285265788195688196913573758068103837053101346998825609214205276038687559034192304371872943907249443528872226085299467928431065958759540136261519005379168677221254869014546450034718072497468988508270838349269402480650384821960711325395235993964580155076822291490486947104885166952044984411287045298420185833946505638243929090785662101407855012735606555864862089883657478725508458913841158771671929166067019569281657675683705259559690890903278975543031326352392102929791140703065678478729420894088423182717757562741495500119575650424732472279481354439400093964451269833306976777128616271918897277716336408387679363859939704679437705284593690441674413643498817692994305739795800703741416317779626697867286654497390681954219924239497595590329432002097269690441227897419695225327717655208897069308889022574229276478977898905608760576723248274853734735859426241477038874428253619116936020235986349818413914942108331260279815226294507974912437539517614102036344509441 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt 2
      change (13945668528298285371283208653184395700784275558765577737035034203285265788195688196913573758068103837053101346998825609214205276038687559034192304371872943907249443528872226085299467928431065958759540136261519005379168677221254869014546450034718072497468988508270838349269402480650384821960711325395235993964580155076822291490486947104885166952044984411287045298420185833946505638243929090785662101407855012735606555864862089883657478725508458913841158771671929166067019569281657675683705259559690890903278975543031326352392102929791140703065678478729420894088423182717757562741495500119575650424732472279481354439400093964451269833306976777128616271918897277716336408387679363859939704679437705284593690441674413643498817692994305739795800703741416317779626697867286654497390681954219924239497595590329432002097269690441227897419695225327717655208897069308889022574229276478977898905608760576723248274853734735859426241477038874428253619116936020235986349818413914942108331260279815226294507974912437539517614102036344509441 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_254 :
    values14 (254 : Fin 455) < values14 (255 : Fin 455) := by
  have hleft : values14 (254 : Fin 455) < (2011 / 1000 : Real) := by
    rw [show values14 (254 : Fin 455) = 1 + values12 (5 : Fin 154) by rfl]
    change 1 + values12 (5 : Fin 154) < (2011 / 1000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (5 : Fin 154) < (10109 / 10000 : Real) := by
      rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (5 : Fin 91)) < (10109 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10109 / 10000 : Real))]
      norm_num
      change values11 (5 : Fin 91) < (102191881 / 100000000 : Real)
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (5 : Fin 54)) < (102191881 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (102191881 / 100000000 : Real))]
      norm_num
      change values10 (5 : Fin 54) < (10443180542318161 / 10000000000000000 : Real)
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (5 : Fin 33)) < (10443180542318161 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443180542318161 / 10000000000000000 : Real))]
      norm_num
      change values9 (5 : Fin 33) < (109060019839452639292947750421921 / 100000000000000000000000000000000 : Real)
      rw [show values9 (5 : Fin 33) = Real.sqrt (values8 (5 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (5 : Fin 20)) < (109060019839452639292947750421921 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109060019839452639292947750421921 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values8 (5 : Fin 20) < (11894087927381803286458790069939770000406278276302115433517330241 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (11894087927381803286458790069939770000406278276302115433517330241 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11894087927381803286458790069939770000406278276302115433517330241 / 10000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change values7 (5 : Fin 13) < (141469327624289561049062608857346940866763035427088738575107045262535976742706645639636534190225240828041653420795049284253118081 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (141469327624289561049062608857346940866763035427088738575107045262535976742706645639636534190225240828041653420795049284253118081 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141469327624289561049062608857346940866763035427088738575107045262535976742706645639636534190225240828041653420795049284253118081 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change values6 (5 : Fin 8) < (20013570658468577499210058546657491552402332845392731081142144604389299248248468842899591537279827104584814721964238969654628145094060296830525412573717372550863520700755295822089164955226087411356320122485227708963267580439914527866369394197076770929122561 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20013570658468577499210058546657491552402332845392731081142144604389299248248468842899591537279827104584814721964238969654628145094060296830525412573717372550863520700755295822089164955226087411356320122485227708963267580439914527866369394197076770929122561 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2011 / 1000 : Real) < values14 (255 : Fin 455) := by
    rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    change (2011 / 1000 : Real) < Real.sqrt (values13 (250 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (4044121 / 1000000 : Real) < values13 (250 : Fin 264)
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    change (4044121 / 1000000 : Real) < 1 + values11 (77 : Fin 91)
    have h5 : (99999 / 100000 : Real) < 1 := by
      norm_num
    have h6 : (304427 / 100000 : Real) < values11 (77 : Fin 91) := by
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by a158415_twelve_table]
      change (304427 / 100000 : Real) < 1 + values9 (20 : Fin 33)
      have h7 : (999999 / 1000000 : Real) < 1 := by
        norm_num
      have h8 : (2044273 / 1000000 : Real) < values9 (20 : Fin 33) := by
        rw [show values9 (20 : Fin 33) = 1 + values7 (1 : Fin 13) by a158415_twelve_table]
        change (2044273 / 1000000 : Real) < 1 + values7 (1 : Fin 13)
        have h9 : (9999999 / 10000000 : Real) < 1 := by
          norm_num
        have h10 : (10442737 / 10000000 : Real) < values7 (1 : Fin 13) := by
          rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
          change (10442737 / 10000000 : Real) < Real.sqrt (values6 (1 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (109050756051169 / 100000000000000 : Real) < values6 (1 : Fin 8)
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change (109050756051169 / 100000000000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (11892067395331572270146266561 / 10000000000000000000000000000 : Real) < values5 (1 : Fin 5)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (11892067395331572270146266561 / 10000000000000000000000000000 : Real) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (141421266935108245590895037072423705961333120846866766721 / 100000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt 2
          change (141421266935108245590895037072423705961333120846866766721 / 100000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_255 :
    values14 (255 : Fin 455) < values14 (256 : Fin 455) := by
  have hleft : values14 (255 : Fin 455) < (503 / 250 : Real) := by
    rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    change Real.sqrt (values13 (250 : Fin 264)) < (503 / 250 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (503 / 250 : Real))]
    norm_num
    change values13 (250 : Fin 264) < (253009 / 62500 : Real)
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    change 1 + values11 (77 : Fin 91) < (253009 / 62500 : Real)
    have h1 : 1 < (1001 / 1000 : Real) := by
      norm_num
    have h2 : values11 (77 : Fin 91) < (609 / 200 : Real) := by
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (20 : Fin 33) < (609 / 200 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (20 : Fin 33) < (20443 / 10000 : Real) := by
        rw [show values9 (20 : Fin 33) = 1 + values7 (1 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (1 : Fin 13) < (20443 / 10000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (1 : Fin 13) < (26107 / 25000 : Real) := by
          rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (1 : Fin 8)) < (26107 / 25000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (26107 / 25000 : Real))]
          norm_num
          change values6 (1 : Fin 8) < (681575449 / 625000000 : Real)
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (1 : Fin 5)) < (681575449 / 625000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (681575449 / 625000000 : Real))]
          norm_num
          change values5 (1 : Fin 5) < (464545092679551601 / 390625000000000000 : Real)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (464545092679551601 / 390625000000000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (464545092679551601 / 390625000000000000 : Real))]
          norm_num
          change Real.sqrt 2 < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
          change Real.sqrt (2) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (503 / 250 : Real) < values14 (256 : Fin 455) := by
    rw [show values14 (256 : Fin 455) = 1 + values12 (6 : Fin 154) by rfl]
    change (503 / 250 : Real) < 1 + values12 (6 : Fin 154)
    have h7 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h8 : (5069 / 5000 : Real) < values12 (6 : Fin 154) := by
      rw [show values12 (6 : Fin 154) = Real.sqrt (values11 (6 : Fin 91)) by a158415_twelve_table]
      change (5069 / 5000 : Real) < Real.sqrt (values11 (6 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (25694761 / 25000000 : Real) < values11 (6 : Fin 91)
      rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by a158415_twelve_table]
      change (25694761 / 25000000 : Real) < Real.sqrt (values10 (6 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (660220742847121 / 625000000000000 : Real) < values10 (6 : Fin 54)
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by a158415_twelve_table]
      change (660220742847121 / 625000000000000 : Real) < Real.sqrt (values9 (6 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (435891429285604275085177988641 / 390625000000000000000000000000 : Real) < values9 (6 : Fin 33)
      rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
      change (435891429285604275085177988641 / 390625000000000000000000000000 : Real) < Real.sqrt (values8 (6 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (190001338124646952272344462323072536368797370298926325026881 / 152587890625000000000000000000000000000000000000000000000000 : Real) < values8 (6 : Fin 20)
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (190001338124646952272344462323072536368797370298926325026881 / 152587890625000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (36100508489156419434272039187332858681721491639957879976860513065799707288811995112636810757146732000016502085372588161 / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (36100508489156419434272039187332858681721491639957879976860513065799707288811995112636810757146732000016502085372588161 / 23283064365386962890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1303246713175654705350589123474719037003738972932722401329541645335556652247424987929990062102744837934582634606001483356187262468125554855525359854572625430400767995700727800681522131903926997827373819693349284901348188144453307717361921 / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (1303246713175654705350589123474719037003738972932722401329541645335556652247424987929990062102744837934582634606001483356187262468125554855525359854572625430400767995700727800681522131903926997827373819693349284901348188144453307717361921 / 542101086242752217003726400434970855712890625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < 1 + Real.sqrt 2
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_258 :
    values14 (258 : Fin 455) < values14 (259 : Fin 455) := by
  have hleft : values14 (258 : Fin 455) < (1011 / 500 : Real) := by
    rw [show values14 (258 : Fin 455) = 1 + values12 (8 : Fin 154) by rfl]
    change 1 + values12 (8 : Fin 154) < (1011 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (8 : Fin 154) < (10219 / 10000 : Real) := by
      rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (8 : Fin 91)) < (10219 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10219 / 10000 : Real))]
      norm_num
      change values11 (8 : Fin 91) < (104427961 / 100000000 : Real)
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (8 : Fin 54)) < (104427961 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (104427961 / 100000000 : Real))]
      norm_num
      change values10 (8 : Fin 54) < (10905199038617521 / 10000000000000000 : Real)
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (8 : Fin 33)) < (10905199038617521 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10905199038617521 / 10000000000000000 : Real))]
      norm_num
      change values9 (8 : Fin 33) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real)
      rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (8 : Fin 20)) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values8 (8 : Fin 20) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (8 : Fin 13)) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change values7 (8 : Fin 13) < (200017858355834144152057285593529953526086114939832688773440502100850437168712195190982786797967106432267261395823796759254399361 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (0 : Fin 5) < (200017858355834144152057285593529953526086114939832688773440502100850437168712195190982786797967106432267261395823796759254399361 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (0 : Fin 5) < (100001 / 100000 : Real) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change Real.sqrt (1) < (100001 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (100001 / 100000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (1011 / 500 : Real) < values14 (259 : Fin 455) := by
    rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    change (1011 / 500 : Real) < Real.sqrt (values13 (251 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1022121 / 250000 : Real) < values13 (251 : Fin 264)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    change (1022121 / 250000 : Real) < 1 + values11 (78 : Fin 91)
    have h5 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h6 : (309 / 100 : Real) < values11 (78 : Fin 91) := by
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by a158415_twelve_table]
      change (309 / 100 : Real) < 1 + values9 (21 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (4181 / 2000 : Real) < values9 (21 : Fin 33) := by
        rw [show values9 (21 : Fin 33) = 1 + values7 (2 : Fin 13) by a158415_twelve_table]
        change (4181 / 2000 : Real) < 1 + values7 (2 : Fin 13)
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (1090507 / 1000000 : Real) < values7 (2 : Fin 13) := by
          rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
          change (1090507 / 1000000 : Real) < Real.sqrt (values6 (2 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1189205517049 / 1000000000000 : Real) < values6 (2 : Fin 8)
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change (1189205517049 / 1000000000000 : Real) < Real.sqrt (values5 (2 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1414209761779779429668401 / 1000000000000000000000000 : Real) < values5 (2 : Fin 5)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (1414209761779779429668401 / 1000000000000000000000000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_259 :
    values14 (259 : Fin 455) < values14 (260 : Fin 455) := by
  have hleft : values14 (259 : Fin 455) < (2023 / 1000 : Real) := by
    rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    change Real.sqrt (values13 (251 : Fin 264)) < (2023 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2023 / 1000 : Real))]
    norm_num
    change values13 (251 : Fin 264) < (4092529 / 1000000 : Real)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    change 1 + values11 (78 : Fin 91) < (4092529 / 1000000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (78 : Fin 91) < (3091 / 1000 : Real) := by
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (21 : Fin 33) < (3091 / 1000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (21 : Fin 33) < (10453 / 5000 : Real) := by
        rw [show values9 (21 : Fin 33) = 1 + values7 (2 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (2 : Fin 13) < (10453 / 5000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values7 (2 : Fin 13) < (109051 / 100000 : Real) := by
          rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (2 : Fin 8)) < (109051 / 100000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109051 / 100000 : Real))]
          norm_num
          change values6 (2 : Fin 8) < (11892120601 / 10000000000 : Real)
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (2 : Fin 5)) < (11892120601 / 10000000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11892120601 / 10000000000 : Real))]
          norm_num
          change values5 (2 : Fin 5) < (141422532388728601201 / 100000000000000000000 : Real)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (141422532388728601201 / 100000000000000000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141422532388728601201 / 100000000000000000000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2023 / 1000 : Real) < values14 (260 : Fin 455) := by
    rw [show values14 (260 : Fin 455) = 1 + values12 (9 : Fin 154) by rfl]
    change (2023 / 1000 : Real) < 1 + values12 (9 : Fin 154)
    have h7 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h8 : (10247 / 10000 : Real) < values12 (9 : Fin 154) := by
      rw [show values12 (9 : Fin 154) = Real.sqrt (values11 (9 : Fin 91)) by a158415_twelve_table]
      change (10247 / 10000 : Real) < Real.sqrt (values11 (9 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (105001009 / 100000000 : Real) < values11 (9 : Fin 91)
      rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by a158415_twelve_table]
      change (105001009 / 100000000 : Real) < Real.sqrt (values10 (9 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11025211891018081 / 10000000000000000 : Real) < values10 (9 : Fin 54)
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by a158415_twelve_table]
      change (11025211891018081 / 10000000000000000 : Real) < Real.sqrt (values9 (9 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (121555297241846489593402668922561 / 100000000000000000000000000000000 : Real) < values9 (9 : Fin 33)
      rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
      change (121555297241846489593402668922561 / 100000000000000000000000000000000 : Real) < Real.sqrt (values8 (9 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (14775690287553652800356665851600970147662308961076542436614798721 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < values8 (9 : Fin 20)
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (14775690287553652800356665851600970147662308961076542436614798721 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (218321023473707346978507206941752854116115602283981005169639738004216496726055626222728909685808934114862208241888026179343235841 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (218321023473707346978507206941752854116115602283981005169639738004216496726055626222728909685808934114862208241888026179343235841 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < 1 + values5 (1 : Fin 5)
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_262 :
    values14 (262 : Fin 455) < values14 (263 : Fin 455) := by
  have hleft : values14 (262 : Fin 455) < (407 / 200 : Real) := by
    rw [show values14 (262 : Fin 455) = 1 + values12 (11 : Fin 154) by rfl]
    change 1 + values12 (11 : Fin 154) < (407 / 200 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (11 : Fin 154) < (103493 / 100000 : Real) := by
      rw [show values12 (11 : Fin 154) = Real.sqrt (values11 (11 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (11 : Fin 91)) < (103493 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (103493 / 100000 : Real))]
      norm_num
      change values11 (11 : Fin 91) < (10710801049 / 10000000000 : Real)
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (11 : Fin 54)) < (10710801049 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10710801049 / 10000000000 : Real))]
      norm_num
      change values10 (11 : Fin 54) < (114721259111259500401 / 100000000000000000000 : Real)
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (11 : Fin 33)) < (114721259111259500401 / 100000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (114721259111259500401 / 100000000000000000000 : Real))]
      norm_num
      change values9 (11 : Fin 33) < (13160967292072740935806126147480119160801 / 10000000000000000000000000000000000000000 : Real)
      rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (11 : Fin 20)) < (13160967292072740935806126147480119160801 / 10000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13160967292072740935806126147480119160801 / 10000000000000000000000000000000000000000 : Real))]
      norm_num
      change values8 (11 : Fin 20) < (173211060063008495417873087004165583956170041930771299005495281536062256494961601 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (11 : Fin 13)) < (173211060063008495417873087004165583956170041930771299005495281536062256494961601 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211060063008495417873087004165583956170041930771299005495281536062256494961601 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change values7 (11 : Fin 13) < (30002071328151136564639951185751624226025394200286467102789402885539639456011560957877365247516044153522160471649628407725061389009919001879763175850698464483201 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (3 : Fin 5) < (30002071328151136564639951185751624226025394200286467102789402885539639456011560957877365247516044153522160471649628407725061389009919001879763175850698464483201 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (3 : Fin 5) < (200001 / 100000 : Real) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (407 / 200 : Real) < values14 (263 : Fin 455) := by
    rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    change (407 / 200 : Real) < Real.sqrt (values13 (252 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (165649 / 40000 : Real) < values13 (252 : Fin 264)
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    change (165649 / 40000 : Real) < 1 + values11 (79 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (1573 / 500 : Real) < values11 (79 : Fin 91) := by
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by a158415_twelve_table]
      change (1573 / 500 : Real) < Real.sqrt 2 + values6 (4 : Fin 8)
      have h9 : (7071 / 5000 : Real) < Real.sqrt 2 := by
        change (7071 / 5000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h10 : (433 / 250 : Real) < values6 (4 : Fin 8) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (433 / 250 : Real) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : Real) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (187489 / 62500 : Real) < 1 + 2
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_263 :
    values14 (263 : Fin 455) < values14 (264 : Fin 455) := by
  have hleft : values14 (263 : Fin 455) < (2037 / 1000 : Real) := by
    rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    change Real.sqrt (values13 (252 : Fin 264)) < (2037 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2037 / 1000 : Real))]
    norm_num
    change values13 (252 : Fin 264) < (4149369 / 1000000 : Real)
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    change 1 + values11 (79 : Fin 91) < (4149369 / 1000000 : Real)
    have h1 : 1 < (1001 / 1000 : Real) := by
      norm_num
    have h2 : values11 (79 : Fin 91) < (3147 / 1000 : Real) := by
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by a158415_twelve_table]
      change Real.sqrt 2 + values6 (4 : Fin 8) < (3147 / 1000 : Real)
      have h3 : Real.sqrt 2 < (14143 / 10000 : Real) := by
        change Real.sqrt (2) < (14143 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
        norm_num
      have h4 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
        norm_num
        change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (300017041 / 100000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (2037 / 1000 : Real) < values14 (264 : Fin 455) := by
    rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    change (2037 / 1000 : Real) < 1 + values12 (12 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (261 / 250 : Real) < values12 (12 : Fin 154) := by
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by a158415_twelve_table]
      change (261 / 250 : Real) < Real.sqrt (values11 (12 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : Real) < values11 (12 : Fin 91)
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by a158415_twelve_table]
      change (68121 / 62500 : Real) < Real.sqrt (values10 (12 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : Real) < values10 (12 : Fin 54)
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by a158415_twelve_table]
      change (4640470641 / 3906250000 : Real) < Real.sqrt (values9 (12 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : Real) < values9 (12 : Fin 33)
      rw [show values9 (12 : Fin 33) = Real.sqrt (values8 (12 : Fin 20)) by a158415_twelve_table]
      change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt (values8 (12 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < values8 (12 : Fin 20)
      rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
      change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < Real.sqrt (values7 (12 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (215028603706253369351700249785656905921075116297105851816893540862484669697921 / 54210108624275221700372640043497085571289062500000000000000000000000000000000 : Real) < values7 (12 : Fin 13)
      rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
      change (215028603706253369351700249785656905921075116297105851816893540862484669697921 / 54210108624275221700372640043497085571289062500000000000000000000000000000000 : Real) < 1 + values5 (4 : Fin 5)
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (2999 / 1000 : Real) < values5 (4 : Fin 5) := by
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (2999 / 1000 : Real) < 1 + 2
        have h11 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h12 : (19999 / 10000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_264 :
    values14 (264 : Fin 455) < values14 (265 : Fin 455) := by
  have hleft : values14 (264 : Fin 455) < (409 / 200 : Real) := by
    rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    change 1 + values12 (12 : Fin 154) < (409 / 200 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (12 : Fin 154) < (10443 / 10000 : Real) := by
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (12 : Fin 91)) < (10443 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443 / 10000 : Real))]
      norm_num
      change values11 (12 : Fin 91) < (109056249 / 100000000 : Real)
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (12 : Fin 54)) < (109056249 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109056249 / 100000000 : Real))]
      norm_num
      change values10 (12 : Fin 54) < (11893265445950001 / 10000000000000000 : Real)
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (12 : Fin 33)) < (11893265445950001 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893265445950001 / 10000000000000000 : Real))]
      norm_num
      change values9 (12 : Fin 33) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [show values9 (12 : Fin 33) = Real.sqrt (values8 (12 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (12 : Fin 20)) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values8 (12 : Fin 20) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (12 : Fin 13)) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change values7 (12 : Fin 13) < (400321482314546872543502305991575931282447972798696901706233454547339106491559864049750473213354154184072744237574545393567600001 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (4 : Fin 5) < (400321482314546872543502305991575931282447972798696901706233454547339106491559864049750473213354154184072744237574545393567600001 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (1001 / 1000 : Real) := by
        norm_num
      have h4 : values5 (4 : Fin 5) < (3001 / 1000 : Real) := by
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (3001 / 1000 : Real)
        have h5 : 1 < (10001 / 10000 : Real) := by
          norm_num
        have h6 : 2 < (20001 / 10000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (409 / 200 : Real) < values14 (265 : Fin 455) := by
    rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    change (409 / 200 : Real) < Real.sqrt (values13 (253 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (167281 / 40000 : Real) < values13 (253 : Fin 264)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    change (167281 / 40000 : Real) < 1 + values11 (80 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (3189 / 1000 : Real) < values11 (80 : Fin 91) := by
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by a158415_twelve_table]
      change (3189 / 1000 : Real) < 1 + values9 (22 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (5473 / 2500 : Real) < values9 (22 : Fin 33) := by
        rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
        change (5473 / 2500 : Real) < 1 + values7 (3 : Fin 13)
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (1189207 / 1000000 : Real) < values7 (3 : Fin 13) := by
          rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
          change (1189207 / 1000000 : Real) < Real.sqrt (values6 (3 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1414213288849 / 1000000000000 : Real) < values6 (3 : Fin 8)
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (1414213288849 / 1000000000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1999999226357105107744801 / 1000000000000000000000000 : Real) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (1999999226357105107744801 / 1000000000000000000000000 : Real) < 1 + 1
          have h13 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          have h14 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_265 :
    values14 (265 : Fin 455) < values14 (266 : Fin 455) := by
  have hleft : values14 (265 : Fin 455) < (2047 / 1000 : Real) := by
    rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    change Real.sqrt (values13 (253 : Fin 264)) < (2047 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2047 / 1000 : Real))]
    norm_num
    change values13 (253 : Fin 264) < (4190209 / 1000000 : Real)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    change 1 + values11 (80 : Fin 91) < (4190209 / 1000000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (80 : Fin 91) < (31893 / 10000 : Real) := by
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (22 : Fin 33) < (31893 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (22 : Fin 33) < (218921 / 100000 : Real) := by
        rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (3 : Fin 13) < (218921 / 100000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values7 (3 : Fin 13) < (148651 / 125000 : Real) := by
          rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (3 : Fin 8)) < (148651 / 125000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (148651 / 125000 : Real))]
          norm_num
          change values6 (3 : Fin 8) < (22097119801 / 15625000000 : Real)
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (22097119801 / 15625000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (22097119801 / 15625000000 : Real))]
          norm_num
          change values5 (3 : Fin 5) < (488282703499746279601 / 244140625000000000000 : Real)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (488282703499746279601 / 244140625000000000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2047 / 1000 : Real) < values14 (266 : Fin 455) := by
    rw [show values14 (266 : Fin 455) = 1 + values12 (13 : Fin 154) by rfl]
    change (2047 / 1000 : Real) < 1 + values12 (13 : Fin 154)
    have h9 : (99999 / 100000 : Real) < 1 := by
      norm_num
    have h10 : (26179 / 25000 : Real) < values12 (13 : Fin 154) := by
      rw [show values12 (13 : Fin 154) = Real.sqrt (values11 (13 : Fin 91)) by a158415_twelve_table]
      change (26179 / 25000 : Real) < Real.sqrt (values11 (13 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (685340041 / 625000000 : Real) < values11 (13 : Fin 91)
      rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by a158415_twelve_table]
      change (685340041 / 625000000 : Real) < Real.sqrt (values10 (13 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (469690971797881681 / 390625000000000000 : Real) < values10 (13 : Fin 54)
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by a158415_twelve_table]
      change (469690971797881681 / 390625000000000000 : Real) < Real.sqrt (values9 (13 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (220609608988438484620619678875385761 / 152587890625000000000000000000000000 : Real) < values9 (13 : Fin 33)
      rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
      change (220609608988438484620619678875385761 / 152587890625000000000000000000000000 : Real) < Real.sqrt (values8 (13 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (48668599578031718225548510026676472607458414843439591001510146561549121 / 23283064365386962890625000000000000000000000000000000000000000000000000 : Real) < values8 (13 : Fin 20)
      rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
      change (48668599578031718225548510026676472607458414843439591001510146561549121 / 23283064365386962890625000000000000000000000000000000000000000000000000 : Real) < 1 + values6 (1 : Fin 8)
      have h11 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h12 : (2181 / 2000 : Real) < values6 (1 : Fin 8) := by
        rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
        change (2181 / 2000 : Real) < Real.sqrt (values5 (1 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (4756761 / 4000000 : Real) < values5 (1 : Fin 5)
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (4756761 / 4000000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (22626775211121 / 16000000000000 : Real) < Real.sqrt 2
        change (22626775211121 / 16000000000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_270 :
    values14 (270 : Fin 455) < values14 (271 : Fin 455) := by
  have hleft : values14 (270 : Fin 455) < (259 / 125 : Real) := by
    rw [show values14 (270 : Fin 455) = 1 + values12 (17 : Fin 154) by rfl]
    change 1 + values12 (17 : Fin 154) < (259 / 125 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (17 : Fin 154) < (10711 / 10000 : Real) := by
      rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (17 : Fin 91)) < (10711 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10711 / 10000 : Real))]
      norm_num
      change values11 (17 : Fin 91) < (114725521 / 100000000 : Real)
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (17 : Fin 54)) < (114725521 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (114725521 / 100000000 : Real))]
      norm_num
      change values10 (17 : Fin 54) < (13161945168721441 / 10000000000000000 : Real)
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (17 : Fin 33)) < (13161945168721441 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161945168721441 / 10000000000000000 : Real))]
      norm_num
      change values9 (17 : Fin 33) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real)
      rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (17 : Fin 20)) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values8 (17 : Fin 20) < (30010989090588400256679505311166483916986617065427311405753823361 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (5 : Fin 8) < (30010989090588400256679505311166483916986617065427311405753823361 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values6 (5 : Fin 8) < (20001 / 10000 : Real) := by
        rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (20001 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 1 < (100001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (259 / 125 : Real) < values14 (271 : Fin 455) := by
    rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    change (259 / 125 : Real) < Real.sqrt (values13 (254 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (67081 / 15625 : Real) < values13 (254 : Fin 264)
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    change (67081 / 15625 : Real) < 1 + values11 (81 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (829 / 250 : Real) < values11 (81 : Fin 91) := by
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by a158415_twelve_table]
      change (829 / 250 : Real) < 1 + values9 (23 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (231607 / 100000 : Real) < values9 (23 : Fin 33) := by
        rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
        change (231607 / 100000 : Real) < 1 + values7 (4 : Fin 13)
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (658037 / 500000 : Real) < values7 (4 : Fin 13) := by
          rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
          change (658037 / 500000 : Real) < Real.sqrt (values6 (4 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (433012693369 / 250000000000 : Real) < values6 (4 : Fin 8)
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change (433012693369 / 250000000000 : Real) < Real.sqrt (values5 (4 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (187499992618675616570161 / 62500000000000000000000 : Real) < values5 (4 : Fin 5)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change (187499992618675616570161 / 62500000000000000000000 : Real) < 1 + 2
          have h13 : (99999999 / 100000000 : Real) < 1 := by
            norm_num
          have h14 : (199999999 / 100000000 : Real) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_271 :
    values14 (271 : Fin 455) < values14 (272 : Fin 455) := by
  have hleft : values14 (271 : Fin 455) < (1039 / 500 : Real) := by
    rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    change Real.sqrt (values13 (254 : Fin 264)) < (1039 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1039 / 500 : Real))]
    norm_num
    change values13 (254 : Fin 264) < (1079521 / 250000 : Real)
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    change 1 + values11 (81 : Fin 91) < (1079521 / 250000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (81 : Fin 91) < (33161 / 10000 : Real) := by
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (23 : Fin 33) < (33161 / 10000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (23 : Fin 33) < (28951 / 12500 : Real) := by
        rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (4 : Fin 13) < (28951 / 12500 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (4 : Fin 13) < (52643 / 40000 : Real) := by
          rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (4 : Fin 8)) < (52643 / 40000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (52643 / 40000 : Real))]
          norm_num
          change values6 (4 : Fin 8) < (2771285449 / 1600000000 : Real)
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (2771285449 / 1600000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2771285449 / 1600000000 : Real))]
          norm_num
          change values5 (4 : Fin 5) < (7680023039839131601 / 2560000000000000000 : Real)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (7680023039839131601 / 2560000000000000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 2 < (2000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1039 / 500 : Real) < values14 (272 : Fin 455) := by
    rw [show values14 (272 : Fin 455) = 1 + values12 (18 : Fin 154) by rfl]
    change (1039 / 500 : Real) < 1 + values12 (18 : Fin 154)
    have h9 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h10 : (10797 / 10000 : Real) < values12 (18 : Fin 154) := by
      rw [show values12 (18 : Fin 154) = Real.sqrt (values11 (18 : Fin 91)) by a158415_twelve_table]
      change (10797 / 10000 : Real) < Real.sqrt (values11 (18 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (116575209 / 100000000 : Real) < values11 (18 : Fin 91)
      rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by a158415_twelve_table]
      change (116575209 / 100000000 : Real) < Real.sqrt (values10 (18 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (13589779353393681 / 10000000000000000 : Real) < values10 (18 : Fin 54)
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by a158415_twelve_table]
      change (13589779353393681 / 10000000000000000 : Real) < Real.sqrt (values9 (18 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (184682102873925174460091770729761 / 100000000000000000000000000000000 : Real) < values9 (18 : Fin 33)
      rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
      change (184682102873925174460091770729761 / 100000000000000000000000000000000 : Real) < Real.sqrt (values8 (18 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (34107479121935081183758137217650508668877415300074960866491117121 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < values8 (18 : Fin 20)
      rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
      change (34107479121935081183758137217650508668877415300074960866491117121 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < 1 + values6 (6 : Fin 8)
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (1207 / 500 : Real) < values6 (6 : Fin 8) := by
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change (1207 / 500 : Real) < 1 + Real.sqrt 2
        have h13 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h14 : (7071 / 5000 : Real) < Real.sqrt 2 := by
          change (7071 / 5000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_275 :
    values14 (275 : Fin 455) < values14 (276 : Fin 455) := by
  have hleft : values14 (275 : Fin 455) < (2097 / 1000 : Real) := by
    rw [show values14 (275 : Fin 455) = 1 + values12 (21 : Fin 154) by rfl]
    change 1 + values12 (21 : Fin 154) < (2097 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (21 : Fin 154) < (5483 / 5000 : Real) := by
      rw [show values12 (21 : Fin 154) = Real.sqrt (values11 (21 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (21 : Fin 91)) < (5483 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5483 / 5000 : Real))]
      norm_num
      change values11 (21 : Fin 91) < (30063289 / 25000000 : Real)
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (21 : Fin 54)) < (30063289 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (30063289 / 25000000 : Real))]
      norm_num
      change values10 (21 : Fin 54) < (903801345497521 / 625000000000000 : Real)
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (21 : Fin 33)) < (903801345497521 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (903801345497521 / 625000000000000 : Real))]
      norm_num
      change values9 (21 : Fin 33) < (816856872123129323179017145441 / 390625000000000000000000000000 : Real)
      rw [show values9 (21 : Fin 33) = 1 + values7 (2 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (2 : Fin 13) < (816856872123129323179017145441 / 390625000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values7 (2 : Fin 13) < (5453 / 5000 : Real) := by
        rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (2 : Fin 8)) < (5453 / 5000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
        norm_num
        change values6 (2 : Fin 8) < (29735209 / 25000000 : Real)
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (29735209 / 25000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
        norm_num
        change values5 (2 : Fin 5) < (884182654273681 / 625000000000000 : Real)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2097 / 1000 : Real) < values14 (276 : Fin 455) := by
    rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    change (2097 / 1000 : Real) < Real.sqrt (values13 (255 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (4397409 / 1000000 : Real) < values13 (255 : Fin 264)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    change (4397409 / 1000000 : Real) < 1 + values11 (82 : Fin 91)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1707 / 500 : Real) < values11 (82 : Fin 91) := by
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by a158415_twelve_table]
      change (1707 / 500 : Real) < 1 + values9 (24 : Fin 33)
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (12071 / 5000 : Real) < values9 (24 : Fin 33) := by
        rw [show values9 (24 : Fin 33) = 1 + values7 (5 : Fin 13) by a158415_twelve_table]
        change (12071 / 5000 : Real) < 1 + values7 (5 : Fin 13)
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (141421 / 100000 : Real) < values7 (5 : Fin 13) := by
          rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
          change (141421 / 100000 : Real) < Real.sqrt (values6 (5 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (19999899241 / 10000000000 : Real) < values6 (5 : Fin 8)
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (19999899241 / 10000000000 : Real) < 1 + 1
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_276 :
    values14 (276 : Fin 455) < values14 (277 : Fin 455) := by
  have hleft : values14 (276 : Fin 455) < (1051 / 500 : Real) := by
    rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    change Real.sqrt (values13 (255 : Fin 264)) < (1051 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1051 / 500 : Real))]
    norm_num
    change values13 (255 : Fin 264) < (1104601 / 250000 : Real)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    change 1 + values11 (82 : Fin 91) < (1104601 / 250000 : Real)
    have h1 : 1 < (1001 / 1000 : Real) := by
      norm_num
    have h2 : values11 (82 : Fin 91) < (683 / 200 : Real) := by
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (24 : Fin 33) < (683 / 200 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (24 : Fin 33) < (24143 / 10000 : Real) := by
        rw [show values9 (24 : Fin 33) = 1 + values7 (5 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (5 : Fin 13) < (24143 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values7 (5 : Fin 13) < (70711 / 50000 : Real) := by
          rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (5 : Fin 8)) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
          change values6 (5 : Fin 8) < (5000045521 / 2500000000 : Real)
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (5000045521 / 2500000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1051 / 500 : Real) < values14 (277 : Fin 455) := by
    rw [show values14 (277 : Fin 455) = 1 + values12 (22 : Fin 154) by rfl]
    change (1051 / 500 : Real) < 1 + values12 (22 : Fin 154)
    have h9 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h10 : (2757 / 2500 : Real) < values12 (22 : Fin 154) := by
      rw [show values12 (22 : Fin 154) = Real.sqrt (values11 (22 : Fin 91)) by a158415_twelve_table]
      change (2757 / 2500 : Real) < Real.sqrt (values11 (22 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (7601049 / 6250000 : Real) < values11 (22 : Fin 91)
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by a158415_twelve_table]
      change (7601049 / 6250000 : Real) < Real.sqrt (values10 (22 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (57775945900401 / 39062500000000 : Real) < values10 (22 : Fin 54)
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by a158415_twelve_table]
      change (57775945900401 / 39062500000000 : Real) < Real.sqrt (values9 (22 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3338059924686063118611960801 / 1525878906250000000000000000 : Real) < values9 (22 : Fin 33)
      rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
      change (3338059924686063118611960801 / 1525878906250000000000000000 : Real) < 1 + values7 (3 : Fin 13)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (1189 / 1000 : Real) < values7 (3 : Fin 13) := by
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (values6 (3 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < values6 (3 : Fin 8)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (1413721 / 1000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1998607065841 / 1000000000000 : Real) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (1998607065841 / 1000000000000 : Real) < 1 + 1
        have h13 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h14 : (9999 / 10000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_281 :
    values14 (281 : Fin 455) < values14 (282 : Fin 455) := by
  have hleft : values14 (281 : Fin 455) < (21339 / 10000 : Real) := by
    rw [show values14 (281 : Fin 455) = 1 + values12 (26 : Fin 154) by rfl]
    change 1 + values12 (26 : Fin 154) < (21339 / 10000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (26 : Fin 154) < (113387 / 100000 : Real) := by
      rw [show values12 (26 : Fin 154) = Real.sqrt (values11 (26 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (26 : Fin 91)) < (113387 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (113387 / 100000 : Real))]
      norm_num
      change values11 (26 : Fin 91) < (12856611769 / 10000000000 : Real)
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (26 : Fin 54)) < (12856611769 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12856611769 / 10000000000 : Real))]
      norm_num
      change values10 (26 : Fin 54) < (165292466178789309361 / 100000000000000000000 : Real)
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (26 : Fin 33)) < (165292466178789309361 / 100000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (165292466178789309361 / 100000000000000000000 : Real))]
      norm_num
      change values9 (26 : Fin 33) < (27321599375466207709398765593783362228321 / 10000000000000000000000000000000000000000 : Real)
      rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (7 : Fin 13) < (27321599375466207709398765593783362228321 / 10000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values7 (7 : Fin 13) < (86603 / 50000 : Real) := by
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (7 : Fin 8)) < (86603 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (86603 / 50000 : Real))]
        norm_num
        change values6 (7 : Fin 8) < (7500079609 / 2500000000 : Real)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (7500079609 / 2500000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (21339 / 10000 : Real) < values14 (282 : Fin 455) := by
    rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    change (21339 / 10000 : Real) < Real.sqrt (values13 (256 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (455352921 / 100000000 : Real) < values13 (256 : Fin 264)
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    change (455352921 / 100000000 : Real) < 1 + values11 (83 : Fin 91)
    have h7 : (99999 / 100000 : Real) < 1 := by
      norm_num
    have h8 : (35537 / 10000 : Real) < values11 (83 : Fin 91) := by
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by a158415_twelve_table]
      change (35537 / 10000 : Real) < 1 + values9 (25 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (255377 / 100000 : Real) < values9 (25 : Fin 33) := by
        rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
        change (255377 / 100000 : Real) < 1 + values7 (6 : Fin 13)
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (1553773 / 1000000 : Real) < values7 (6 : Fin 13) := by
          rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
          change (1553773 / 1000000 : Real) < Real.sqrt (values6 (6 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (2414210535529 / 1000000000000 : Real) < values6 (6 : Fin 8)
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change (2414210535529 / 1000000000000 : Real) < 1 + Real.sqrt 2
          have h13 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h14 : (1414213 / 1000000 : Real) < Real.sqrt 2 := by
            change (1414213 / 1000000 : Real) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_282 :
    values14 (282 : Fin 455) < values14 (283 : Fin 455) := by
  have hleft : values14 (282 : Fin 455) < (1067 / 500 : Real) := by
    rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    change Real.sqrt (values13 (256 : Fin 264)) < (1067 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1067 / 500 : Real))]
    norm_num
    change values13 (256 : Fin 264) < (1138489 / 250000 : Real)
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    change 1 + values11 (83 : Fin 91) < (1138489 / 250000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values11 (83 : Fin 91) < (17769 / 5000 : Real) := by
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (25 : Fin 33) < (17769 / 5000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (25 : Fin 33) < (127689 / 50000 : Real) := by
        rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (6 : Fin 13) < (127689 / 50000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (6 : Fin 13) < (776887 / 500000 : Real) := by
          rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (6 : Fin 8)) < (776887 / 500000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (776887 / 500000 : Real))]
          norm_num
          change values6 (6 : Fin 8) < (603553410769 / 250000000000 : Real)
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change 1 + Real.sqrt 2 < (603553410769 / 250000000000 : Real)
          have h7 : 1 < (100000001 / 100000000 : Real) := by
            norm_num
          have h8 : Real.sqrt 2 < (141421357 / 100000000 : Real) := by
            change Real.sqrt (2) < (141421357 / 100000000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141421357 / 100000000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1067 / 500 : Real) < values14 (283 : Fin 455) := by
    rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    change (1067 / 500 : Real) < values6 (1 : Fin 8) + values7 (1 : Fin 13)
    have h9 : (2181 / 2000 : Real) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (2181 / 2000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4756761 / 4000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (4756761 / 4000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (22626775211121 / 16000000000000 : Real) < Real.sqrt 2
      change (22626775211121 / 16000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (5221 / 5000 : Real) < values7 (1 : Fin 13) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (5221 / 5000 : Real) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (27258841 / 25000000 : Real) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (27258841 / 25000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (743044412663281 / 625000000000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (743044412663281 / 625000000000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (552114999190120225711485684961 / 390625000000000000000000000000 : Real) < Real.sqrt 2
      change (552114999190120225711485684961 / 390625000000000000000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_283 :
    values14 (283 : Fin 455) < values14 (284 : Fin 455) := by
  have hleft : values14 (283 : Fin 455) < (427 / 200 : Real) := by
    rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    change values6 (1 : Fin 8) + values7 (1 : Fin 13) < (427 / 200 : Real)
    have h1 : values6 (1 : Fin 8) < (109051 / 100000 : Real) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (109051 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109051 / 100000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (11892120601 / 10000000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11892120601 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11892120601 / 10000000000 : Real))]
      norm_num
      change Real.sqrt 2 < (141422532388728601201 / 100000000000000000000 : Real)
      change Real.sqrt (2) < (141422532388728601201 / 100000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141422532388728601201 / 100000000000000000000 : Real))]
      norm_num
    have h2 : values7 (1 : Fin 13) < (10443 / 10000 : Real) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (10443 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443 / 10000 : Real))]
      norm_num
      change values6 (1 : Fin 8) < (109056249 / 100000000 : Real)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (109056249 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109056249 / 100000000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (11893265445950001 / 10000000000000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893265445950001 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893265445950001 / 10000000000000000 : Real))]
      norm_num
      change Real.sqrt 2 < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      change Real.sqrt (2) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (427 / 200 : Real) < values14 (284 : Fin 455) := by
    rw [show values14 (284 : Fin 455) = 1 + values12 (27 : Fin 154) by rfl]
    change (427 / 200 : Real) < 1 + values12 (27 : Fin 154)
    have h3 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h4 : (569 / 500 : Real) < values12 (27 : Fin 154) := by
      rw [show values12 (27 : Fin 154) = Real.sqrt (values11 (27 : Fin 91)) by a158415_twelve_table]
      change (569 / 500 : Real) < Real.sqrt (values11 (27 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (323761 / 250000 : Real) < values11 (27 : Fin 91)
      rw [show values11 (27 : Fin 91) = Real.sqrt (values10 (27 : Fin 54)) by a158415_twelve_table]
      change (323761 / 250000 : Real) < Real.sqrt (values10 (27 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (104821185121 / 62500000000 : Real) < values10 (27 : Fin 54)
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by a158415_twelve_table]
      change (104821185121 / 62500000000 : Real) < Real.sqrt (values9 (27 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10987480850170951784641 / 3906250000000000000000 : Real) < values9 (27 : Fin 33)
      rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
      change (10987480850170951784641 / 3906250000000000000000 : Real) < Real.sqrt 2 + Real.sqrt 2
      have h5 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h6 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_287 :
    values14 (287 : Fin 455) < values14 (288 : Fin 455) := by
  have hleft : values14 (287 : Fin 455) < (1083 / 500 : Real) := by
    rw [show values14 (287 : Fin 455) = 1 + values12 (30 : Fin 154) by rfl]
    change 1 + values12 (30 : Fin 154) < (1083 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (30 : Fin 154) < (116591 / 100000 : Real) := by
      rw [show values12 (30 : Fin 154) = Real.sqrt (values11 (30 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (30 : Fin 91)) < (116591 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (116591 / 100000 : Real))]
      norm_num
      change values11 (30 : Fin 91) < (13593461281 / 10000000000 : Real)
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (30 : Fin 54)) < (13593461281 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13593461281 / 10000000000 : Real))]
      norm_num
      change values10 (30 : Fin 54) < (184782189598046160961 / 100000000000000000000 : Real)
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by a158415_twelve_table]
      change Real.sqrt (values9 (30 : Fin 33)) < (184782189598046160961 / 100000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (184782189598046160961 / 100000000000000000000 : Real))]
      norm_num
      change values9 (30 : Fin 33) < (34144457592648278848499057898190320443521 / 10000000000000000000000000000000000000000 : Real)
      rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
      change 1 + values7 (10 : Fin 13) < (34144457592648278848499057898190320443521 / 10000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values7 (10 : Fin 13) < (120711 / 50000 : Real) := by
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (120711 / 50000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values5 (2 : Fin 5) < (707107 / 500000 : Real) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (707107 / 500000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1083 / 500 : Real) < values14 (288 : Fin 455) := by
    rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    change (1083 / 500 : Real) < Real.sqrt (values13 (257 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1172889 / 250000 : Real) < values13 (257 : Fin 264)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    change (1172889 / 250000 : Real) < 1 + values11 (84 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (933 / 250 : Real) < values11 (84 : Fin 91) := by
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by a158415_twelve_table]
      change (933 / 250 : Real) < 1 + values9 (26 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (54641 / 20000 : Real) < values9 (26 : Fin 33) := by
        rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
        change (54641 / 20000 : Real) < 1 + values7 (7 : Fin 13)
        have h11 : (9999999 / 10000000 : Real) < 1 := by
          norm_num
        have h12 : (4330127 / 2500000 : Real) < values7 (7 : Fin 13) := by
          rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
          change (4330127 / 2500000 : Real) < Real.sqrt (values6 (7 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (18749999836129 / 6250000000000 : Real) < values6 (7 : Fin 8)
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change (18749999836129 / 6250000000000 : Real) < 1 + 2
          have h13 : (999999999 / 1000000000 : Real) < 1 := by
            norm_num
          have h14 : (1999999999 / 1000000000 : Real) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_288 :
    values14 (288 : Fin 455) < values14 (289 : Fin 455) := by
  have hleft : values14 (288 : Fin 455) < (272 / 125 : Real) := by
    rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    change Real.sqrt (values13 (257 : Fin 264)) < (272 / 125 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (272 / 125 : Real))]
    norm_num
    change values13 (257 : Fin 264) < (73984 / 15625 : Real)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    change 1 + values11 (84 : Fin 91) < (73984 / 15625 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (84 : Fin 91) < (3733 / 1000 : Real) := by
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (26 : Fin 33) < (3733 / 1000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (26 : Fin 33) < (27321 / 10000 : Real) := by
        rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (7 : Fin 13) < (27321 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values7 (7 : Fin 13) < (86603 / 50000 : Real) := by
          rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (7 : Fin 8)) < (86603 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (86603 / 50000 : Real))]
          norm_num
          change values6 (7 : Fin 8) < (7500079609 / 2500000000 : Real)
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (7500079609 / 2500000000 : Real)
          have h7 : 1 < (100001 / 100000 : Real) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (272 / 125 : Real) < values14 (289 : Fin 455) := by
    rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    change (272 / 125 : Real) < values6 (1 : Fin 8) + values7 (2 : Fin 13)
    have h9 : (109 / 100 : Real) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < Real.sqrt 2
      change (141158161 / 100000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (109 / 100 : Real) < values7 (2 : Fin 13) := by
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values6 (2 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values6 (2 : Fin 8)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (141158161 / 100000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_289 :
    values14 (289 : Fin 455) < values14 (290 : Fin 455) := by
  have hleft : values14 (289 : Fin 455) < (1091 / 500 : Real) := by
    rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    change values6 (1 : Fin 8) + values7 (2 : Fin 13) < (1091 / 500 : Real)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : Real) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (29735209 / 25000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change Real.sqrt 2 < (884182654273681 / 625000000000000 : Real)
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
    have h2 : values7 (2 : Fin 13) < (5453 / 5000 : Real) := by
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (2 : Fin 8)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values6 (2 : Fin 8) < (29735209 / 25000000 : Real)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change values5 (2 : Fin 5) < (884182654273681 / 625000000000000 : Real)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
    linarith
  have hright : (1091 / 500 : Real) < values14 (290 : Fin 455) := by
    rw [show values14 (290 : Fin 455) = 1 + values12 (31 : Fin 154) by rfl]
    change (1091 / 500 : Real) < 1 + values12 (31 : Fin 154)
    have h3 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h4 : (1189 / 1000 : Real) < values12 (31 : Fin 154) := by
      rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (values11 (31 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < values11 (31 : Fin 91)
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by a158415_twelve_table]
      change (1413721 / 1000000 : Real) < Real.sqrt (values10 (31 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : Real) < values10 (31 : Fin 54)
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : Real) < Real.sqrt (values9 (31 : Fin 33))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3994430203629571309037281 / 1000000000000000000000000 : Real) < values9 (31 : Fin 33)
      rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
      change (3994430203629571309037281 / 1000000000000000000000000 : Real) < 1 + values7 (11 : Fin 13)
      have h5 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h6 : (2999 / 1000 : Real) < values7 (11 : Fin 13) := by
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (2999 / 1000 : Real) < 1 + values5 (3 : Fin 5)
        have h7 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h8 : (19999 / 10000 : Real) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (19999 / 10000 : Real) < 1 + 1
          have h9 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h10 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_292 :
    values14 (292 : Fin 455) < values14 (293 : Fin 455) := by
  have hleft : values14 (292 : Fin 455) < (549 / 250 : Real) := by
    rw [show values14 (292 : Fin 455) = 1 + values12 (33 : Fin 154) by rfl]
    change 1 + values12 (33 : Fin 154) < (549 / 250 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (33 : Fin 154) < (5979 / 5000 : Real) := by
      rw [show values12 (33 : Fin 154) = Real.sqrt (values11 (33 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (33 : Fin 91)) < (5979 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5979 / 5000 : Real))]
      norm_num
      change values11 (33 : Fin 91) < (35748441 / 25000000 : Real)
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (33 : Fin 54)) < (35748441 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (35748441 / 25000000 : Real))]
      norm_num
      change values10 (33 : Fin 54) < (1277951033930481 / 625000000000000 : Real)
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (2 : Fin 20) < (1277951033930481 / 625000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values8 (2 : Fin 20) < (10443 / 10000 : Real) := by
        rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (2 : Fin 13)) < (10443 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443 / 10000 : Real))]
        norm_num
        change values7 (2 : Fin 13) < (109056249 / 100000000 : Real)
        rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (2 : Fin 8)) < (109056249 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109056249 / 100000000 : Real))]
        norm_num
        change values6 (2 : Fin 8) < (11893265445950001 / 10000000000000000 : Real)
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (11893265445950001 / 10000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893265445950001 / 10000000000000000 : Real))]
        norm_num
        change values5 (2 : Fin 5) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (549 / 250 : Real) < values14 (293 : Fin 455) := by
    rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    change (549 / 250 : Real) < Real.sqrt (values13 (258 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (301401 / 62500 : Real) < values13 (258 : Fin 264)
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    change (301401 / 62500 : Real) < 1 + values11 (85 : Fin 91)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (957 / 250 : Real) < values11 (85 : Fin 91) := by
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by a158415_twelve_table]
      change (957 / 250 : Real) < 1 + values9 (27 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (7071 / 2500 : Real) < values9 (27 : Fin 33) := by
        rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
        change (7071 / 2500 : Real) < Real.sqrt 2 + Real.sqrt 2
        have h9 : (141421 / 100000 : Real) < Real.sqrt 2 := by
          change (141421 / 100000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        have h10 : (141421 / 100000 : Real) < Real.sqrt 2 := by
          change (141421 / 100000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_293 :
    values14 (293 : Fin 455) < values14 (294 : Fin 455) := by
  have hleft : values14 (293 : Fin 455) < (1099 / 500 : Real) := by
    rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    change Real.sqrt (values13 (258 : Fin 264)) < (1099 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1099 / 500 : Real))]
    norm_num
    change values13 (258 : Fin 264) < (1207801 / 250000 : Real)
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    change 1 + values11 (85 : Fin 91) < (1207801 / 250000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (85 : Fin 91) < (3829 / 1000 : Real) := by
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (27 : Fin 33) < (3829 / 1000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (27 : Fin 33) < (5657 / 2000 : Real) := by
        rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
        change Real.sqrt 2 + Real.sqrt 2 < (5657 / 2000 : Real)
        have h5 : Real.sqrt 2 < (70711 / 50000 : Real) := by
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : Real) := by
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1099 / 500 : Real) < values14 (294 : Fin 455) := by
    rw [show values14 (294 : Fin 455) = 1 + values12 (34 : Fin 154) by rfl]
    change (1099 / 500 : Real) < 1 + values12 (34 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (601 / 500 : Real) < values12 (34 : Fin 154) := by
      rw [show values12 (34 : Fin 154) = Real.sqrt (values11 (34 : Fin 91)) by a158415_twelve_table]
      change (601 / 500 : Real) < Real.sqrt (values11 (34 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (361201 / 250000 : Real) < values11 (34 : Fin 91)
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by a158415_twelve_table]
      change (361201 / 250000 : Real) < Real.sqrt (values10 (34 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (130466162401 / 62500000000 : Real) < values10 (34 : Fin 54)
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by a158415_twelve_table]
      change (130466162401 / 62500000000 : Real) < 1 + values8 (3 : Fin 20)
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (109 / 100 : Real) < values8 (3 : Fin 20) := by
        rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
        change (109 / 100 : Real) < Real.sqrt (values7 (3 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11881 / 10000 : Real) < values7 (3 : Fin 13)
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change (11881 / 10000 : Real) < Real.sqrt (values6 (3 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (141158161 / 100000000 : Real) < values6 (3 : Fin 8)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (141158161 / 100000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (19925626416901921 / 10000000000000000 : Real) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (19925626416901921 / 10000000000000000 : Real) < 1 + 1
        have h11 : (999 / 1000 : Real) < 1 := by
          norm_num
        have h12 : (999 / 1000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_295 :
    values14 (295 : Fin 455) < values14 (296 : Fin 455) := by
  have hleft : values14 (295 : Fin 455) < (2211 / 1000 : Real) := by
    rw [show values14 (295 : Fin 455) = 1 + values12 (35 : Fin 154) by rfl]
    change 1 + values12 (35 : Fin 154) < (2211 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (35 : Fin 154) < (6053 / 5000 : Real) := by
      rw [show values12 (35 : Fin 154) = Real.sqrt (values11 (35 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (35 : Fin 91)) < (6053 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (6053 / 5000 : Real))]
      norm_num
      change values11 (35 : Fin 91) < (36638809 / 25000000 : Real)
      rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (35 : Fin 54)) < (36638809 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (36638809 / 25000000 : Real))]
      norm_num
      change values10 (35 : Fin 54) < (1342402324938481 / 625000000000000 : Real)
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (4 : Fin 20) < (1342402324938481 / 625000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values8 (4 : Fin 20) < (11473 / 10000 : Real) := by
        rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (4 : Fin 13)) < (11473 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11473 / 10000 : Real))]
        norm_num
        change values7 (4 : Fin 13) < (131629729 / 100000000 : Real)
        rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (4 : Fin 8)) < (131629729 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (131629729 / 100000000 : Real))]
        norm_num
        change values6 (4 : Fin 8) < (17326385556613441 / 10000000000000000 : Real)
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (4 : Fin 5)) < (17326385556613441 / 10000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17326385556613441 / 10000000000000000 : Real))]
        norm_num
        change values5 (4 : Fin 5) < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
        have h5 : 1 < (10001 / 10000 : Real) := by
          norm_num
        have h6 : 2 < (20001 / 10000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (2211 / 1000 : Real) < values14 (296 : Fin 455) := by
    rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    change (2211 / 1000 : Real) < values5 (1 : Fin 5) + values8 (1 : Fin 20)
    have h7 : (2973 / 2500 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (2973 / 2500 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (8838729 / 6250000 : Real) < Real.sqrt 2
      change (8838729 / 6250000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (102189 / 100000 : Real) < values8 (1 : Fin 20) := by
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (102189 / 100000 : Real) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10442591721 / 10000000000 : Real) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (10442591721 / 10000000000 : Real) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (109047721851497741841 / 100000000000000000000 : Real) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109047721851497741841 / 100000000000000000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11891405641001618093863193082322282069281 / 10000000000000000000000000000000000000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11891405641001618093863193082322282069281 / 10000000000000000000000000000000000000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141405528118845103701984886021026474860395882942331700231681873560264043283856961 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt 2
      change (141405528118845103701984886021026474860395882942331700231681873560264043283856961 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_296 :
    values14 (296 : Fin 455) < values14 (297 : Fin 455) := by
  have hleft : values14 (296 : Fin 455) < (553 / 250 : Real) := by
    rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (1 : Fin 20) < (553 / 250 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (1 : Fin 20) < (511 / 500 : Real) := by
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (1 : Fin 13)) < (511 / 500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (511 / 500 : Real))]
      norm_num
      change values7 (1 : Fin 13) < (261121 / 250000 : Real)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (261121 / 250000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (261121 / 250000 : Real))]
      norm_num
      change values6 (1 : Fin 8) < (68184176641 / 62500000000 : Real)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (68184176641 / 62500000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (68184176641 / 62500000000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (4649081944211090042881 / 3906250000000000000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (4649081944211090042881 / 3906250000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (4649081944211090042881 / 3906250000000000000000 : Real))]
      norm_num
      change Real.sqrt 2 < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real)
      change Real.sqrt (2) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (553 / 250 : Real) < values14 (297 : Fin 455) := by
    rw [show values14 (297 : Fin 455) = 1 + values12 (36 : Fin 154) by rfl]
    change (553 / 250 : Real) < 1 + values12 (36 : Fin 154)
    have h3 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h4 : (152 / 125 : Real) < values12 (36 : Fin 154) := by
      rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by a158415_twelve_table]
      change (152 / 125 : Real) < Real.sqrt (values11 (36 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (23104 / 15625 : Real) < values11 (36 : Fin 91)
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by a158415_twelve_table]
      change (23104 / 15625 : Real) < Real.sqrt (values10 (36 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (533794816 / 244140625 : Real) < values10 (36 : Fin 54)
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by a158415_twelve_table]
      change (533794816 / 244140625 : Real) < 1 + values8 (5 : Fin 20)
      have h5 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h6 : (1189 / 1000 : Real) < values8 (5 : Fin 20) := by
        rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (values7 (5 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < values7 (5 : Fin 13)
        rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
        change (1413721 / 1000000 : Real) < Real.sqrt (values6 (5 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1998607065841 / 1000000000000 : Real) < values6 (5 : Fin 8)
        rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
        change (1998607065841 / 1000000000000 : Real) < 1 + 1
        have h7 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h8 : (9999 / 10000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_299 :
    values14 (299 : Fin 455) < values14 (300 : Fin 455) := by
  have hleft : values14 (299 : Fin 455) < (89 / 40 : Real) := by
    rw [show values14 (299 : Fin 455) = 1 + values12 (38 : Fin 154) by rfl]
    change 1 + values12 (38 : Fin 154) < (89 / 40 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (38 : Fin 154) < (12243 / 10000 : Real) := by
      rw [show values12 (38 : Fin 154) = Real.sqrt (values11 (38 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (38 : Fin 91)) < (12243 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12243 / 10000 : Real))]
      norm_num
      change values11 (38 : Fin 91) < (149891049 / 100000000 : Real)
      rw [show values11 (38 : Fin 91) = Real.sqrt (values10 (38 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (38 : Fin 54)) < (149891049 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (149891049 / 100000000 : Real))]
      norm_num
      change values10 (38 : Fin 54) < (22467326570320401 / 10000000000000000 : Real)
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (6 : Fin 20) < (22467326570320401 / 10000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values8 (6 : Fin 20) < (124651 / 100000 : Real) := by
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (6 : Fin 13)) < (124651 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (124651 / 100000 : Real))]
        norm_num
        change values7 (6 : Fin 13) < (15537871801 / 10000000000 : Real)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (15537871801 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15537871801 / 10000000000 : Real))]
        norm_num
        change values6 (6 : Fin 8) < (241425460104310983601 / 100000000000000000000 : Real)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (241425460104310983601 / 100000000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : Real) := by
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (89 / 40 : Real) < values14 (300 : Fin 455) := by
    rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    change (89 / 40 : Real) < values5 (1 : Fin 5) + values8 (2 : Fin 20)
    have h7 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (261 / 250 : Real) < values8 (2 : Fin 20) := by
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change (261 / 250 : Real) < Real.sqrt (values7 (2 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : Real) < values7 (2 : Fin 13)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change (68121 / 62500 : Real) < Real.sqrt (values6 (2 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : Real) < values6 (2 : Fin 8)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (4640470641 / 3906250000 : Real) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : Real) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_300 :
    values14 (300 : Fin 455) < values14 (301 : Fin 455) := by
  have hleft : values14 (300 : Fin 455) < (4467 / 2000 : Real) := by
    rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (2 : Fin 20) < (4467 / 2000 : Real)
    have h1 : values5 (1 : Fin 5) < (118921 / 100000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
      norm_num
      change Real.sqrt 2 < (14142204241 / 10000000000 : Real)
      change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
      norm_num
    have h2 : values8 (2 : Fin 20) < (26107 / 25000 : Real) := by
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (2 : Fin 13)) < (26107 / 25000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (26107 / 25000 : Real))]
      norm_num
      change values7 (2 : Fin 13) < (681575449 / 625000000 : Real)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (2 : Fin 8)) < (681575449 / 625000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (681575449 / 625000000 : Real))]
      norm_num
      change values6 (2 : Fin 8) < (464545092679551601 / 390625000000000000 : Real)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (464545092679551601 / 390625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (464545092679551601 / 390625000000000000 : Real))]
      norm_num
      change values5 (2 : Fin 5) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (4467 / 2000 : Real) < values14 (301 : Fin 455) := by
    rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    change (4467 / 2000 : Real) < 1 + values12 (39 : Fin 154)
    have h3 : (99999 / 100000 : Real) < 1 := by
      norm_num
    have h4 : (771 / 625 : Real) < values12 (39 : Fin 154) := by
      rw [show values12 (39 : Fin 154) = Real.sqrt (values11 (39 : Fin 91)) by a158415_twelve_table]
      change (771 / 625 : Real) < Real.sqrt (values11 (39 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (594441 / 390625 : Real) < values11 (39 : Fin 91)
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by a158415_twelve_table]
      change (594441 / 390625 : Real) < Real.sqrt (values10 (39 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (353360102481 / 152587890625 : Real) < values10 (39 : Fin 54)
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by a158415_twelve_table]
      change (353360102481 / 152587890625 : Real) < 1 + values8 (7 : Fin 20)
      have h5 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h6 : (329 / 250 : Real) < values8 (7 : Fin 20) := by
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change (329 / 250 : Real) < Real.sqrt (values7 (7 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108241 / 62500 : Real) < values7 (7 : Fin 13)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (108241 / 62500 : Real) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11716114081 / 3906250000 : Real) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (11716114081 / 3906250000 : Real) < 1 + 2
        have h7 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h8 : (19999 / 10000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_301 :
    values14 (301 : Fin 455) < values14 (302 : Fin 455) := by
  have hleft : values14 (301 : Fin 455) < (1117 / 500 : Real) := by
    rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    change 1 + values12 (39 : Fin 154) < (1117 / 500 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (39 : Fin 154) < (12337 / 10000 : Real) := by
      rw [show values12 (39 : Fin 154) = Real.sqrt (values11 (39 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (39 : Fin 91)) < (12337 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12337 / 10000 : Real))]
      norm_num
      change values11 (39 : Fin 91) < (152201569 / 100000000 : Real)
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (39 : Fin 54)) < (152201569 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (152201569 / 100000000 : Real))]
      norm_num
      change values10 (39 : Fin 54) < (23165317606061761 / 10000000000000000 : Real)
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (7 : Fin 20) < (23165317606061761 / 10000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values8 (7 : Fin 20) < (13161 / 10000 : Real) := by
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (7 : Fin 13)) < (13161 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
        norm_num
        change values7 (7 : Fin 13) < (173211921 / 100000000 : Real)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (7 : Fin 8)) < (173211921 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
        norm_num
        change values6 (7 : Fin 8) < (30002369576510241 / 10000000000000000 : Real)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (30002369576510241 / 10000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (1117 / 500 : Real) < values14 (302 : Fin 455) := by
    rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    change (1117 / 500 : Real) < Real.sqrt (values13 (259 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1247689 / 250000 : Real) < values13 (259 : Fin 264)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    change (1247689 / 250000 : Real) < 1 + values11 (86 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (3999 / 1000 : Real) < values11 (86 : Fin 91) := by
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by a158415_twelve_table]
      change (3999 / 1000 : Real) < 1 + values9 (28 : Fin 33)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (29999 / 10000 : Real) < values9 (28 : Fin 33) := by
        rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
        change (29999 / 10000 : Real) < 1 + values7 (8 : Fin 13)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : Real) < values7 (8 : Fin 13) := by
          rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
          change (199999 / 100000 : Real) < 1 + values5 (0 : Fin 5)
          have h13 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h14 : (999999 / 1000000 : Real) < values5 (0 : Fin 5) := by
            rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
            change (999999 / 1000000 : Real) < Real.sqrt (1)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_302 :
    values14 (302 : Fin 455) < values14 (303 : Fin 455) := by
  have hleft : values14 (302 : Fin 455) < (2237 / 1000 : Real) := by
    rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    change Real.sqrt (values13 (259 : Fin 264)) < (2237 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2237 / 1000 : Real))]
    norm_num
    change values13 (259 : Fin 264) < (5004169 / 1000000 : Real)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    change 1 + values11 (86 : Fin 91) < (5004169 / 1000000 : Real)
    have h1 : 1 < (1001 / 1000 : Real) := by
      norm_num
    have h2 : values11 (86 : Fin 91) < (4001 / 1000 : Real) := by
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (28 : Fin 33) < (4001 / 1000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (28 : Fin 33) < (30001 / 10000 : Real) := by
        rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (8 : Fin 13) < (30001 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values7 (8 : Fin 13) < (200001 / 100000 : Real) := by
          rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (0 : Fin 5) < (200001 / 100000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : values5 (0 : Fin 5) < (1000001 / 1000000 : Real) := by
            rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
            change Real.sqrt (1) < (1000001 / 1000000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1000001 / 1000000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2237 / 1000 : Real) < values14 (303 : Fin 455) := by
    rw [show values14 (303 : Fin 455) = 1 + values12 (40 : Fin 154) by rfl]
    change (2237 / 1000 : Real) < 1 + values12 (40 : Fin 154)
    have h9 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h10 : (623 / 500 : Real) < values12 (40 : Fin 154) := by
      rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by a158415_twelve_table]
      change (623 / 500 : Real) < Real.sqrt (values11 (40 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : Real) < values11 (40 : Fin 91)
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by a158415_twelve_table]
      change (388129 / 250000 : Real) < Real.sqrt (values10 (40 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : Real) < values10 (40 : Fin 54)
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by a158415_twelve_table]
      change (150644120641 / 62500000000 : Real) < 1 + values8 (8 : Fin 20)
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (707 / 500 : Real) < values8 (8 : Fin 20) := by
        rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
        change (707 / 500 : Real) < Real.sqrt (values7 (8 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (499849 / 250000 : Real) < values7 (8 : Fin 13)
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change (499849 / 250000 : Real) < 1 + values5 (0 : Fin 5)
        have h13 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h14 : (9999 / 10000 : Real) < values5 (0 : Fin 5) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change (9999 / 10000 : Real) < Real.sqrt (1)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_306 :
    values14 (306 : Fin 455) < values14 (307 : Fin 455) := by
  have hleft : values14 (306 : Fin 455) < (2271 / 1000 : Real) := by
    rw [show values14 (306 : Fin 455) = 1 + values12 (43 : Fin 154) by rfl]
    change 1 + values12 (43 : Fin 154) < (2271 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (43 : Fin 154) < (12703 / 10000 : Real) := by
      rw [show values12 (43 : Fin 154) = Real.sqrt (values11 (43 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (43 : Fin 91)) < (12703 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12703 / 10000 : Real))]
      norm_num
      change values11 (43 : Fin 91) < (161366209 / 100000000 : Real)
      rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (43 : Fin 54)) < (161366209 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (161366209 / 100000000 : Real))]
      norm_num
      change values10 (43 : Fin 54) < (26039053407031681 / 10000000000000000 : Real)
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by a158415_twelve_table]
      change Real.sqrt 2 + values5 (1 : Fin 5) < (26039053407031681 / 10000000000000000 : Real)
      have h3 : Real.sqrt 2 < (14143 / 10000 : Real) := by
        change Real.sqrt (2) < (14143 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
        norm_num
      have h4 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
        norm_num
        change Real.sqrt 2 < (141443449 / 100000000 : Real)
        change Real.sqrt (2) < (141443449 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2271 / 1000 : Real) < values14 (307 : Fin 455) := by
    rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    change (2271 / 1000 : Real) < Real.sqrt (values13 (260 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (5157441 / 1000000 : Real) < values13 (260 : Fin 264)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    change (5157441 / 1000000 : Real) < 1 + values11 (87 : Fin 91)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (4189 / 1000 : Real) < values11 (87 : Fin 91) := by
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by a158415_twelve_table]
      change (4189 / 1000 : Real) < 1 + values9 (29 : Fin 33)
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (7973 / 2500 : Real) < values9 (29 : Fin 33) := by
        rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
        change (7973 / 2500 : Real) < 1 + values7 (9 : Fin 13)
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (2189207 / 1000000 : Real) < values7 (9 : Fin 13) := by
          rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
          change (2189207 / 1000000 : Real) < 1 + values5 (1 : Fin 5)
          have h11 : (99999999 / 100000000 : Real) < 1 := by
            norm_num
          have h12 : (11892071 / 10000000 : Real) < values5 (1 : Fin 5) := by
            rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
            change (11892071 / 10000000 : Real) < Real.sqrt (Real.sqrt 2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
            change (141421352669041 / 100000000000000 : Real) < Real.sqrt 2
            change (141421352669041 / 100000000000000 : Real) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_307 :
    values14 (307 : Fin 455) < values14 (308 : Fin 455) := by
  have hleft : values14 (307 : Fin 455) < (1139 / 500 : Real) := by
    rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    change Real.sqrt (values13 (260 : Fin 264)) < (1139 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1139 / 500 : Real))]
    norm_num
    change values13 (260 : Fin 264) < (1297321 / 250000 : Real)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    change 1 + values11 (87 : Fin 91) < (1297321 / 250000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values11 (87 : Fin 91) < (418921 / 100000 : Real) := by
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (29 : Fin 33) < (418921 / 100000 : Real)
      have h3 : 1 < (10000001 / 10000000 : Real) := by
        norm_num
      have h4 : values9 (29 : Fin 33) < (398651 / 125000 : Real) := by
        rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (9 : Fin 13) < (398651 / 125000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values7 (9 : Fin 13) < (2736509 / 1250000 : Real) := by
          rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (1 : Fin 5) < (2736509 / 1250000 : Real)
          have h7 : 1 < (100000001 / 100000000 : Real) := by
            norm_num
          have h8 : values5 (1 : Fin 5) < (14865089 / 12500000 : Real) := by
            rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
            change Real.sqrt (Real.sqrt 2) < (14865089 / 12500000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14865089 / 12500000 : Real))]
            norm_num
            change Real.sqrt 2 < (220970870977921 / 156250000000000 : Real)
            change Real.sqrt (2) < (220970870977921 / 156250000000000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (220970870977921 / 156250000000000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1139 / 500 : Real) < values14 (308 : Fin 455) := by
    rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    change (1139 / 500 : Real) < values5 (1 : Fin 5) + values8 (3 : Fin 20)
    have h9 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (109 / 100 : Real) < values8 (3 : Fin 20) := by
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values7 (3 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values7 (3 : Fin 13)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (values6 (3 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < values6 (3 : Fin 8)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change (141158161 / 100000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (19925626416901921 / 10000000000000000 : Real) < values5 (3 : Fin 5)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change (19925626416901921 / 10000000000000000 : Real) < 1 + 1
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (999 / 1000 : Real) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_308 :
    values14 (308 : Fin 455) < values14 (309 : Fin 455) := by
  have hleft : values14 (308 : Fin 455) < (57 / 25 : Real) := by
    rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (3 : Fin 20) < (57 / 25 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (3 : Fin 20) < (5453 / 5000 : Real) := by
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (3 : Fin 13)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values7 (3 : Fin 13) < (29735209 / 25000000 : Real)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (3 : Fin 8)) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change values6 (3 : Fin 8) < (884182654273681 / 625000000000000 : Real)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (3 : Fin 5)) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
      change values5 (3 : Fin 5) < (781778966118451701933649289761 / 390625000000000000000000000000 : Real)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (781778966118451701933649289761 / 390625000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (57 / 25 : Real) < values14 (309 : Fin 455) := by
    rw [show values14 (309 : Fin 455) = 1 + values12 (44 : Fin 154) by rfl]
    change (57 / 25 : Real) < 1 + values12 (44 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (257 / 200 : Real) < values12 (44 : Fin 154) := by
      rw [show values12 (44 : Fin 154) = Real.sqrt (values11 (44 : Fin 91)) by a158415_twelve_table]
      change (257 / 200 : Real) < Real.sqrt (values11 (44 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (66049 / 40000 : Real) < values11 (44 : Fin 91)
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by a158415_twelve_table]
      change (66049 / 40000 : Real) < Real.sqrt (values10 (44 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4362470401 / 1600000000 : Real) < values10 (44 : Fin 54)
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by a158415_twelve_table]
      change (4362470401 / 1600000000 : Real) < 1 + values8 (11 : Fin 20)
      have h7 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h8 : (433 / 250 : Real) < values8 (11 : Fin 20) := by
        rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
        change (433 / 250 : Real) < Real.sqrt (values7 (11 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : Real) < values7 (11 : Fin 13)
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (187489 / 62500 : Real) < 1 + values5 (3 : Fin 5)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (199999 / 100000 : Real) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : Real) < 1 + 1
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_312 :
    values14 (312 : Fin 455) < values14 (313 : Fin 455) := by
  have hleft : values14 (312 : Fin 455) < (1163 / 500 : Real) := by
    rw [show values14 (312 : Fin 455) = 1 + values12 (47 : Fin 154) by rfl]
    change 1 + values12 (47 : Fin 154) < (1163 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (47 : Fin 154) < (13259 / 10000 : Real) := by
      rw [show values12 (47 : Fin 154) = Real.sqrt (values11 (47 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (47 : Fin 91)) < (13259 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13259 / 10000 : Real))]
      norm_num
      change values11 (47 : Fin 91) < (175801081 / 100000000 : Real)
      rw [show values11 (47 : Fin 91) = Real.sqrt (values10 (47 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (47 : Fin 54)) < (175801081 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (175801081 / 100000000 : Real))]
      norm_num
      change values10 (47 : Fin 54) < (30906020080768561 / 10000000000000000 : Real)
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (13 : Fin 20) < (30906020080768561 / 10000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values8 (13 : Fin 20) < (209051 / 100000 : Real) := by
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (1 : Fin 8) < (209051 / 100000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values6 (1 : Fin 8) < (272627 / 250000 : Real) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (1 : Fin 5)) < (272627 / 250000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (272627 / 250000 : Real))]
          norm_num
          change values5 (1 : Fin 5) < (74325481129 / 62500000000 : Real)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change Real.sqrt (Real.sqrt 2) < (74325481129 / 62500000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (74325481129 / 62500000000 : Real))]
          norm_num
          change Real.sqrt 2 < (5524277145057335114641 / 3906250000000000000000 : Real)
          change Real.sqrt (2) < (5524277145057335114641 / 3906250000000000000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5524277145057335114641 / 3906250000000000000000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1163 / 500 : Real) < values14 (313 : Fin 455) := by
    rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    change (1163 / 500 : Real) < Real.sqrt (values13 (261 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (1352569 / 250000 : Real) < values13 (261 : Fin 264)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    change (1352569 / 250000 : Real) < 1 + values11 (88 : Fin 91)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (2207 / 500 : Real) < values11 (88 : Fin 91) := by
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by a158415_twelve_table]
      change (2207 / 500 : Real) < 1 + values9 (30 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (17071 / 5000 : Real) < values9 (30 : Fin 33) := by
        rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
        change (17071 / 5000 : Real) < 1 + values7 (10 : Fin 13)
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (241421 / 100000 : Real) < values7 (10 : Fin 13) := by
          rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
          change (241421 / 100000 : Real) < 1 + values5 (2 : Fin 5)
          have h13 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h14 : (1414213 / 1000000 : Real) < values5 (2 : Fin 5) := by
            rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
            change (1414213 / 1000000 : Real) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_313 :
    values14 (313 : Fin 455) < values14 (314 : Fin 455) := by
  have hleft : values14 (313 : Fin 455) < (2327 / 1000 : Real) := by
    rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    change Real.sqrt (values13 (261 : Fin 264)) < (2327 / 1000 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2327 / 1000 : Real))]
    norm_num
    change values13 (261 : Fin 264) < (5414929 / 1000000 : Real)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    change 1 + values11 (88 : Fin 91) < (5414929 / 1000000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (88 : Fin 91) < (44143 / 10000 : Real) := by
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (30 : Fin 33) < (44143 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (30 : Fin 33) < (170711 / 50000 : Real) := by
        rw [show values9 (30 : Fin 33) = 1 + values7 (10 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (10 : Fin 13) < (170711 / 50000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (10 : Fin 13) < (1207107 / 500000 : Real) := by
          rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (2 : Fin 5) < (1207107 / 500000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : values5 (2 : Fin 5) < (1767767 / 1250000 : Real) := by
            rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
            change Real.sqrt (2) < (1767767 / 1250000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1767767 / 1250000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2327 / 1000 : Real) < values14 (314 : Fin 455) := by
    rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    change (2327 / 1000 : Real) < 1 + values12 (48 : Fin 154)
    have h9 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h10 : (167 / 125 : Real) < values12 (48 : Fin 154) := by
      rw [show values12 (48 : Fin 154) = Real.sqrt (values11 (48 : Fin 91)) by a158415_twelve_table]
      change (167 / 125 : Real) < Real.sqrt (values11 (48 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (27889 / 15625 : Real) < values11 (48 : Fin 91)
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by a158415_twelve_table]
      change (27889 / 15625 : Real) < Real.sqrt (values10 (48 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (777796321 / 244140625 : Real) < values10 (48 : Fin 54)
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by a158415_twelve_table]
      change (777796321 / 244140625 : Real) < 1 + values8 (14 : Fin 20)
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (2189 / 1000 : Real) < values8 (14 : Fin 20) := by
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change (2189 / 1000 : Real) < 1 + values6 (2 : Fin 8)
        have h13 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h14 : (2973 / 2500 : Real) < values6 (2 : Fin 8) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change (2973 / 2500 : Real) < Real.sqrt (values5 (2 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (8838729 / 6250000 : Real) < values5 (2 : Fin 5)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change (8838729 / 6250000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_314 :
    values14 (314 : Fin 455) < values14 (315 : Fin 455) := by
  have hleft : values14 (314 : Fin 455) < (5841 / 2500 : Real) := by
    rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    change 1 + values12 (48 : Fin 154) < (5841 / 2500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (48 : Fin 154) < (33409 / 25000 : Real) := by
      rw [show values12 (48 : Fin 154) = Real.sqrt (values11 (48 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (48 : Fin 91)) < (33409 / 25000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (33409 / 25000 : Real))]
      norm_num
      change values11 (48 : Fin 91) < (1116161281 / 625000000 : Real)
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (48 : Fin 54)) < (1116161281 / 625000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1116161281 / 625000000 : Real))]
      norm_num
      change values10 (48 : Fin 54) < (1245816005203560961 / 390625000000000000 : Real)
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (14 : Fin 20) < (1245816005203560961 / 390625000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values8 (14 : Fin 20) < (218921 / 100000 : Real) := by
        rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (2 : Fin 8) < (218921 / 100000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values6 (2 : Fin 8) < (148651 / 125000 : Real) := by
          rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (2 : Fin 5)) < (148651 / 125000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (148651 / 125000 : Real))]
          norm_num
          change values5 (2 : Fin 5) < (22097119801 / 15625000000 : Real)
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (22097119801 / 15625000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (22097119801 / 15625000000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (5841 / 2500 : Real) < values14 (315 : Fin 455) := by
    rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    change (5841 / 2500 : Real) < values5 (1 : Fin 5) + values8 (4 : Fin 20)
    have h7 : (1189207 / 1000000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189207 / 1000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1414213288849 / 1000000000000 : Real) < Real.sqrt 2
      change (1414213288849 / 1000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (717 / 625 : Real) < values8 (4 : Fin 20) := by
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change (717 / 625 : Real) < Real.sqrt (values7 (4 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (514089 / 390625 : Real) < values7 (4 : Fin 13)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (514089 / 390625 : Real) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (264287499921 / 152587890625 : Real) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (264287499921 / 152587890625 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (69847882614492575006241 / 23283064365386962890625 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (69847882614492575006241 / 23283064365386962890625 : Real) < 1 + 2
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_315 :
    values14 (315 : Fin 455) < values14 (316 : Fin 455) := by
  have hleft : values14 (315 : Fin 455) < (2337 / 1000 : Real) := by
    rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (4 : Fin 20) < (2337 / 1000 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (4 : Fin 20) < (11473 / 10000 : Real) := by
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (4 : Fin 13)) < (11473 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11473 / 10000 : Real))]
      norm_num
      change values7 (4 : Fin 13) < (131629729 / 100000000 : Real)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (131629729 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (131629729 / 100000000 : Real))]
      norm_num
      change values6 (4 : Fin 8) < (17326385556613441 / 10000000000000000 : Real)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17326385556613441 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17326385556613441 / 10000000000000000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 2 < (20001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2337 / 1000 : Real) < values14 (316 : Fin 455) := by
    rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    change (2337 / 1000 : Real) < 1 + values12 (49 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1359 / 1000 : Real) < values12 (49 : Fin 154) := by
      rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by a158415_twelve_table]
      change (1359 / 1000 : Real) < Real.sqrt (values11 (49 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1846881 / 1000000 : Real) < values11 (49 : Fin 91)
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by a158415_twelve_table]
      change (1846881 / 1000000 : Real) < Real.sqrt (values10 (49 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3410969428161 / 1000000000000 : Real) < values10 (49 : Fin 54)
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change (3410969428161 / 1000000000000 : Real) < 1 + values8 (15 : Fin 20)
      have h7 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h8 : (1207 / 500 : Real) < values8 (15 : Fin 20) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change (1207 / 500 : Real) < 1 + values6 (3 : Fin 8)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (7071 / 5000 : Real) < values6 (3 : Fin 8) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (7071 / 5000 : Real) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (49999041 / 25000000 : Real) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (49999041 / 25000000 : Real) < 1 + 1
          have h11 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h12 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_316 :
    values14 (316 : Fin 455) < values14 (317 : Fin 455) := by
  have hleft : values14 (316 : Fin 455) < (59 / 25 : Real) := by
    rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    change 1 + values12 (49 : Fin 154) < (59 / 25 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (49 : Fin 154) < (6797 / 5000 : Real) := by
      rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (49 : Fin 91)) < (6797 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (6797 / 5000 : Real))]
      norm_num
      change values11 (49 : Fin 91) < (46199209 / 25000000 : Real)
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (49 : Fin 54)) < (46199209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (46199209 / 25000000 : Real))]
      norm_num
      change values10 (49 : Fin 54) < (2134366912225681 / 625000000000000 : Real)
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (15 : Fin 20) < (2134366912225681 / 625000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values8 (15 : Fin 20) < (24143 / 10000 : Real) := by
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (3 : Fin 8) < (24143 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (3 : Fin 8) < (70711 / 50000 : Real) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
          change values5 (3 : Fin 5) < (5000045521 / 2500000000 : Real)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (5000045521 / 2500000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (59 / 25 : Real) < values14 (317 : Fin 455) := by
    rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    change (59 / 25 : Real) < values5 (1 : Fin 5) + values8 (5 : Fin 20)
    have h9 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1189 / 1000 : Real) < values8 (5 : Fin 20) := by
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (values7 (5 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < values7 (5 : Fin 13)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change (1413721 / 1000000 : Real) < Real.sqrt (values6 (5 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : Real) < values6 (5 : Fin 8)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : Real) < 1 + 1
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (9999 / 10000 : Real) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_317 :
    values14 (317 : Fin 455) < values14 (318 : Fin 455) := by
  have hleft : values14 (317 : Fin 455) < (2379 / 1000 : Real) := by
    rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (5 : Fin 20) < (2379 / 1000 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (5 : Fin 20) < (11893 / 10000 : Real) := by
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change values7 (5 : Fin 13) < (141443449 / 100000000 : Real)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
      change values6 (5 : Fin 8) < (20006249265015601 / 10000000000000000 : Real)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20006249265015601 / 10000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2379 / 1000 : Real) < values14 (318 : Fin 455) := by
    rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    change (2379 / 1000 : Real) < 1 + values12 (50 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1389 / 1000 : Real) < values12 (50 : Fin 154) := by
      rw [show values12 (50 : Fin 154) = Real.sqrt (values11 (50 : Fin 91)) by a158415_twelve_table]
      change (1389 / 1000 : Real) < Real.sqrt (values11 (50 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1929321 / 1000000 : Real) < values11 (50 : Fin 91)
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by a158415_twelve_table]
      change (1929321 / 1000000 : Real) < Real.sqrt (values10 (50 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3722279521041 / 1000000000000 : Real) < values10 (50 : Fin 54)
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change (3722279521041 / 1000000000000 : Real) < 1 + values8 (16 : Fin 20)
      have h7 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h8 : (683 / 250 : Real) < values8 (16 : Fin 20) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change (683 / 250 : Real) < 1 + values6 (4 : Fin 8)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (34641 / 20000 : Real) < values6 (4 : Fin 8) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change (34641 / 20000 : Real) < Real.sqrt (values5 (4 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1199998881 / 400000000 : Real) < values5 (4 : Fin 5)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change (1199998881 / 400000000 : Real) < 1 + 2
          have h11 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          have h12 : (19999999 / 10000000 : Real) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_318 :
    values14 (318 : Fin 455) < values14 (319 : Fin 455) := by
  have hleft : values14 (318 : Fin 455) < (239 / 100 : Real) := by
    rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    change 1 + values12 (50 : Fin 154) < (239 / 100 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (50 : Fin 154) < (8687 / 6250 : Real) := by
      rw [show values12 (50 : Fin 154) = Real.sqrt (values11 (50 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (50 : Fin 91)) < (8687 / 6250 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (8687 / 6250 : Real))]
      norm_num
      change values11 (50 : Fin 91) < (75463969 / 39062500 : Real)
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (50 : Fin 54)) < (75463969 / 39062500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (75463969 / 39062500 : Real))]
      norm_num
      change values10 (50 : Fin 54) < (5694810617232961 / 1525878906250000 : Real)
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (16 : Fin 20) < (5694810617232961 / 1525878906250000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values8 (16 : Fin 20) < (136603 / 50000 : Real) := by
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (4 : Fin 8) < (136603 / 50000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values6 (4 : Fin 8) < (1732051 / 1000000 : Real) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (1732051 / 1000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1732051 / 1000000 : Real))]
          norm_num
          change values5 (4 : Fin 5) < (3000000666601 / 1000000000000 : Real)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (3000000666601 / 1000000000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : 2 < (20000001 / 10000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (239 / 100 : Real) < values14 (319 : Fin 455) := by
    rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    change (239 / 100 : Real) < values6 (1 : Fin 8) + values7 (4 : Fin 13)
    have h9 : (109 / 100 : Real) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < Real.sqrt 2
      change (141158161 / 100000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (329 / 250 : Real) < values7 (4 : Fin 13) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (329 / 250 : Real) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : Real) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (108241 / 62500 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (11716114081 / 3906250000 : Real) < 1 + 2
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (19999 / 10000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_319 :
    values14 (319 : Fin 455) < values14 (320 : Fin 455) := by
  have hleft : values14 (319 : Fin 455) < (2407 / 1000 : Real) := by
    rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    change values6 (1 : Fin 8) + values7 (4 : Fin 13) < (2407 / 1000 : Real)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : Real) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (29735209 / 25000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change Real.sqrt 2 < (884182654273681 / 625000000000000 : Real)
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
    have h2 : values7 (4 : Fin 13) < (13161 / 10000 : Real) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (13161 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
      norm_num
      change values6 (4 : Fin 8) < (173211921 / 100000000 : Real)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (173211921 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (30002369576510241 / 10000000000000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30002369576510241 / 10000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2407 / 1000 : Real) < values14 (320 : Fin 455) := by
    rw [show values14 (320 : Fin 455) = 1 + values12 (51 : Fin 154) by rfl]
    change (2407 / 1000 : Real) < 1 + values12 (51 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (707 / 500 : Real) < values12 (51 : Fin 154) := by
      rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by a158415_twelve_table]
      change (707 / 500 : Real) < Real.sqrt (values11 (51 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : Real) < values11 (51 : Fin 91)
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by a158415_twelve_table]
      change (499849 / 250000 : Real) < Real.sqrt (values10 (51 : Fin 54))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (249849022801 / 62500000000 : Real) < values10 (51 : Fin 54)
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by a158415_twelve_table]
      change (249849022801 / 62500000000 : Real) < 1 + values8 (17 : Fin 20)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (29999 / 10000 : Real) < values8 (17 : Fin 20) := by
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change (29999 / 10000 : Real) < 1 + values6 (5 : Fin 8)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (199999 / 100000 : Real) < values6 (5 : Fin 8) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : Real) < 1 + 1
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_322 :
    values14 (322 : Fin 455) < values14 (323 : Fin 455) := by
  have hleft : values14 (322 : Fin 455) < (1211 / 500 : Real) := by
    rw [show values14 (322 : Fin 455) = 1 + values12 (53 : Fin 154) by rfl]
    change 1 + values12 (53 : Fin 154) < (1211 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (53 : Fin 154) < (71097 / 50000 : Real) := by
      rw [show values12 (53 : Fin 154) = Real.sqrt (values11 (53 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (53 : Fin 91)) < (71097 / 50000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (71097 / 50000 : Real))]
      norm_num
      change values11 (53 : Fin 91) < (5054783409 / 2500000000 : Real)
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (2 : Fin 33) < (5054783409 / 2500000000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (2 : Fin 33) < (10219 / 10000 : Real) := by
        rw [show values9 (2 : Fin 33) = Real.sqrt (values8 (2 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (2 : Fin 20)) < (10219 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10219 / 10000 : Real))]
        norm_num
        change values8 (2 : Fin 20) < (104427961 / 100000000 : Real)
        rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (2 : Fin 13)) < (104427961 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (104427961 / 100000000 : Real))]
        norm_num
        change values7 (2 : Fin 13) < (10905199038617521 / 10000000000000000 : Real)
        rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (2 : Fin 8)) < (10905199038617521 / 10000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10905199038617521 / 10000000000000000 : Real))]
        norm_num
        change values6 (2 : Fin 8) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real)
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118923366071864504274670928185441 / 100000000000000000000000000000000 : Real))]
        norm_num
        change values5 (2 : Fin 5) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142766997862693493695017618958027938788793762779687152884364481 / 10000000000000000000000000000000000000000000000000000000000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (1211 / 500 : Real) < values14 (323 : Fin 455) := by
    rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    change (1211 / 500 : Real) < Real.sqrt 2 + values9 (1 : Fin 33)
    have h5 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (101 / 100 : Real) < values9 (1 : Fin 33) := by
      rw [show values9 (1 : Fin 33) = Real.sqrt (values8 (1 : Fin 20)) by a158415_twelve_table]
      change (101 / 100 : Real) < Real.sqrt (values8 (1 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10201 / 10000 : Real) < values8 (1 : Fin 20)
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change (10201 / 10000 : Real) < Real.sqrt (values7 (1 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (104060401 / 100000000 : Real) < values7 (1 : Fin 13)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (104060401 / 100000000 : Real) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10828567056280801 / 10000000000000000 : Real) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (10828567056280801 / 10000000000000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (117257864492369852051862561201601 / 100000000000000000000000000000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (117257864492369852051862561201601 / 100000000000000000000000000000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (13749406785310970541622913505711040449564178320493809360964963201 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt 2
      change (13749406785310970541622913505711040449564178320493809360964963201 / 10000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_323 :
    values14 (323 : Fin 455) < values14 (324 : Fin 455) := by
  have hleft : values14 (323 : Fin 455) < (1213 / 500 : Real) := by
    rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (1 : Fin 33) < (1213 / 500 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (1 : Fin 33) < (1011 / 1000 : Real) := by
      rw [show values9 (1 : Fin 33) = Real.sqrt (values8 (1 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (1 : Fin 20)) < (1011 / 1000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1011 / 1000 : Real))]
      norm_num
      change values8 (1 : Fin 20) < (1022121 / 1000000 : Real)
      rw [show values8 (1 : Fin 20) = Real.sqrt (values7 (1 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (1 : Fin 13)) < (1022121 / 1000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1022121 / 1000000 : Real))]
      norm_num
      change values7 (1 : Fin 13) < (1044731338641 / 1000000000000 : Real)
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (1044731338641 / 1000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1044731338641 / 1000000000000 : Real))]
      norm_num
      change values6 (1 : Fin 8) < (1091463569938615819726881 / 1000000000000000000000000 : Real)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (1091463569938615819726881 / 1000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1091463569938615819726881 / 1000000000000000000000000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (1191292724503147706918923940038142771789433988161 / 1000000000000000000000000000000000000000000000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (1191292724503147706918923940038142771789433988161 / 1000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1191292724503147706918923940038142771789433988161 / 1000000000000000000000000000000000000000000000000 : Real))]
      norm_num
      change Real.sqrt 2 < (1419178355454132580952754710331474914693657724176897545763266549913419789963289489925781888161921 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      change Real.sqrt (2) < (1419178355454132580952754710331474914693657724176897545763266549913419789963289489925781888161921 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1419178355454132580952754710331474914693657724176897545763266549913419789963289489925781888161921 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (1213 / 500 : Real) < values14 (324 : Fin 455) := by
    rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    change (1213 / 500 : Real) < 1 + values12 (54 : Fin 154)
    have h3 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h4 : (1429 / 1000 : Real) < values12 (54 : Fin 154) := by
      rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by a158415_twelve_table]
      change (1429 / 1000 : Real) < Real.sqrt (values11 (54 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2042041 / 1000000 : Real) < values11 (54 : Fin 91)
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by a158415_twelve_table]
      change (2042041 / 1000000 : Real) < 1 + values9 (3 : Fin 33)
      have h5 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h6 : (261 / 250 : Real) < values9 (3 : Fin 33) := by
        rw [show values9 (3 : Fin 33) = Real.sqrt (values8 (3 : Fin 20)) by a158415_twelve_table]
        change (261 / 250 : Real) < Real.sqrt (values8 (3 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (68121 / 62500 : Real) < values8 (3 : Fin 20)
        rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
        change (68121 / 62500 : Real) < Real.sqrt (values7 (3 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (4640470641 / 3906250000 : Real) < values7 (3 : Fin 13)
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change (4640470641 / 3906250000 : Real) < Real.sqrt (values6 (3 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (21533967769982950881 / 15258789062500000000 : Real) < values6 (3 : Fin 8)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < 1 + 1
        have h7 : (999 / 1000 : Real) < 1 := by
          norm_num
        have h8 : (999 / 1000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_324 :
    values14 (324 : Fin 455) < values14 (325 : Fin 455) := by
  have hleft : values14 (324 : Fin 455) < (243 / 100 : Real) := by
    rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    change 1 + values12 (54 : Fin 154) < (243 / 100 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (54 : Fin 154) < (7149 / 5000 : Real) := by
      rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (54 : Fin 91)) < (7149 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (7149 / 5000 : Real))]
      norm_num
      change values11 (54 : Fin 91) < (51108201 / 25000000 : Real)
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (3 : Fin 33) < (51108201 / 25000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (3 : Fin 33) < (26107 / 25000 : Real) := by
        rw [show values9 (3 : Fin 33) = Real.sqrt (values8 (3 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (3 : Fin 20)) < (26107 / 25000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (26107 / 25000 : Real))]
        norm_num
        change values8 (3 : Fin 20) < (681575449 / 625000000 : Real)
        rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (3 : Fin 13)) < (681575449 / 625000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (681575449 / 625000000 : Real))]
        norm_num
        change values7 (3 : Fin 13) < (464545092679551601 / 390625000000000000 : Real)
        rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (3 : Fin 8)) < (464545092679551601 / 390625000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (464545092679551601 / 390625000000000000 : Real))]
        norm_num
        change values6 (3 : Fin 8) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (3 : Fin 5)) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (215802143132653186472374962421663201 / 152587890625000000000000000000000000 : Real))]
        norm_num
        change values5 (3 : Fin 5) < (46570564980646132850631122261553460526945389186084493276146579077566401 / 23283064365386962890625000000000000000000000000000000000000000000000000 : Real)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (46570564980646132850631122261553460526945389186084493276146579077566401 / 23283064365386962890625000000000000000000000000000000000000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 1 < (100001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (243 / 100 : Real) < values14 (325 : Fin 455) := by
    rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    change (243 / 100 : Real) < values5 (1 : Fin 5) + values8 (6 : Fin 20)
    have h7 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (623 / 500 : Real) < values8 (6 : Fin 20) := by
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (623 / 500 : Real) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : Real) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (388129 / 250000 : Real) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : Real) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (150644120641 / 62500000000 : Real) < 1 + Real.sqrt 2
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_325 :
    values14 (325 : Fin 455) < values14 (326 : Fin 455) := by
  have hleft : values14 (325 : Fin 455) < (609 / 250 : Real) := by
    rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (6 : Fin 20) < (609 / 250 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (6 : Fin 20) < (6233 / 5000 : Real) := by
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (6 : Fin 13)) < (6233 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (6233 / 5000 : Real))]
      norm_num
      change values7 (6 : Fin 13) < (38850289 / 25000000 : Real)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (38850289 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (38850289 / 25000000 : Real))]
      norm_num
      change values6 (6 : Fin 8) < (1509344955383521 / 625000000000000 : Real)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (1509344955383521 / 625000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : Real.sqrt 2 < (14143 / 10000 : Real) := by
        change Real.sqrt (2) < (14143 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (609 / 250 : Real) < values14 (326 : Fin 455) := by
    rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    change (609 / 250 : Real) < Real.sqrt 2 + values9 (2 : Fin 33)
    have h5 : (7071 / 5000 : Real) < Real.sqrt 2 := by
      change (7071 / 5000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (102189 / 100000 : Real) < values9 (2 : Fin 33) := by
      rw [show values9 (2 : Fin 33) = Real.sqrt (values8 (2 : Fin 20)) by a158415_twelve_table]
      change (102189 / 100000 : Real) < Real.sqrt (values8 (2 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (10442591721 / 10000000000 : Real) < values8 (2 : Fin 20)
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change (10442591721 / 10000000000 : Real) < Real.sqrt (values7 (2 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (109047721851497741841 / 100000000000000000000 : Real) < values7 (2 : Fin 13)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change (109047721851497741841 / 100000000000000000000 : Real) < Real.sqrt (values6 (2 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11891405641001618093863193082322282069281 / 10000000000000000000000000000000000000000 : Real) < values6 (2 : Fin 8)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change (11891405641001618093863193082322282069281 / 10000000000000000000000000000000000000000 : Real) < Real.sqrt (values5 (2 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141405528118845103701984886021026474860395882942331700231681873560264043283856961 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values5 (2 : Fin 5)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change (141405528118845103701984886021026474860395882942331700231681873560264043283856961 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_326 :
    values14 (326 : Fin 455) < values14 (327 : Fin 455) := by
  have hleft : values14 (326 : Fin 455) < (2437 / 1000 : Real) := by
    rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (2 : Fin 33) < (2437 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (2 : Fin 33) < (511 / 500 : Real) := by
      rw [show values9 (2 : Fin 33) = Real.sqrt (values8 (2 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (2 : Fin 20)) < (511 / 500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (511 / 500 : Real))]
      norm_num
      change values8 (2 : Fin 20) < (261121 / 250000 : Real)
      rw [show values8 (2 : Fin 20) = Real.sqrt (values7 (2 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (2 : Fin 13)) < (261121 / 250000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (261121 / 250000 : Real))]
      norm_num
      change values7 (2 : Fin 13) < (68184176641 / 62500000000 : Real)
      rw [show values7 (2 : Fin 13) = Real.sqrt (values6 (2 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (2 : Fin 8)) < (68184176641 / 62500000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (68184176641 / 62500000000 : Real))]
      norm_num
      change values6 (2 : Fin 8) < (4649081944211090042881 / 3906250000000000000000 : Real)
      rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (2 : Fin 5)) < (4649081944211090042881 / 3906250000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (4649081944211090042881 / 3906250000000000000000 : Real))]
      norm_num
      change values5 (2 : Fin 5) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real)
      rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
      change Real.sqrt (2) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (21613962923989568949877044687531502418780161 / 15258789062500000000000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (2437 / 1000 : Real) < values14 (327 : Fin 455) := by
    rw [show values14 (327 : Fin 455) = 1 + values12 (55 : Fin 154) by rfl]
    change (2437 / 1000 : Real) < 1 + values12 (55 : Fin 154)
    have h3 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h4 : (1439 / 1000 : Real) < values12 (55 : Fin 154) := by
      rw [show values12 (55 : Fin 154) = Real.sqrt (values11 (55 : Fin 91)) by a158415_twelve_table]
      change (1439 / 1000 : Real) < Real.sqrt (values11 (55 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2070721 / 1000000 : Real) < values11 (55 : Fin 91)
      rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by a158415_twelve_table]
      change (2070721 / 1000000 : Real) < 1 + values9 (4 : Fin 33)
      have h5 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h6 : (1071 / 1000 : Real) < values9 (4 : Fin 33) := by
        rw [show values9 (4 : Fin 33) = Real.sqrt (values8 (4 : Fin 20)) by a158415_twelve_table]
        change (1071 / 1000 : Real) < Real.sqrt (values8 (4 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1147041 / 1000000 : Real) < values8 (4 : Fin 20)
        rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
        change (1147041 / 1000000 : Real) < Real.sqrt (values7 (4 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1315703055681 / 1000000000000 : Real) < values7 (4 : Fin 13)
        rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
        change (1315703055681 / 1000000000000 : Real) < Real.sqrt (values6 (4 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1731074530728320586373761 / 1000000000000000000000000 : Real) < values6 (4 : Fin 8)
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (1731074530728320586373761 / 1000000000000000000000000 : Real) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (2996619030936275334023016331350479057227589285121 / 1000000000000000000000000000000000000000000000000 : Real) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (2996619030936275334023016331350479057227589285121 / 1000000000000000000000000000000000000000000000000 : Real) < 1 + 2
        have h7 : (999 / 1000 : Real) < 1 := by
          norm_num
        have h8 : (1999 / 1000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_329 :
    values14 (329 : Fin 455) < values14 (330 : Fin 455) := by
  have hleft : values14 (329 : Fin 455) < (612371 / 250000 : Real) := by
    rw [show values14 (329 : Fin 455) = 1 + values12 (57 : Fin 154) by rfl]
    change 1 + values12 (57 : Fin 154) < (612371 / 250000 : Real)
    have h1 : 1 < (10000001 / 10000000 : Real) := by
      norm_num
    have h2 : values12 (57 : Fin 154) < (14494837 / 10000000 : Real) := by
      rw [show values12 (57 : Fin 154) = Real.sqrt (values11 (57 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (57 : Fin 91)) < (14494837 / 10000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14494837 / 10000000 : Real))]
      norm_num
      change values11 (57 : Fin 91) < (210100299656569 / 100000000000000 : Real)
      rw [show values11 (57 : Fin 91) = Real.sqrt (values10 (52 : Fin 54)) by a158415_twelve_table]
      change Real.sqrt (values10 (52 : Fin 54)) < (210100299656569 / 100000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (210100299656569 / 100000000000000 : Real))]
      norm_num
      change values10 (52 : Fin 54) < (44142135915780087859344851761 / 10000000000000000000000000000 : Real)
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by a158415_twelve_table]
      change 1 + values8 (18 : Fin 20) < (44142135915780087859344851761 / 10000000000000000000000000000 : Real)
      have h3 : 1 < (1000000001 / 1000000000 : Real) := by
        norm_num
      have h4 : values8 (18 : Fin 20) < (341421357 / 100000000 : Real) := by
        rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (6 : Fin 8) < (341421357 / 100000000 : Real)
        have h5 : 1 < (1000000001 / 1000000000 : Real) := by
          norm_num
        have h6 : values6 (6 : Fin 8) < (2414213563 / 1000000000 : Real) := by
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change 1 + Real.sqrt 2 < (2414213563 / 1000000000 : Real)
          have h7 : 1 < (10000000001 / 10000000000 : Real) := by
            norm_num
          have h8 : Real.sqrt 2 < (1767766953 / 1250000000 : Real) := by
            change Real.sqrt (2) < (1767766953 / 1250000000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1767766953 / 1250000000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (612371 / 250000 : Real) < values14 (330 : Fin 455) := by
    rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    change (612371 / 250000 : Real) < Real.sqrt (values13 (262 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (374998241641 / 62500000000 : Real) < values13 (262 : Fin 264)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    change (374998241641 / 62500000000 : Real) < 1 + values11 (89 : Fin 91)
    have h9 : (999999 / 1000000 : Real) < 1 := by
      norm_num
    have h10 : (4999999 / 1000000 : Real) < values11 (89 : Fin 91) := by
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by a158415_twelve_table]
      change (4999999 / 1000000 : Real) < 1 + values9 (31 : Fin 33)
      have h11 : (9999999 / 10000000 : Real) < 1 := by
        norm_num
      have h12 : (39999999 / 10000000 : Real) < values9 (31 : Fin 33) := by
        rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
        change (39999999 / 10000000 : Real) < 1 + values7 (11 : Fin 13)
        have h13 : (99999999 / 100000000 : Real) < 1 := by
          norm_num
        have h14 : (299999999 / 100000000 : Real) < values7 (11 : Fin 13) := by
          rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
          change (299999999 / 100000000 : Real) < 1 + values5 (3 : Fin 5)
          have h15 : (999999999 / 1000000000 : Real) < 1 := by
            norm_num
          have h16 : (1999999999 / 1000000000 : Real) < values5 (3 : Fin 5) := by
            rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
            change (1999999999 / 1000000000 : Real) < 1 + 1
            have h17 : (9999999999 / 10000000000 : Real) < 1 := by
              norm_num
            have h18 : (9999999999 / 10000000000 : Real) < 1 := by
              norm_num
            linarith
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_330 :
    values14 (330 : Fin 455) < values14 (331 : Fin 455) := by
  have hleft : values14 (330 : Fin 455) < (49 / 20 : Real) := by
    rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    change Real.sqrt (values13 (262 : Fin 264)) < (49 / 20 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (49 / 20 : Real))]
    norm_num
    change values13 (262 : Fin 264) < (2401 / 400 : Real)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    change 1 + values11 (89 : Fin 91) < (2401 / 400 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (89 : Fin 91) < (50001 / 10000 : Real) := by
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (31 : Fin 33) < (50001 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (31 : Fin 33) < (400001 / 100000 : Real) := by
        rw [show values9 (31 : Fin 33) = 1 + values7 (11 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (11 : Fin 13) < (400001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (11 : Fin 13) < (3000001 / 1000000 : Real) := by
          rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (3 : Fin 5) < (3000001 / 1000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : values5 (3 : Fin 5) < (20000001 / 10000000 : Real) := by
            rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
            change 1 + 1 < (20000001 / 10000000 : Real)
            have h9 : 1 < (100000001 / 100000000 : Real) := by
              norm_num
            have h10 : 1 < (100000001 / 100000000 : Real) := by
              norm_num
            linarith
          linarith
        linarith
      linarith
    linarith
  have hright : (49 / 20 : Real) < values14 (331 : Fin 455) := by
    rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    change (49 / 20 : Real) < 1 + values12 (58 : Fin 154)
    have h11 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h12 : (727 / 500 : Real) < values12 (58 : Fin 154) := by
      rw [show values12 (58 : Fin 154) = Real.sqrt (values11 (58 : Fin 91)) by a158415_twelve_table]
      change (727 / 500 : Real) < Real.sqrt (values11 (58 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (528529 / 250000 : Real) < values11 (58 : Fin 91)
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by a158415_twelve_table]
      change (528529 / 250000 : Real) < 1 + values9 (6 : Fin 33)
      have h13 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h14 : (279 / 250 : Real) < values9 (6 : Fin 33) := by
        rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
        change (279 / 250 : Real) < Real.sqrt (values8 (6 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (77841 / 62500 : Real) < values8 (6 : Fin 20)
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change (77841 / 62500 : Real) < Real.sqrt (values7 (6 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (6059221281 / 3906250000 : Real) < values7 (6 : Fin 13)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change (6059221281 / 3906250000 : Real) < Real.sqrt (values6 (6 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (36714162532123280961 / 15258789062500000000 : Real) < values6 (6 : Fin 8)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change (36714162532123280961 / 15258789062500000000 : Real) < 1 + Real.sqrt 2
        have h15 : (999 / 1000 : Real) < 1 := by
          norm_num
        have h16 : (707 / 500 : Real) < Real.sqrt 2 := by
          change (707 / 500 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_331 :
    values14 (331 : Fin 455) < values14 (332 : Fin 455) := by
  have hleft : values14 (331 : Fin 455) < (491 / 200 : Real) := by
    rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    change 1 + values12 (58 : Fin 154) < (491 / 200 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (58 : Fin 154) < (145481 / 100000 : Real) := by
      rw [show values12 (58 : Fin 154) = Real.sqrt (values11 (58 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (58 : Fin 91)) < (145481 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (145481 / 100000 : Real))]
      norm_num
      change values11 (58 : Fin 91) < (21164721361 / 10000000000 : Real)
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (6 : Fin 33) < (21164721361 / 10000000000 : Real)
      have h3 : 1 < (10000001 / 10000000 : Real) := by
        norm_num
      have h4 : values9 (6 : Fin 33) < (111647 / 100000 : Real) := by
        rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (6 : Fin 20)) < (111647 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (111647 / 100000 : Real))]
        norm_num
        change values8 (6 : Fin 20) < (12465052609 / 10000000000 : Real)
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (6 : Fin 13)) < (12465052609 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12465052609 / 10000000000 : Real))]
        norm_num
        change values7 (6 : Fin 13) < (155377536545137706881 / 100000000000000000000 : Real)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (155377536545137706881 / 100000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (155377536545137706881 / 100000000000000000000 : Real))]
        norm_num
        change values6 (6 : Fin 8) < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : Real)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : Real.sqrt 2 < (707107 / 500000 : Real) := by
          change Real.sqrt (2) < (707107 / 500000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (491 / 200 : Real) < values14 (332 : Fin 455) := by
    rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    change (491 / 200 : Real) < Real.sqrt 2 + values9 (3 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (261 / 250 : Real) < values9 (3 : Fin 33) := by
      rw [show values9 (3 : Fin 33) = Real.sqrt (values8 (3 : Fin 20)) by a158415_twelve_table]
      change (261 / 250 : Real) < Real.sqrt (values8 (3 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : Real) < values8 (3 : Fin 20)
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change (68121 / 62500 : Real) < Real.sqrt (values7 (3 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : Real) < values7 (3 : Fin 13)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change (4640470641 / 3906250000 : Real) < Real.sqrt (values6 (3 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : Real) < values6 (3 : Fin 8)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt (values5 (3 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < values5 (3 : Fin 5)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change (463711767918664502541894501412458676161 / 232830643653869628906250000000000000000 : Real) < 1 + 1
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (999 / 1000 : Real) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_332 :
    values14 (332 : Fin 455) < values14 (333 : Fin 455) := by
  have hleft : values14 (332 : Fin 455) < (2459 / 1000 : Real) := by
    rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (3 : Fin 33) < (2459 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (3 : Fin 33) < (10443 / 10000 : Real) := by
      rw [show values9 (3 : Fin 33) = Real.sqrt (values8 (3 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (3 : Fin 20)) < (10443 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443 / 10000 : Real))]
      norm_num
      change values8 (3 : Fin 20) < (109056249 / 100000000 : Real)
      rw [show values8 (3 : Fin 20) = Real.sqrt (values7 (3 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (3 : Fin 13)) < (109056249 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109056249 / 100000000 : Real))]
      norm_num
      change values7 (3 : Fin 13) < (11893265445950001 / 10000000000000000 : Real)
      rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (3 : Fin 8)) < (11893265445950001 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893265445950001 / 10000000000000000 : Real))]
      norm_num
      change values6 (3 : Fin 8) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (3 : Fin 5)) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values5 (3 : Fin 5) < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (20008035443654803575511477523052719335287620733591301476783800001 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2459 / 1000 : Real) < values14 (333 : Fin 455) := by
    rw [show values14 (333 : Fin 455) = 1 + values12 (59 : Fin 154) by rfl]
    change (2459 / 1000 : Real) < 1 + values12 (59 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (293 / 200 : Real) < values12 (59 : Fin 154) := by
      rw [show values12 (59 : Fin 154) = Real.sqrt (values11 (59 : Fin 91)) by a158415_twelve_table]
      change (293 / 200 : Real) < Real.sqrt (values11 (59 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (85849 / 40000 : Real) < values11 (59 : Fin 91)
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by a158415_twelve_table]
      change (85849 / 40000 : Real) < 1 + values9 (7 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (1147 / 1000 : Real) < values9 (7 : Fin 33) := by
        rw [show values9 (7 : Fin 33) = Real.sqrt (values8 (7 : Fin 20)) by a158415_twelve_table]
        change (1147 / 1000 : Real) < Real.sqrt (values8 (7 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1315609 / 1000000 : Real) < values8 (7 : Fin 20)
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change (1315609 / 1000000 : Real) < Real.sqrt (values7 (7 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1730827040881 / 1000000000000 : Real) < values7 (7 : Fin 13)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (1730827040881 / 1000000000000 : Real) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (2995762245444878845256161 / 1000000000000000000000000 : Real) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (2995762245444878845256161 / 1000000000000000000000000 : Real) < 1 + 2
        have h9 : (999 / 1000 : Real) < 1 := by
          norm_num
        have h10 : (1999 / 1000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_334 :
    values14 (334 : Fin 455) < values14 (335 : Fin 455) := by
  have hleft : values14 (334 : Fin 455) < (62 / 25 : Real) := by
    rw [show values14 (334 : Fin 455) = 1 + values12 (60 : Fin 154) by rfl]
    change 1 + values12 (60 : Fin 154) < (62 / 25 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (60 : Fin 154) < (3699 / 2500 : Real) := by
      rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (60 : Fin 91)) < (3699 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3699 / 2500 : Real))]
      norm_num
      change values11 (60 : Fin 91) < (13682601 / 6250000 : Real)
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (8 : Fin 33) < (13682601 / 6250000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (8 : Fin 33) < (118921 / 100000 : Real) := by
        rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (8 : Fin 20)) < (118921 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
        norm_num
        change values8 (8 : Fin 20) < (14142204241 / 10000000000 : Real)
        rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (8 : Fin 13)) < (14142204241 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
        norm_num
        change values7 (8 : Fin 13) < (200001940794158386081 / 100000000000000000000 : Real)
        rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (0 : Fin 5) < (200001940794158386081 / 100000000000000000000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values5 (0 : Fin 5) < (1000001 / 1000000 : Real) := by
          rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
          change Real.sqrt (1) < (1000001 / 1000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1000001 / 1000000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (62 / 25 : Real) < values14 (335 : Fin 455) := by
    rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    change (62 / 25 : Real) < Real.sqrt 2 + values9 (4 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1071 / 1000 : Real) < values9 (4 : Fin 33) := by
      rw [show values9 (4 : Fin 33) = Real.sqrt (values8 (4 : Fin 20)) by a158415_twelve_table]
      change (1071 / 1000 : Real) < Real.sqrt (values8 (4 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1147041 / 1000000 : Real) < values8 (4 : Fin 20)
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change (1147041 / 1000000 : Real) < Real.sqrt (values7 (4 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1315703055681 / 1000000000000 : Real) < values7 (4 : Fin 13)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (1315703055681 / 1000000000000 : Real) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1731074530728320586373761 / 1000000000000000000000000 : Real) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (1731074530728320586373761 / 1000000000000000000000000 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2996619030936275334023016331350479057227589285121 / 1000000000000000000000000000000000000000000000000 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (2996619030936275334023016331350479057227589285121 / 1000000000000000000000000000000000000000000000000 : Real) < 1 + 2
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (1999 / 1000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_335 :
    values14 (335 : Fin 455) < values14 (336 : Fin 455) := by
  have hleft : values14 (335 : Fin 455) < (1243 / 500 : Real) := by
    rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (4 : Fin 33) < (1243 / 500 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (4 : Fin 33) < (10711 / 10000 : Real) := by
      rw [show values9 (4 : Fin 33) = Real.sqrt (values8 (4 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (4 : Fin 20)) < (10711 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10711 / 10000 : Real))]
      norm_num
      change values8 (4 : Fin 20) < (114725521 / 100000000 : Real)
      rw [show values8 (4 : Fin 20) = Real.sqrt (values7 (4 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (4 : Fin 13)) < (114725521 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (114725521 / 100000000 : Real))]
      norm_num
      change values7 (4 : Fin 13) < (13161945168721441 / 10000000000000000 : Real)
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (13161945168721441 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161945168721441 / 10000000000000000 : Real))]
      norm_num
      change values6 (4 : Fin 8) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173236800624429681992414653116481 / 100000000000000000000000000000000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (30010989090588400256679505311166483916986617065427311405753823361 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30010989090588400256679505311166483916986617065427311405753823361 / 10000000000000000000000000000000000000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 2 < (20001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (1243 / 500 : Real) < values14 (336 : Fin 455) := by
    rw [show values14 (336 : Fin 455) = 1 + values12 (61 : Fin 154) by rfl]
    change (1243 / 500 : Real) < 1 + values12 (61 : Fin 154)
    have h5 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h6 : (186 / 125 : Real) < values12 (61 : Fin 154) := by
      rw [show values12 (61 : Fin 154) = Real.sqrt (values11 (61 : Fin 91)) by a158415_twelve_table]
      change (186 / 125 : Real) < Real.sqrt (values11 (61 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (34596 / 15625 : Real) < values11 (61 : Fin 91)
      rw [show values11 (61 : Fin 91) = 1 + values9 (9 : Fin 33) by a158415_twelve_table]
      change (34596 / 15625 : Real) < 1 + values9 (9 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (152 / 125 : Real) < values9 (9 : Fin 33) := by
        rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
        change (152 / 125 : Real) < Real.sqrt (values8 (9 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (23104 / 15625 : Real) < values8 (9 : Fin 20)
        rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
        change (23104 / 15625 : Real) < Real.sqrt (values7 (9 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (533794816 / 244140625 : Real) < values7 (9 : Fin 13)
        rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
        change (533794816 / 244140625 : Real) < 1 + values5 (1 : Fin 5)
        have h9 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h10 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1413721 / 1000000 : Real) < Real.sqrt 2
          change (1413721 / 1000000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_338 :
    values14 (338 : Fin 455) < values14 (339 : Fin 455) := by
  have hleft : values14 (338 : Fin 455) < (2499 / 1000 : Real) := by
    rw [show values14 (338 : Fin 455) = 1 + values12 (63 : Fin 154) by rfl]
    change 1 + values12 (63 : Fin 154) < (2499 / 1000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (63 : Fin 154) < (37471 / 25000 : Real) := by
      rw [show values12 (63 : Fin 154) = Real.sqrt (values11 (63 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (63 : Fin 91)) < (37471 / 25000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (37471 / 25000 : Real))]
      norm_num
      change values11 (63 : Fin 91) < (1404075841 / 625000000 : Real)
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (10 : Fin 33) < (1404075841 / 625000000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (10 : Fin 33) < (124651 / 100000 : Real) := by
        rw [show values9 (10 : Fin 33) = Real.sqrt (values8 (10 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (10 : Fin 20)) < (124651 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (124651 / 100000 : Real))]
        norm_num
        change values8 (10 : Fin 20) < (15537871801 / 10000000000 : Real)
        rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (10 : Fin 13)) < (15537871801 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15537871801 / 10000000000 : Real))]
        norm_num
        change values7 (10 : Fin 13) < (241425460104310983601 / 100000000000000000000 : Real)
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (241425460104310983601 / 100000000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values5 (2 : Fin 5) < (70711 / 50000 : Real) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2499 / 1000 : Real) < values14 (339 : Fin 455) := by
    rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    change (2499 / 1000 : Real) < Real.sqrt 2 + values9 (5 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (109 / 100 : Real) < values9 (5 : Fin 33) := by
      rw [show values9 (5 : Fin 33) = Real.sqrt (values8 (5 : Fin 20)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values8 (5 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values8 (5 : Fin 20)
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (values7 (5 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < values7 (5 : Fin 13)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change (141158161 / 100000000 : Real) < Real.sqrt (values6 (5 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (19925626416901921 / 10000000000000000 : Real) < values6 (5 : Fin 8)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change (19925626416901921 / 10000000000000000 : Real) < 1 + 1
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (999 / 1000 : Real) < 1 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_339 :
    values14 (339 : Fin 455) < values14 (340 : Fin 455) := by
  have hleft : values14 (339 : Fin 455) < (501 / 200 : Real) := by
    rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (5 : Fin 33) < (501 / 200 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (5 : Fin 33) < (5453 / 5000 : Real) := by
      rw [show values9 (5 : Fin 33) = Real.sqrt (values8 (5 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (5 : Fin 20)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values8 (5 : Fin 20) < (29735209 / 25000000 : Real)
      rw [show values8 (5 : Fin 20) = Real.sqrt (values7 (5 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (5 : Fin 13)) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change values7 (5 : Fin 13) < (884182654273681 / 625000000000000 : Real)
      rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (5 : Fin 8)) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
      change values6 (5 : Fin 8) < (781778966118451701933649289761 / 390625000000000000000000000000 : Real)
      rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
      change 1 + 1 < (781778966118451701933649289761 / 390625000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 1 < (10001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (501 / 200 : Real) < values14 (340 : Fin 455) := by
    rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    change (501 / 200 : Real) < values5 (1 : Fin 5) + values8 (7 : Fin 20)
    have h5 : (2973 / 2500 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (2973 / 2500 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (8838729 / 6250000 : Real) < Real.sqrt 2
      change (8838729 / 6250000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (329 / 250 : Real) < values8 (7 : Fin 20) := by
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change (329 / 250 : Real) < Real.sqrt (values7 (7 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : Real) < values7 (7 : Fin 13)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (108241 / 62500 : Real) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : Real) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (11716114081 / 3906250000 : Real) < 1 + 2
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (19999 / 10000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_340 :
    values14 (340 : Fin 455) < values14 (341 : Fin 455) := by
  have hleft : values14 (340 : Fin 455) < (1253 / 500 : Real) := by
    rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (7 : Fin 20) < (1253 / 500 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (7 : Fin 20) < (13161 / 10000 : Real) := by
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (7 : Fin 13)) < (13161 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
      norm_num
      change values7 (7 : Fin 13) < (173211921 / 100000000 : Real)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (173211921 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
      norm_num
      change values6 (7 : Fin 8) < (30002369576510241 / 10000000000000000 : Real)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30002369576510241 / 10000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (1253 / 500 : Real) < values14 (341 : Fin 455) := by
    rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    change (1253 / 500 : Real) < 1 + values12 (64 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1521 / 1000 : Real) < values12 (64 : Fin 154) := by
      rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by a158415_twelve_table]
      change (1521 / 1000 : Real) < Real.sqrt (values11 (64 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2313441 / 1000000 : Real) < values11 (64 : Fin 91)
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by a158415_twelve_table]
      change (2313441 / 1000000 : Real) < 1 + values9 (11 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (329 / 250 : Real) < values9 (11 : Fin 33) := by
        rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
        change (329 / 250 : Real) < Real.sqrt (values8 (11 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108241 / 62500 : Real) < values8 (11 : Fin 20)
        rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
        change (108241 / 62500 : Real) < Real.sqrt (values7 (11 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11716114081 / 3906250000 : Real) < values7 (11 : Fin 13)
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (11716114081 / 3906250000 : Real) < 1 + values5 (3 : Fin 5)
        have h9 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h10 : (19999 / 10000 : Real) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (19999 / 10000 : Real) < 1 + 1
          have h11 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h12 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_341 :
    values14 (341 : Fin 455) < values14 (342 : Fin 455) := by
  have hleft : values14 (341 : Fin 455) < (1261 / 500 : Real) := by
    rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    change 1 + values12 (64 : Fin 154) < (1261 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (64 : Fin 154) < (15219 / 10000 : Real) := by
      rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (64 : Fin 91)) < (15219 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15219 / 10000 : Real))]
      norm_num
      change values11 (64 : Fin 91) < (231617961 / 100000000 : Real)
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (11 : Fin 33) < (231617961 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (11 : Fin 33) < (13161 / 10000 : Real) := by
        rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (11 : Fin 20)) < (13161 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
        norm_num
        change values8 (11 : Fin 20) < (173211921 / 100000000 : Real)
        rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (11 : Fin 13)) < (173211921 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
        norm_num
        change values7 (11 : Fin 13) < (30002369576510241 / 10000000000000000 : Real)
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (3 : Fin 5) < (30002369576510241 / 10000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values5 (3 : Fin 5) < (200001 / 100000 : Real) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (200001 / 100000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1261 / 500 : Real) < values14 (342 : Fin 455) := by
    rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    change (1261 / 500 : Real) < Real.sqrt 2 + values9 (6 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (279 / 250 : Real) < values9 (6 : Fin 33) := by
      rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
      change (279 / 250 : Real) < Real.sqrt (values8 (6 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (77841 / 62500 : Real) < values8 (6 : Fin 20)
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change (77841 / 62500 : Real) < Real.sqrt (values7 (6 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (6059221281 / 3906250000 : Real) < values7 (6 : Fin 13)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (6059221281 / 3906250000 : Real) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (36714162532123280961 / 15258789062500000000 : Real) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (36714162532123280961 / 15258789062500000000 : Real) < 1 + Real.sqrt 2
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_342 :
    values14 (342 : Fin 455) < values14 (343 : Fin 455) := by
  have hleft : values14 (342 : Fin 455) < (2531 / 1000 : Real) := by
    rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (6 : Fin 33) < (2531 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (6 : Fin 33) < (2233 / 2000 : Real) := by
      rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (6 : Fin 20)) < (2233 / 2000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2233 / 2000 : Real))]
      norm_num
      change values8 (6 : Fin 20) < (4986289 / 4000000 : Real)
      rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (6 : Fin 13)) < (4986289 / 4000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (4986289 / 4000000 : Real))]
      norm_num
      change values7 (6 : Fin 13) < (24863077991521 / 16000000000000 : Real)
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (24863077991521 / 16000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (24863077991521 / 16000000000000 : Real))]
      norm_num
      change values6 (6 : Fin 8) < (618172647212455923347893441 / 256000000000000000000000000 : Real)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (618172647212455923347893441 / 256000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : Real.sqrt 2 < (14143 / 10000 : Real) := by
        change Real.sqrt (2) < (14143 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2531 / 1000 : Real) < values14 (343 : Fin 455) := by
    rw [show values14 (343 : Fin 455) = 1 + values12 (65 : Fin 154) by rfl]
    change (2531 / 1000 : Real) < 1 + values12 (65 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (771 / 500 : Real) < values12 (65 : Fin 154) := by
      rw [show values12 (65 : Fin 154) = Real.sqrt (values11 (65 : Fin 91)) by a158415_twelve_table]
      change (771 / 500 : Real) < Real.sqrt (values11 (65 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (594441 / 250000 : Real) < values11 (65 : Fin 91)
      rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by a158415_twelve_table]
      change (594441 / 250000 : Real) < values5 (1 : Fin 5) + values5 (1 : Fin 5)
      have h7 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h8 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_344 :
    values14 (344 : Fin 455) < values14 (345 : Fin 455) := by
  have hleft : values14 (344 : Fin 455) < (1277 / 500 : Real) := by
    rw [show values14 (344 : Fin 455) = 1 + values12 (66 : Fin 154) by rfl]
    change 1 + values12 (66 : Fin 154) < (1277 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (66 : Fin 154) < (7769 / 5000 : Real) := by
      rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (66 : Fin 91)) < (7769 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (7769 / 5000 : Real))]
      norm_num
      change values11 (66 : Fin 91) < (60357361 / 25000000 : Real)
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (12 : Fin 33) < (60357361 / 25000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (12 : Fin 33) < (70711 / 50000 : Real) := by
        rw [show values9 (12 : Fin 33) = Real.sqrt (values8 (12 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (12 : Fin 20)) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
        change values8 (12 : Fin 20) < (5000045521 / 2500000000 : Real)
        rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (12 : Fin 13)) < (5000045521 / 2500000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5000045521 / 2500000000 : Real))]
        norm_num
        change values7 (12 : Fin 13) < (25000455212072161441 / 6250000000000000000 : Real)
        rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (4 : Fin 5) < (25000455212072161441 / 6250000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values5 (4 : Fin 5) < (300001 / 100000 : Real) := by
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (300001 / 100000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 2 < (2000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1277 / 500 : Real) < values14 (345 : Fin 455) := by
    rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    change (1277 / 500 : Real) < Real.sqrt 2 + values9 (7 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1147 / 1000 : Real) < values9 (7 : Fin 33) := by
      rw [show values9 (7 : Fin 33) = Real.sqrt (values8 (7 : Fin 20)) by a158415_twelve_table]
      change (1147 / 1000 : Real) < Real.sqrt (values8 (7 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1315609 / 1000000 : Real) < values8 (7 : Fin 20)
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change (1315609 / 1000000 : Real) < Real.sqrt (values7 (7 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1730827040881 / 1000000000000 : Real) < values7 (7 : Fin 13)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (1730827040881 / 1000000000000 : Real) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2995762245444878845256161 / 1000000000000000000000000 : Real) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (2995762245444878845256161 / 1000000000000000000000000 : Real) < 1 + 2
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (1999 / 1000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_345 :
    values14 (345 : Fin 455) < values14 (346 : Fin 455) := by
  have hleft : values14 (345 : Fin 455) < (1281 / 500 : Real) := by
    rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (7 : Fin 33) < (1281 / 500 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (7 : Fin 33) < (11473 / 10000 : Real) := by
      rw [show values9 (7 : Fin 33) = Real.sqrt (values8 (7 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (7 : Fin 20)) < (11473 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11473 / 10000 : Real))]
      norm_num
      change values8 (7 : Fin 20) < (131629729 / 100000000 : Real)
      rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (7 : Fin 13)) < (131629729 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (131629729 / 100000000 : Real))]
      norm_num
      change values7 (7 : Fin 13) < (17326385556613441 / 10000000000000000 : Real)
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (17326385556613441 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17326385556613441 / 10000000000000000 : Real))]
      norm_num
      change values6 (7 : Fin 8) < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300203636456422859700092701860481 / 100000000000000000000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : 2 < (20001 / 10000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (1281 / 500 : Real) < values14 (346 : Fin 455) := by
    rw [show values14 (346 : Fin 455) = 1 + values12 (67 : Fin 154) by rfl]
    change (1281 / 500 : Real) < 1 + values12 (67 : Fin 154)
    have h5 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h6 : (15639 / 10000 : Real) < values12 (67 : Fin 154) := by
      rw [show values12 (67 : Fin 154) = Real.sqrt (values11 (67 : Fin 91)) by a158415_twelve_table]
      change (15639 / 10000 : Real) < Real.sqrt (values11 (67 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (244578321 / 100000000 : Real) < values11 (67 : Fin 91)
      rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by a158415_twelve_table]
      change (244578321 / 100000000 : Real) < 1 + values9 (13 : Fin 33)
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (28917 / 20000 : Real) < values9 (13 : Fin 33) := by
        rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
        change (28917 / 20000 : Real) < Real.sqrt (values8 (13 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (836192889 / 400000000 : Real) < values8 (13 : Fin 20)
        rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
        change (836192889 / 400000000 : Real) < 1 + values6 (1 : Fin 8)
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (2181 / 2000 : Real) < values6 (1 : Fin 8) := by
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change (2181 / 2000 : Real) < Real.sqrt (values5 (1 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (4756761 / 4000000 : Real) < values5 (1 : Fin 5)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (4756761 / 4000000 : Real) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (22626775211121 / 16000000000000 : Real) < Real.sqrt 2
          change (22626775211121 / 16000000000000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_349 :
    values14 (349 : Fin 455) < values14 (350 : Fin 455) := by
  have hleft : values14 (349 : Fin 455) < (2599 / 1000 : Real) := by
    rw [show values14 (349 : Fin 455) = 1 + values12 (70 : Fin 154) by rfl]
    change 1 + values12 (70 : Fin 154) < (2599 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (70 : Fin 154) < (15981 / 10000 : Real) := by
      rw [show values12 (70 : Fin 154) = Real.sqrt (values11 (70 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (70 : Fin 91)) < (15981 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15981 / 10000 : Real))]
      norm_num
      change values11 (70 : Fin 91) < (255392361 / 100000000 : Real)
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (15 : Fin 33) < (255392361 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (15 : Fin 33) < (7769 / 5000 : Real) := by
        rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (15 : Fin 20)) < (7769 / 5000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (7769 / 5000 : Real))]
        norm_num
        change values8 (15 : Fin 20) < (60357361 / 25000000 : Real)
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (3 : Fin 8) < (60357361 / 25000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (3 : Fin 8) < (70711 / 50000 : Real) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
          change values5 (3 : Fin 5) < (5000045521 / 2500000000 : Real)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (5000045521 / 2500000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2599 / 1000 : Real) < values14 (350 : Fin 455) := by
    rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    change (2599 / 1000 : Real) < Real.sqrt 2 + values9 (8 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1189 / 1000 : Real) < values9 (8 : Fin 33) := by
      rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (values8 (8 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < values8 (8 : Fin 20)
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change (1413721 / 1000000 : Real) < Real.sqrt (values7 (8 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1998607065841 / 1000000000000 : Real) < values7 (8 : Fin 13)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change (1998607065841 / 1000000000000 : Real) < 1 + values5 (0 : Fin 5)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (9999 / 10000 : Real) < values5 (0 : Fin 5) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change (9999 / 10000 : Real) < Real.sqrt (1)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_350 :
    values14 (350 : Fin 455) < values14 (351 : Fin 455) := by
  have hleft : values14 (350 : Fin 455) < (651 / 250 : Real) := by
    rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (8 : Fin 33) < (651 / 250 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (8 : Fin 33) < (11893 / 10000 : Real) := by
      rw [show values9 (8 : Fin 33) = Real.sqrt (values8 (8 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (8 : Fin 20)) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change values8 (8 : Fin 20) < (141443449 / 100000000 : Real)
      rw [show values8 (8 : Fin 20) = Real.sqrt (values7 (8 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (8 : Fin 13)) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
      change values7 (8 : Fin 13) < (20006249265015601 / 10000000000000000 : Real)
      rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (0 : Fin 5) < (20006249265015601 / 10000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values5 (0 : Fin 5) < (10001 / 10000 : Real) := by
        rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
        change Real.sqrt (1) < (10001 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10001 / 10000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (651 / 250 : Real) < values14 (351 : Fin 455) := by
    rw [show values14 (351 : Fin 455) = 1 + values12 (71 : Fin 154) by rfl]
    change (651 / 250 : Real) < 1 + values12 (71 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1613 / 1000 : Real) < values12 (71 : Fin 154) := by
      rw [show values12 (71 : Fin 154) = Real.sqrt (values11 (71 : Fin 91)) by a158415_twelve_table]
      change (1613 / 1000 : Real) < Real.sqrt (values11 (71 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2601769 / 1000000 : Real) < values11 (71 : Fin 91)
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by a158415_twelve_table]
      change (2601769 / 1000000 : Real) < Real.sqrt 2 + values6 (2 : Fin 8)
      have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h8 : (1189 / 1000 : Real) < values6 (2 : Fin 8) := by
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (values5 (2 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < values5 (2 : Fin 5)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_352 :
    values14 (352 : Fin 455) < values14 (353 : Fin 455) := by
  have hleft : values14 (352 : Fin 455) < (2629 / 1000 : Real) := by
    rw [show values14 (352 : Fin 455) = 1 + values12 (72 : Fin 154) by rfl]
    change 1 + values12 (72 : Fin 154) < (2629 / 1000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (72 : Fin 154) < (1018 / 625 : Real) := by
      rw [show values12 (72 : Fin 154) = Real.sqrt (values11 (72 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (72 : Fin 91)) < (1018 / 625 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1018 / 625 : Real))]
      norm_num
      change values11 (72 : Fin 91) < (1036324 / 390625 : Real)
      rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (16 : Fin 33) < (1036324 / 390625 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (16 : Fin 33) < (16529 / 10000 : Real) := by
        rw [show values9 (16 : Fin 33) = Real.sqrt (values8 (16 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (16 : Fin 20)) < (16529 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (16529 / 10000 : Real))]
        norm_num
        change values8 (16 : Fin 20) < (273207841 / 100000000 : Real)
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (4 : Fin 8) < (273207841 / 100000000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values6 (4 : Fin 8) < (86603 / 50000 : Real) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (86603 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (86603 / 50000 : Real))]
          norm_num
          change values5 (4 : Fin 5) < (7500079609 / 2500000000 : Real)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (7500079609 / 2500000000 : Real)
          have h7 : 1 < (100001 / 100000 : Real) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2629 / 1000 : Real) < values14 (353 : Fin 455) := by
    rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    change (2629 / 1000 : Real) < Real.sqrt 2 + values9 (9 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (152 / 125 : Real) < values9 (9 : Fin 33) := by
      rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
      change (152 / 125 : Real) < Real.sqrt (values8 (9 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (23104 / 15625 : Real) < values8 (9 : Fin 20)
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (23104 / 15625 : Real) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (533794816 / 244140625 : Real) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (533794816 / 244140625 : Real) < 1 + values5 (1 : Fin 5)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_353 :
    values14 (353 : Fin 455) < values14 (354 : Fin 455) := by
  have hleft : values14 (353 : Fin 455) < (2631 / 1000 : Real) := by
    rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (9 : Fin 33) < (2631 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (9 : Fin 33) < (3041 / 2500 : Real) := by
      rw [show values9 (9 : Fin 33) = Real.sqrt (values8 (9 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (9 : Fin 20)) < (3041 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3041 / 2500 : Real))]
      norm_num
      change values8 (9 : Fin 20) < (9247681 / 6250000 : Real)
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (9 : Fin 13)) < (9247681 / 6250000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (9247681 / 6250000 : Real))]
      norm_num
      change values7 (9 : Fin 13) < (85519603877761 / 39062500000000 : Real)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (1 : Fin 5) < (85519603877761 / 39062500000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (1 : Fin 5) < (118921 / 100000 : Real) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
        norm_num
        change Real.sqrt 2 < (14142204241 / 10000000000 : Real)
        change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2631 / 1000 : Real) < values14 (354 : Fin 455) := by
    rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    change (2631 / 1000 : Real) < values6 (1 : Fin 8) + values7 (6 : Fin 13)
    have h5 : (109 / 100 : Real) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (109 / 100 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11881 / 10000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (11881 / 10000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (141158161 / 100000000 : Real) < Real.sqrt 2
      change (141158161 / 100000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (1553 / 1000 : Real) < values7 (6 : Fin 13) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (1553 / 1000 : Real) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : Real) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (2411809 / 1000000 : Real) < 1 + Real.sqrt 2
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_354 :
    values14 (354 : Fin 455) < values14 (355 : Fin 455) := by
  have hleft : values14 (354 : Fin 455) < (529 / 200 : Real) := by
    rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    change values6 (1 : Fin 8) + values7 (6 : Fin 13) < (529 / 200 : Real)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : Real) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (29735209 / 25000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change Real.sqrt 2 < (884182654273681 / 625000000000000 : Real)
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
    have h2 : values7 (6 : Fin 13) < (777 / 500 : Real) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (777 / 500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (777 / 500 : Real))]
      norm_num
      change values6 (6 : Fin 8) < (603729 / 250000 : Real)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (603729 / 250000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : Real.sqrt 2 < (14143 / 10000 : Real) := by
        change Real.sqrt (2) < (14143 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (529 / 200 : Real) < values14 (355 : Fin 455) := by
    rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    change (529 / 200 : Real) < Real.sqrt (values13 (263 : Fin 264))
    apply Real.lt_sqrt_of_sq_lt
    norm_num
    change (279841 / 40000 : Real) < values13 (263 : Fin 264)
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    change (279841 / 40000 : Real) < 1 + values11 (90 : Fin 91)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (5999 / 1000 : Real) < values11 (90 : Fin 91) := by
      rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by a158415_twelve_table]
      change (5999 / 1000 : Real) < 1 + values9 (32 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (49999 / 10000 : Real) < values9 (32 : Fin 33) := by
        rw [show values9 (32 : Fin 33) = 1 + values7 (12 : Fin 13) by a158415_twelve_table]
        change (49999 / 10000 : Real) < 1 + values7 (12 : Fin 13)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (399999 / 100000 : Real) < values7 (12 : Fin 13) := by
          rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
          change (399999 / 100000 : Real) < 1 + values5 (4 : Fin 5)
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (2999999 / 1000000 : Real) < values5 (4 : Fin 5) := by
            rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
            change (2999999 / 1000000 : Real) < 1 + 2
            have h13 : (9999999 / 10000000 : Real) < 1 := by
              norm_num
            have h14 : (19999999 / 10000000 : Real) < 2 := by
              norm_num
            linarith
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_355 :
    values14 (355 : Fin 455) < values14 (356 : Fin 455) := by
  have hleft : values14 (355 : Fin 455) < (1323 / 500 : Real) := by
    rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    change Real.sqrt (values13 (263 : Fin 264)) < (1323 / 500 : Real)
    rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1323 / 500 : Real))]
    norm_num
    change values13 (263 : Fin 264) < (1750329 / 250000 : Real)
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    change 1 + values11 (90 : Fin 91) < (1750329 / 250000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values11 (90 : Fin 91) < (60001 / 10000 : Real) := by
      rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (32 : Fin 33) < (60001 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (32 : Fin 33) < (500001 / 100000 : Real) := by
        rw [show values9 (32 : Fin 33) = 1 + values7 (12 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (12 : Fin 13) < (500001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (12 : Fin 13) < (4000001 / 1000000 : Real) := by
          rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (4 : Fin 5) < (4000001 / 1000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : values5 (4 : Fin 5) < (30000001 / 10000000 : Real) := by
            rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
            change 1 + 2 < (30000001 / 10000000 : Real)
            have h9 : 1 < (100000001 / 100000000 : Real) := by
              norm_num
            have h10 : 2 < (200000001 / 100000000 : Real) := by
              norm_num
            linarith
          linarith
        linarith
      linarith
    linarith
  have hright : (1323 / 500 : Real) < values14 (356 : Fin 455) := by
    rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    change (1323 / 500 : Real) < 1 + values12 (73 : Fin 154)
    have h11 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h12 : (413 / 250 : Real) < values12 (73 : Fin 154) := by
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by a158415_twelve_table]
      change (413 / 250 : Real) < Real.sqrt (values11 (73 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (170569 / 62500 : Real) < values11 (73 : Fin 91)
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by a158415_twelve_table]
      change (170569 / 62500 : Real) < 1 + values9 (17 : Fin 33)
      have h13 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h14 : (433 / 250 : Real) < values9 (17 : Fin 33) := by
        rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
        change (433 / 250 : Real) < Real.sqrt (values8 (17 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : Real) < values8 (17 : Fin 20)
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change (187489 / 62500 : Real) < 1 + values6 (5 : Fin 8)
        have h15 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h16 : (199999 / 100000 : Real) < values6 (5 : Fin 8) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : Real) < 1 + 1
          have h17 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h18 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_356 :
    values14 (356 : Fin 455) < values14 (357 : Fin 455) := by
  have hleft : values14 (356 : Fin 455) < (2653 / 1000 : Real) := by
    rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    change 1 + values12 (73 : Fin 154) < (2653 / 1000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (73 : Fin 154) < (16529 / 10000 : Real) := by
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (73 : Fin 91)) < (16529 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (16529 / 10000 : Real))]
      norm_num
      change values11 (73 : Fin 91) < (273207841 / 100000000 : Real)
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (17 : Fin 33) < (273207841 / 100000000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values9 (17 : Fin 33) < (86603 / 50000 : Real) := by
        rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (17 : Fin 20)) < (86603 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (86603 / 50000 : Real))]
        norm_num
        change values8 (17 : Fin 20) < (7500079609 / 2500000000 : Real)
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (5 : Fin 8) < (7500079609 / 2500000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (5 : Fin 8) < (200001 / 100000 : Real) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (200001 / 100000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2653 / 1000 : Real) < values14 (357 : Fin 455) := by
    rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    change (2653 / 1000 : Real) < Real.sqrt 2 + values9 (10 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (623 / 500 : Real) < values9 (10 : Fin 33) := by
      rw [show values9 (10 : Fin 33) = Real.sqrt (values8 (10 : Fin 20)) by a158415_twelve_table]
      change (623 / 500 : Real) < Real.sqrt (values8 (10 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (388129 / 250000 : Real) < values8 (10 : Fin 20)
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change (388129 / 250000 : Real) < Real.sqrt (values7 (10 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (150644120641 / 62500000000 : Real) < values7 (10 : Fin 13)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change (150644120641 / 62500000000 : Real) < 1 + values5 (2 : Fin 5)
      have h11 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h12 : (707 / 500 : Real) < values5 (2 : Fin 5) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_357 :
    values14 (357 : Fin 455) < values14 (358 : Fin 455) := by
  have hleft : values14 (357 : Fin 455) < (2661 / 1000 : Real) := by
    rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (10 : Fin 33) < (2661 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (10 : Fin 33) < (124651 / 100000 : Real) := by
      rw [show values9 (10 : Fin 33) = Real.sqrt (values8 (10 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (10 : Fin 20)) < (124651 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (124651 / 100000 : Real))]
      norm_num
      change values8 (10 : Fin 20) < (15537871801 / 10000000000 : Real)
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (10 : Fin 13)) < (15537871801 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15537871801 / 10000000000 : Real))]
      norm_num
      change values7 (10 : Fin 13) < (241425460104310983601 / 100000000000000000000 : Real)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (2 : Fin 5) < (241425460104310983601 / 100000000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (2 : Fin 5) < (70711 / 50000 : Real) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2661 / 1000 : Real) < values14 (358 : Fin 455) := by
    rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    change (2661 / 1000 : Real) < values5 (1 : Fin 5) + values8 (9 : Fin 20)
    have h5 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (1479 / 1000 : Real) < values8 (9 : Fin 20) := by
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change (1479 / 1000 : Real) < Real.sqrt (values7 (9 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2187441 / 1000000 : Real) < values7 (9 : Fin 13)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change (2187441 / 1000000 : Real) < 1 + values5 (1 : Fin 5)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_358 :
    values14 (358 : Fin 455) < values14 (359 : Fin 455) := by
  have hleft : values14 (358 : Fin 455) < (2669 / 1000 : Real) := by
    rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (9 : Fin 20) < (2669 / 1000 : Real)
    have h1 : values5 (1 : Fin 5) < (118921 / 100000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
      norm_num
      change Real.sqrt 2 < (14142204241 / 10000000000 : Real)
      change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
      norm_num
    have h2 : values8 (9 : Fin 20) < (3699 / 2500 : Real) := by
      rw [show values8 (9 : Fin 20) = Real.sqrt (values7 (9 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (9 : Fin 13)) < (3699 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3699 / 2500 : Real))]
      norm_num
      change values7 (9 : Fin 13) < (13682601 / 6250000 : Real)
      rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (1 : Fin 5) < (13682601 / 6250000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values5 (1 : Fin 5) < (118921 / 100000 : Real) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
        norm_num
        change Real.sqrt 2 < (14142204241 / 10000000000 : Real)
        change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2669 / 1000 : Real) < values14 (359 : Fin 455) := by
    rw [show values14 (359 : Fin 455) = 1 + values12 (74 : Fin 154) by rfl]
    change (2669 / 1000 : Real) < 1 + values12 (74 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1681 / 1000 : Real) < values12 (74 : Fin 154) := by
      rw [show values12 (74 : Fin 154) = Real.sqrt (values11 (74 : Fin 91)) by a158415_twelve_table]
      change (1681 / 1000 : Real) < Real.sqrt (values11 (74 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2825761 / 1000000 : Real) < values11 (74 : Fin 91)
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by a158415_twelve_table]
      change (2825761 / 1000000 : Real) < Real.sqrt 2 + values6 (3 : Fin 8)
      have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h8 : (707 / 500 : Real) < values6 (3 : Fin 8) := by
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (707 / 500 : Real) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (499849 / 250000 : Real) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (499849 / 250000 : Real) < 1 + 1
        have h9 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h10 : (9999 / 10000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_360 :
    values14 (360 : Fin 455) < values14 (361 : Fin 455) := by
  have hleft : values14 (360 : Fin 455) < (336 / 125 : Real) := by
    rw [show values14 (360 : Fin 455) = 1 + values12 (75 : Fin 154) by rfl]
    change 1 + values12 (75 : Fin 154) < (336 / 125 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (75 : Fin 154) < (4219 / 2500 : Real) := by
      rw [show values12 (75 : Fin 154) = Real.sqrt (values11 (75 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (75 : Fin 91)) < (4219 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (4219 / 2500 : Real))]
      norm_num
      change values11 (75 : Fin 91) < (17799961 / 6250000 : Real)
      rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (18 : Fin 33) < (17799961 / 6250000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (18 : Fin 33) < (9239 / 5000 : Real) := by
        rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (18 : Fin 20)) < (9239 / 5000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (9239 / 5000 : Real))]
        norm_num
        change values8 (18 : Fin 20) < (85359121 / 25000000 : Real)
        rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (6 : Fin 8) < (85359121 / 25000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (6 : Fin 8) < (120711 / 50000 : Real) := by
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change 1 + Real.sqrt 2 < (120711 / 50000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : Real.sqrt 2 < (707107 / 500000 : Real) := by
            change Real.sqrt (2) < (707107 / 500000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (336 / 125 : Real) < values14 (361 : Fin 455) := by
    rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    change (336 / 125 : Real) < Real.sqrt 2 + values9 (11 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (329 / 250 : Real) < values9 (11 : Fin 33) := by
      rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
      change (329 / 250 : Real) < Real.sqrt (values8 (11 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : Real) < values8 (11 : Fin 20)
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change (108241 / 62500 : Real) < Real.sqrt (values7 (11 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : Real) < values7 (11 : Fin 13)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change (11716114081 / 3906250000 : Real) < 1 + values5 (3 : Fin 5)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (19999 / 10000 : Real) < values5 (3 : Fin 5) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (19999 / 10000 : Real) < 1 + 1
        have h13 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h14 : (99999 / 100000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_361 :
    values14 (361 : Fin 455) < values14 (362 : Fin 455) := by
  have hleft : values14 (361 : Fin 455) < (2731 / 1000 : Real) := by
    rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (11 : Fin 33) < (2731 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (11 : Fin 33) < (13161 / 10000 : Real) := by
      rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (11 : Fin 20)) < (13161 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
      norm_num
      change values8 (11 : Fin 20) < (173211921 / 100000000 : Real)
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (11 : Fin 13)) < (173211921 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
      norm_num
      change values7 (11 : Fin 13) < (30002369576510241 / 10000000000000000 : Real)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (3 : Fin 5) < (30002369576510241 / 10000000000000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (3 : Fin 5) < (200001 / 100000 : Real) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (2731 / 1000 : Real) < values14 (362 : Fin 455) := by
    rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    change (2731 / 1000 : Real) < 1 + values12 (76 : Fin 154)
    have h7 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h8 : (433 / 250 : Real) < values12 (76 : Fin 154) := by
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values11 (76 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values11 (76 : Fin 91)
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + values9 (19 : Fin 33)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : Real) < values9 (19 : Fin 33) := by
        rw [show values9 (19 : Fin 33) = Real.sqrt (values8 (19 : Fin 20)) by a158415_twelve_table]
        change (199999 / 100000 : Real) < Real.sqrt (values8 (19 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (39999600001 / 10000000000 : Real) < values8 (19 : Fin 20)
        rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
        change (39999600001 / 10000000000 : Real) < 1 + values6 (7 : Fin 8)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (299999 / 100000 : Real) < values6 (7 : Fin 8) := by
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change (299999 / 100000 : Real) < 1 + 2
          have h13 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h14 : (1999999 / 1000000 : Real) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_362 :
    values14 (362 : Fin 455) < values14 (363 : Fin 455) := by
  have hleft : values14 (362 : Fin 455) < (2733 / 1000 : Real) := by
    rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    change 1 + values12 (76 : Fin 154) < (2733 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (76 : Fin 154) < (17321 / 10000 : Real) := by
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (76 : Fin 91)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values11 (76 : Fin 91) < (300017041 / 100000000 : Real)
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (19 : Fin 33) < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (19 : Fin 33) < (200001 / 100000 : Real) := by
        rw [show values9 (19 : Fin 33) = Real.sqrt (values8 (19 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (19 : Fin 20)) < (200001 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (200001 / 100000 : Real))]
        norm_num
        change values8 (19 : Fin 20) < (40000400001 / 10000000000 : Real)
        rw [show values8 (19 : Fin 20) = 1 + values6 (7 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (7 : Fin 8) < (40000400001 / 10000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (7 : Fin 8) < (300001 / 100000 : Real) := by
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (300001 / 100000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 2 < (2000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (2733 / 1000 : Real) < values14 (363 : Fin 455) := by
    rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    change (2733 / 1000 : Real) < values5 (1 : Fin 5) + values8 (10 : Fin 20)
    have h9 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1553 / 1000 : Real) < values8 (10 : Fin 20) := by
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change (1553 / 1000 : Real) < Real.sqrt (values7 (10 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : Real) < values7 (10 : Fin 13)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change (2411809 / 1000000 : Real) < 1 + values5 (2 : Fin 5)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (707 / 500 : Real) < values5 (2 : Fin 5) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (707 / 500 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_363 :
    values14 (363 : Fin 455) < values14 (364 : Fin 455) := by
  have hleft : values14 (363 : Fin 455) < (2743 / 1000 : Real) := by
    rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (10 : Fin 20) < (2743 / 1000 : Real)
    have h1 : values5 (1 : Fin 5) < (118921 / 100000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (118921 / 100000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
      norm_num
      change Real.sqrt 2 < (14142204241 / 10000000000 : Real)
      change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
      norm_num
    have h2 : values8 (10 : Fin 20) < (77689 / 50000 : Real) := by
      rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (10 : Fin 13)) < (77689 / 50000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (77689 / 50000 : Real))]
      norm_num
      change values7 (10 : Fin 13) < (6035580721 / 2500000000 : Real)
      rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (2 : Fin 5) < (6035580721 / 2500000000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values5 (2 : Fin 5) < (707107 / 500000 : Real) := by
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (707107 / 500000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2743 / 1000 : Real) < values14 (364 : Fin 455) := by
    rw [show values14 (364 : Fin 455) = 1 + values12 (77 : Fin 154) by rfl]
    change (2743 / 1000 : Real) < 1 + values12 (77 : Fin 154)
    have h5 : (9999 / 10000 : Real) < 1 := by
      norm_num
    have h6 : (17447 / 10000 : Real) < values12 (77 : Fin 154) := by
      rw [show values12 (77 : Fin 154) = Real.sqrt (values11 (77 : Fin 91)) by a158415_twelve_table]
      change (17447 / 10000 : Real) < Real.sqrt (values11 (77 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (304397809 / 100000000 : Real) < values11 (77 : Fin 91)
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by a158415_twelve_table]
      change (304397809 / 100000000 : Real) < 1 + values9 (20 : Fin 33)
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (10221 / 5000 : Real) < values9 (20 : Fin 33) := by
        rw [show values9 (20 : Fin 33) = 1 + values7 (1 : Fin 13) by a158415_twelve_table]
        change (10221 / 5000 : Real) < 1 + values7 (1 : Fin 13)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (104427 / 100000 : Real) < values7 (1 : Fin 13) := by
          rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
          change (104427 / 100000 : Real) < Real.sqrt (values6 (1 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (10904998329 / 10000000000 : Real) < values6 (1 : Fin 8)
          rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
          change (10904998329 / 10000000000 : Real) < Real.sqrt (values5 (1 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (118918988555492792241 / 100000000000000000000 : Real) < values5 (1 : Fin 5)
          rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
          change (118918988555492792241 / 100000000000000000000 : Real) < Real.sqrt (Real.sqrt 2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (14141725839061425697760186447702789802081 / 10000000000000000000000000000000000000000 : Real) < Real.sqrt 2
          change (14141725839061425697760186447702789802081 / 10000000000000000000000000000000000000000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_366 :
    values14 (366 : Fin 455) < values14 (367 : Fin 455) := by
  have hleft : values14 (366 : Fin 455) < (1387 / 500 : Real) := by
    rw [show values14 (366 : Fin 455) = 1 + values12 (79 : Fin 154) by rfl]
    change 1 + values12 (79 : Fin 154) < (1387 / 500 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (79 : Fin 154) < (8869 / 5000 : Real) := by
      rw [show values12 (79 : Fin 154) = Real.sqrt (values11 (79 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (79 : Fin 91)) < (8869 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (8869 / 5000 : Real))]
      norm_num
      change values11 (79 : Fin 91) < (78659161 / 25000000 : Real)
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by a158415_twelve_table]
      change Real.sqrt 2 + values6 (4 : Fin 8) < (78659161 / 25000000 : Real)
      have h3 : Real.sqrt 2 < (70711 / 50000 : Real) := by
        change Real.sqrt (2) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
      have h4 : values6 (4 : Fin 8) < (86603 / 50000 : Real) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (4 : Fin 5)) < (86603 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (86603 / 50000 : Real))]
        norm_num
        change values5 (4 : Fin 5) < (7500079609 / 2500000000 : Real)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (7500079609 / 2500000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (1387 / 500 : Real) < values14 (367 : Fin 455) := by
    rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    change (1387 / 500 : Real) < values6 (4 : Fin 8) + values7 (1 : Fin 13)
    have h7 : (433 / 250 : Real) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + 2
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    have h8 : (261 / 250 : Real) < values7 (1 : Fin 13) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change (261 / 250 : Real) < Real.sqrt (values6 (1 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (68121 / 62500 : Real) < values6 (1 : Fin 8)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (68121 / 62500 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4640470641 / 3906250000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (4640470641 / 3906250000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt 2
      change (21533967769982950881 / 15258789062500000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_367 :
    values14 (367 : Fin 455) < values14 (368 : Fin 455) := by
  have hleft : values14 (367 : Fin 455) < (2777 / 1000 : Real) := by
    rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    change values6 (4 : Fin 8) + values7 (1 : Fin 13) < (2777 / 1000 : Real)
    have h1 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    have h2 : values7 (1 : Fin 13) < (10443 / 10000 : Real) := by
      rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (1 : Fin 8)) < (10443 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10443 / 10000 : Real))]
      norm_num
      change values6 (1 : Fin 8) < (109056249 / 100000000 : Real)
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (109056249 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (109056249 / 100000000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (11893265445950001 / 10000000000000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893265445950001 / 10000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893265445950001 / 10000000000000000 : Real))]
      norm_num
      change Real.sqrt 2 < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      change Real.sqrt (2) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141449762967828276157933391900001 / 100000000000000000000000000000000 : Real))]
      norm_num
    linarith
  have hright : (2777 / 1000 : Real) < values14 (368 : Fin 455) := by
    rw [show values14 (368 : Fin 455) = 1 + values12 (80 : Fin 154) by rfl]
    change (2777 / 1000 : Real) < 1 + values12 (80 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (357 / 200 : Real) < values12 (80 : Fin 154) := by
      rw [show values12 (80 : Fin 154) = Real.sqrt (values11 (80 : Fin 91)) by a158415_twelve_table]
      change (357 / 200 : Real) < Real.sqrt (values11 (80 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (127449 / 40000 : Real) < values11 (80 : Fin 91)
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by a158415_twelve_table]
      change (127449 / 40000 : Real) < 1 + values9 (22 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (2189 / 1000 : Real) < values9 (22 : Fin 33) := by
        rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
        change (2189 / 1000 : Real) < 1 + values7 (3 : Fin 13)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (2973 / 2500 : Real) < values7 (3 : Fin 13) := by
          rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
          change (2973 / 2500 : Real) < Real.sqrt (values6 (3 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (8838729 / 6250000 : Real) < values6 (3 : Fin 8)
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (8838729 / 6250000 : Real) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (78123130335441 / 39062500000000 : Real) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (78123130335441 / 39062500000000 : Real) < 1 + 1
          have h11 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h12 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_369 :
    values14 (369 : Fin 455) < values14 (370 : Fin 455) := by
  have hleft : values14 (369 : Fin 455) < (1411 / 500 : Real) := by
    rw [show values14 (369 : Fin 455) = 1 + values12 (81 : Fin 154) by rfl]
    change 1 + values12 (81 : Fin 154) < (1411 / 500 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (81 : Fin 154) < (18211 / 10000 : Real) := by
      rw [show values12 (81 : Fin 154) = Real.sqrt (values11 (81 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (81 : Fin 91)) < (18211 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (18211 / 10000 : Real))]
      norm_num
      change values11 (81 : Fin 91) < (331640521 / 100000000 : Real)
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (23 : Fin 33) < (331640521 / 100000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values9 (23 : Fin 33) < (23161 / 10000 : Real) := by
        rw [show values9 (23 : Fin 33) = 1 + values7 (4 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (4 : Fin 13) < (23161 / 10000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (4 : Fin 13) < (16451 / 12500 : Real) := by
          rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (4 : Fin 8)) < (16451 / 12500 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (16451 / 12500 : Real))]
          norm_num
          change values6 (4 : Fin 8) < (270635401 / 156250000 : Real)
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (270635401 / 156250000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (270635401 / 156250000 : Real))]
          norm_num
          change values5 (4 : Fin 5) < (73243520274430801 / 24414062500000000 : Real)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (73243520274430801 / 24414062500000000 : Real)
          have h7 : 1 < (100001 / 100000 : Real) := by
            norm_num
          have h8 : 2 < (200001 / 100000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1411 / 500 : Real) < values14 (370 : Fin 455) := by
    rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    change (1411 / 500 : Real) < values6 (1 : Fin 8) + values7 (7 : Fin 13)
    have h9 : (2181 / 2000 : Real) < values6 (1 : Fin 8) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change (2181 / 2000 : Real) < Real.sqrt (values5 (1 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (4756761 / 4000000 : Real) < values5 (1 : Fin 5)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (4756761 / 4000000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (22626775211121 / 16000000000000 : Real) < Real.sqrt 2
      change (22626775211121 / 16000000000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (433 / 250 : Real) < values7 (7 : Fin 13) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + 2
      have h11 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h12 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_370 :
    values14 (370 : Fin 455) < values14 (371 : Fin 455) := by
  have hleft : values14 (370 : Fin 455) < (2823 / 1000 : Real) := by
    rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    change values6 (1 : Fin 8) + values7 (7 : Fin 13) < (2823 / 1000 : Real)
    have h1 : values6 (1 : Fin 8) < (5453 / 5000 : Real) := by
      rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
      norm_num
      change values5 (1 : Fin 5) < (29735209 / 25000000 : Real)
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
      norm_num
      change Real.sqrt 2 < (884182654273681 / 625000000000000 : Real)
      change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
      norm_num
    have h2 : values7 (7 : Fin 13) < (17321 / 10000 : Real) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values6 (7 : Fin 8) < (300017041 / 100000000 : Real)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (2823 / 1000 : Real) < values14 (371 : Fin 455) := by
    rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    change (2823 / 1000 : Real) < Real.sqrt 2 + values9 (12 : Fin 33)
    have h5 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (707 / 500 : Real) < values9 (12 : Fin 33) := by
      rw [show values9 (12 : Fin 33) = Real.sqrt (values8 (12 : Fin 20)) by a158415_twelve_table]
      change (707 / 500 : Real) < Real.sqrt (values8 (12 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (499849 / 250000 : Real) < values8 (12 : Fin 20)
      rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
      change (499849 / 250000 : Real) < Real.sqrt (values7 (12 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (249849022801 / 62500000000 : Real) < values7 (12 : Fin 13)
      rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
      change (249849022801 / 62500000000 : Real) < 1 + values5 (4 : Fin 5)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (29999 / 10000 : Real) < values5 (4 : Fin 5) := by
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (29999 / 10000 : Real) < 1 + 2
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (199999 / 100000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_371 :
    values14 (371 : Fin 455) < values14 (372 : Fin 455) := by
  have hleft : values14 (371 : Fin 455) < (2829 / 1000 : Real) := by
    rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (12 : Fin 33) < (2829 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (12 : Fin 33) < (14143 / 10000 : Real) := by
      rw [show values9 (12 : Fin 33) = Real.sqrt (values8 (12 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (12 : Fin 20)) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
      change values8 (12 : Fin 20) < (200024449 / 100000000 : Real)
      rw [show values8 (12 : Fin 20) = Real.sqrt (values7 (12 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (12 : Fin 13)) < (200024449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (200024449 / 100000000 : Real))]
      norm_num
      change values7 (12 : Fin 13) < (40009780197753601 / 10000000000000000 : Real)
      rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (4 : Fin 5) < (40009780197753601 / 10000000000000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values5 (4 : Fin 5) < (30001 / 10000 : Real) := by
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (30001 / 10000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (2829 / 1000 : Real) < values14 (372 : Fin 455) := by
    rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    change (2829 / 1000 : Real) < 1 + values12 (82 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (1847 / 1000 : Real) < values12 (82 : Fin 154) := by
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by a158415_twelve_table]
      change (1847 / 1000 : Real) < Real.sqrt (values11 (82 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3411409 / 1000000 : Real) < values11 (82 : Fin 91)
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by a158415_twelve_table]
      change (3411409 / 1000000 : Real) < 1 + values9 (24 : Fin 33)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (1207 / 500 : Real) < values9 (24 : Fin 33) := by
        rw [show values9 (24 : Fin 33) = 1 + values7 (5 : Fin 13) by a158415_twelve_table]
        change (1207 / 500 : Real) < 1 + values7 (5 : Fin 13)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (7071 / 5000 : Real) < values7 (5 : Fin 13) := by
          rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
          change (7071 / 5000 : Real) < Real.sqrt (values6 (5 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (49999041 / 25000000 : Real) < values6 (5 : Fin 8)
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (49999041 / 25000000 : Real) < 1 + 1
          have h13 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h14 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_372 :
    values14 (372 : Fin 455) < values14 (373 : Fin 455) := by
  have hleft : values14 (372 : Fin 455) < (356 / 125 : Real) := by
    rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    change 1 + values12 (82 : Fin 154) < (356 / 125 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (82 : Fin 154) < (9239 / 5000 : Real) := by
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (82 : Fin 91)) < (9239 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (9239 / 5000 : Real))]
      norm_num
      change values11 (82 : Fin 91) < (85359121 / 25000000 : Real)
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (24 : Fin 33) < (85359121 / 25000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (24 : Fin 33) < (120711 / 50000 : Real) := by
        rw [show values9 (24 : Fin 33) = 1 + values7 (5 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (5 : Fin 13) < (120711 / 50000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (5 : Fin 13) < (707107 / 500000 : Real) := by
          rw [show values7 (5 : Fin 13) = Real.sqrt (values6 (5 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (5 : Fin 8)) < (707107 / 500000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
          norm_num
          change values6 (5 : Fin 8) < (500000309449 / 250000000000 : Real)
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (500000309449 / 250000000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (356 / 125 : Real) < values14 (373 : Fin 455) := by
    rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    change (356 / 125 : Real) < Real.sqrt 2 + values9 (13 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (289 / 200 : Real) < values9 (13 : Fin 33) := by
      rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
      change (289 / 200 : Real) < Real.sqrt (values8 (13 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (83521 / 40000 : Real) < values8 (13 : Fin 20)
      rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
      change (83521 / 40000 : Real) < 1 + values6 (1 : Fin 8)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (109 / 100 : Real) < values6 (1 : Fin 8) := by
        rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
        change (109 / 100 : Real) < Real.sqrt (values5 (1 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11881 / 10000 : Real) < values5 (1 : Fin 5)
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (11881 / 10000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (141158161 / 100000000 : Real) < Real.sqrt 2
        change (141158161 / 100000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_373 :
    values14 (373 : Fin 455) < values14 (374 : Fin 455) := by
  have hleft : values14 (373 : Fin 455) < (2861 / 1000 : Real) := by
    rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (13 : Fin 33) < (2861 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (13 : Fin 33) < (723 / 500 : Real) := by
      rw [show values9 (13 : Fin 33) = Real.sqrt (values8 (13 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (13 : Fin 20)) < (723 / 500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (723 / 500 : Real))]
      norm_num
      change values8 (13 : Fin 20) < (522729 / 250000 : Real)
      rw [show values8 (13 : Fin 20) = 1 + values6 (1 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (1 : Fin 8) < (522729 / 250000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values6 (1 : Fin 8) < (5453 / 5000 : Real) := by
        rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (1 : Fin 5)) < (5453 / 5000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5453 / 5000 : Real))]
        norm_num
        change values5 (1 : Fin 5) < (29735209 / 25000000 : Real)
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (29735209 / 25000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (29735209 / 25000000 : Real))]
        norm_num
        change Real.sqrt 2 < (884182654273681 / 625000000000000 : Real)
        change Real.sqrt (2) < (884182654273681 / 625000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (884182654273681 / 625000000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (2861 / 1000 : Real) < values14 (374 : Fin 455) := by
    rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    change (2861 / 1000 : Real) < 1 + values12 (83 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (377 / 200 : Real) < values12 (83 : Fin 154) := by
      rw [show values12 (83 : Fin 154) = Real.sqrt (values11 (83 : Fin 91)) by a158415_twelve_table]
      change (377 / 200 : Real) < Real.sqrt (values11 (83 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (142129 / 40000 : Real) < values11 (83 : Fin 91)
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by a158415_twelve_table]
      change (142129 / 40000 : Real) < 1 + values9 (25 : Fin 33)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (25537 / 10000 : Real) < values9 (25 : Fin 33) := by
        rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
        change (25537 / 10000 : Real) < 1 + values7 (6 : Fin 13)
        have h9 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h10 : (155377 / 100000 : Real) < values7 (6 : Fin 13) := by
          rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
          change (155377 / 100000 : Real) < Real.sqrt (values6 (6 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (24142012129 / 10000000000 : Real) < values6 (6 : Fin 8)
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change (24142012129 / 10000000000 : Real) < 1 + Real.sqrt 2
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (141421 / 100000 : Real) < Real.sqrt 2 := by
            change (141421 / 100000 : Real) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_374 :
    values14 (374 : Fin 455) < values14 (375 : Fin 455) := by
  have hleft : values14 (374 : Fin 455) < (1443 / 500 : Real) := by
    rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    change 1 + values12 (83 : Fin 154) < (1443 / 500 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (83 : Fin 154) < (4713 / 2500 : Real) := by
      rw [show values12 (83 : Fin 154) = Real.sqrt (values11 (83 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (83 : Fin 91)) < (4713 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (4713 / 2500 : Real))]
      norm_num
      change values11 (83 : Fin 91) < (22212369 / 6250000 : Real)
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (25 : Fin 33) < (22212369 / 6250000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (25 : Fin 33) < (12769 / 5000 : Real) := by
        rw [show values9 (25 : Fin 33) = 1 + values7 (6 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (6 : Fin 13) < (12769 / 5000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (6 : Fin 13) < (77689 / 50000 : Real) := by
          rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
          change Real.sqrt (values6 (6 : Fin 8)) < (77689 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (77689 / 50000 : Real))]
          norm_num
          change values6 (6 : Fin 8) < (6035580721 / 2500000000 : Real)
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change 1 + Real.sqrt 2 < (6035580721 / 2500000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : Real.sqrt 2 < (707107 / 500000 : Real) := by
            change Real.sqrt (2) < (707107 / 500000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (1443 / 500 : Real) < values14 (375 : Fin 455) := by
    rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    change (1443 / 500 : Real) < Real.sqrt 2 + values9 (14 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1479 / 1000 : Real) < values9 (14 : Fin 33) := by
      rw [show values9 (14 : Fin 33) = Real.sqrt (values8 (14 : Fin 20)) by a158415_twelve_table]
      change (1479 / 1000 : Real) < Real.sqrt (values8 (14 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2187441 / 1000000 : Real) < values8 (14 : Fin 20)
      rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
      change (2187441 / 1000000 : Real) < 1 + values6 (2 : Fin 8)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (1189 / 1000 : Real) < values6 (2 : Fin 8) := by
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (values5 (2 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < values5 (2 : Fin 5)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_375 :
    values14 (375 : Fin 455) < values14 (376 : Fin 455) := by
  have hleft : values14 (375 : Fin 455) < (1447 / 500 : Real) := by
    rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (14 : Fin 33) < (1447 / 500 : Real)
    have h1 : Real.sqrt 2 < (70711 / 50000 : Real) := by
      change Real.sqrt (2) < (70711 / 50000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
      norm_num
    have h2 : values9 (14 : Fin 33) < (3699 / 2500 : Real) := by
      rw [show values9 (14 : Fin 33) = Real.sqrt (values8 (14 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (14 : Fin 20)) < (3699 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3699 / 2500 : Real))]
      norm_num
      change values8 (14 : Fin 20) < (13682601 / 6250000 : Real)
      rw [show values8 (14 : Fin 20) = 1 + values6 (2 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (2 : Fin 8) < (13682601 / 6250000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values6 (2 : Fin 8) < (118921 / 100000 : Real) := by
        rw [show values6 (2 : Fin 8) = Real.sqrt (values5 (2 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (2 : Fin 5)) < (118921 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118921 / 100000 : Real))]
        norm_num
        change values5 (2 : Fin 5) < (14142204241 / 10000000000 : Real)
        rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
        change Real.sqrt (2) < (14142204241 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14142204241 / 10000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (1447 / 500 : Real) < values14 (376 : Fin 455) := by
    rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    change (1447 / 500 : Real) < values5 (1 : Fin 5) + values8 (11 : Fin 20)
    have h5 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1413721 / 1000000 : Real) < Real.sqrt 2
      change (1413721 / 1000000 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h6 : (433 / 250 : Real) < values8 (11 : Fin 20) := by
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values7 (11 : Fin 13))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values7 (11 : Fin 13)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + values5 (3 : Fin 5)
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (199999 / 100000 : Real) < values5 (3 : Fin 5) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (199999 / 100000 : Real) < 1 + 1
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_376 :
    values14 (376 : Fin 455) < values14 (377 : Fin 455) := by
  have hleft : values14 (376 : Fin 455) < (1461 / 500 : Real) := by
    rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    change values5 (1 : Fin 5) + values8 (11 : Fin 20) < (1461 / 500 : Real)
    have h1 : values5 (1 : Fin 5) < (11893 / 10000 : Real) := by
      rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
      change Real.sqrt (Real.sqrt 2) < (11893 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (11893 / 10000 : Real))]
      norm_num
      change Real.sqrt 2 < (141443449 / 100000000 : Real)
      change Real.sqrt (2) < (141443449 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141443449 / 100000000 : Real))]
      norm_num
    have h2 : values8 (11 : Fin 20) < (17321 / 10000 : Real) := by
      rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
      change Real.sqrt (values7 (11 : Fin 13)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values7 (11 : Fin 13) < (300017041 / 100000000 : Real)
      rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
      change 1 + values5 (3 : Fin 5) < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values5 (3 : Fin 5) < (200001 / 100000 : Real) := by
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (1461 / 500 : Real) < values14 (377 : Fin 455) := by
    rw [show values14 (377 : Fin 455) = 1 + values12 (84 : Fin 154) by rfl]
    change (1461 / 500 : Real) < 1 + values12 (84 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (1931 / 1000 : Real) < values12 (84 : Fin 154) := by
      rw [show values12 (84 : Fin 154) = Real.sqrt (values11 (84 : Fin 91)) by a158415_twelve_table]
      change (1931 / 1000 : Real) < Real.sqrt (values11 (84 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3728761 / 1000000 : Real) < values11 (84 : Fin 91)
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by a158415_twelve_table]
      change (3728761 / 1000000 : Real) < 1 + values9 (26 : Fin 33)
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (683 / 250 : Real) < values9 (26 : Fin 33) := by
        rw [show values9 (26 : Fin 33) = 1 + values7 (7 : Fin 13) by a158415_twelve_table]
        change (683 / 250 : Real) < 1 + values7 (7 : Fin 13)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (34641 / 20000 : Real) < values7 (7 : Fin 13) := by
          rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
          change (34641 / 20000 : Real) < Real.sqrt (values6 (7 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (1199998881 / 400000000 : Real) < values6 (7 : Fin 8)
          rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
          change (1199998881 / 400000000 : Real) < 1 + 2
          have h13 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          have h14 : (19999999 / 10000000 : Real) < 2 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_378 :
    values14 (378 : Fin 455) < values14 (379 : Fin 455) := by
  have hleft : values14 (378 : Fin 455) < (2957 / 1000 : Real) := by
    rw [show values14 (378 : Fin 455) = 1 + values12 (85 : Fin 154) by rfl]
    change 1 + values12 (85 : Fin 154) < (2957 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (85 : Fin 154) < (19567 / 10000 : Real) := by
      rw [show values12 (85 : Fin 154) = Real.sqrt (values11 (85 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (85 : Fin 91)) < (19567 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (19567 / 10000 : Real))]
      norm_num
      change values11 (85 : Fin 91) < (382867489 / 100000000 : Real)
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (27 : Fin 33) < (382867489 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (27 : Fin 33) < (5657 / 2000 : Real) := by
        rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
        change Real.sqrt 2 + Real.sqrt 2 < (5657 / 2000 : Real)
        have h5 : Real.sqrt 2 < (70711 / 50000 : Real) := by
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        have h6 : Real.sqrt 2 < (70711 / 50000 : Real) := by
          change Real.sqrt (2) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (2957 / 1000 : Real) < values14 (379 : Fin 455) := by
    rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    change (2957 / 1000 : Real) < Real.sqrt 2 + values9 (15 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (1553 / 1000 : Real) < values9 (15 : Fin 33) := by
      rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
      change (1553 / 1000 : Real) < Real.sqrt (values8 (15 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (2411809 / 1000000 : Real) < values8 (15 : Fin 20)
      rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
      change (2411809 / 1000000 : Real) < 1 + values6 (3 : Fin 8)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (707 / 500 : Real) < values6 (3 : Fin 8) := by
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change (707 / 500 : Real) < Real.sqrt (values5 (3 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (499849 / 250000 : Real) < values5 (3 : Fin 5)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change (499849 / 250000 : Real) < 1 + 1
        have h11 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h12 : (9999 / 10000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_379 :
    values14 (379 : Fin 455) < values14 (380 : Fin 455) := by
  have hleft : values14 (379 : Fin 455) < (371 / 125 : Real) := by
    rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (15 : Fin 33) < (371 / 125 : Real)
    have h1 : Real.sqrt 2 < (707107 / 500000 : Real) := by
      change Real.sqrt (2) < (707107 / 500000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
      norm_num
    have h2 : values9 (15 : Fin 33) < (776887 / 500000 : Real) := by
      rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (15 : Fin 20)) < (776887 / 500000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (776887 / 500000 : Real))]
      norm_num
      change values8 (15 : Fin 20) < (603553410769 / 250000000000 : Real)
      rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (3 : Fin 8) < (603553410769 / 250000000000 : Real)
      have h3 : 1 < (100000001 / 100000000 : Real) := by
        norm_num
      have h4 : values6 (3 : Fin 8) < (141421357 / 100000000 : Real) := by
        rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (3 : Fin 5)) < (141421357 / 100000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (141421357 / 100000000 : Real))]
        norm_num
        change values5 (3 : Fin 5) < (20000000215721449 / 10000000000000000 : Real)
        rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (20000000215721449 / 10000000000000000 : Real)
        have h5 : 1 < (1000000001 / 1000000000 : Real) := by
          norm_num
        have h6 : 1 < (1000000001 / 1000000000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (371 / 125 : Real) < values14 (380 : Fin 455) := by
    rw [show values14 (380 : Fin 455) = 1 + values12 (86 : Fin 154) by rfl]
    change (371 / 125 : Real) < 1 + values12 (86 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (1999 / 1000 : Real) < values12 (86 : Fin 154) := by
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by a158415_twelve_table]
      change (1999 / 1000 : Real) < Real.sqrt (values11 (86 : Fin 91))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3996001 / 1000000 : Real) < values11 (86 : Fin 91)
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by a158415_twelve_table]
      change (3996001 / 1000000 : Real) < 1 + values9 (28 : Fin 33)
      have h9 : (999 / 1000 : Real) < 1 := by
        norm_num
      have h10 : (2999 / 1000 : Real) < values9 (28 : Fin 33) := by
        rw [show values9 (28 : Fin 33) = 1 + values7 (8 : Fin 13) by a158415_twelve_table]
        change (2999 / 1000 : Real) < 1 + values7 (8 : Fin 13)
        have h11 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h12 : (19999 / 10000 : Real) < values7 (8 : Fin 13) := by
          rw [show values7 (8 : Fin 13) = 1 + values5 (0 : Fin 5) by a158415_twelve_table]
          change (19999 / 10000 : Real) < 1 + values5 (0 : Fin 5)
          have h13 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h14 : (99999 / 100000 : Real) < values5 (0 : Fin 5) := by
            rw [show values5 (0 : Fin 5) = Real.sqrt (1) by a158415_twelve_table]
            change (99999 / 100000 : Real) < Real.sqrt (1)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_386 :
    values14 (386 : Fin 455) < values14 (387 : Fin 455) := by
  have hleft : values14 (386 : Fin 455) < (3047 / 1000 : Real) := by
    rw [show values14 (386 : Fin 455) = 1 + values12 (92 : Fin 154) by rfl]
    change 1 + values12 (92 : Fin 154) < (3047 / 1000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (92 : Fin 154) < (5117 / 2500 : Real) := by
      rw [show values12 (92 : Fin 154) = Real.sqrt (values11 (87 : Fin 91)) by a158415_twelve_table]
      change Real.sqrt (values11 (87 : Fin 91)) < (5117 / 2500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5117 / 2500 : Real))]
      norm_num
      change values11 (87 : Fin 91) < (26183689 / 6250000 : Real)
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by a158415_twelve_table]
      change 1 + values9 (29 : Fin 33) < (26183689 / 6250000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values9 (29 : Fin 33) < (318921 / 100000 : Real) := by
        rw [show values9 (29 : Fin 33) = 1 + values7 (9 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (9 : Fin 13) < (318921 / 100000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values7 (9 : Fin 13) < (273651 / 125000 : Real) := by
          rw [show values7 (9 : Fin 13) = 1 + values5 (1 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (1 : Fin 5) < (273651 / 125000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : values5 (1 : Fin 5) < (1486509 / 1250000 : Real) := by
            rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
            change Real.sqrt (Real.sqrt 2) < (1486509 / 1250000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1486509 / 1250000 : Real))]
            norm_num
            change Real.sqrt 2 < (2209709007081 / 1562500000000 : Real)
            change Real.sqrt (2) < (2209709007081 / 1562500000000 : Real)
            rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (2209709007081 / 1562500000000 : Real))]
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (3047 / 1000 : Real) < values14 (387 : Fin 455) := by
    rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    change (3047 / 1000 : Real) < values6 (4 : Fin 8) + values7 (4 : Fin 13)
    have h9 : (433 / 250 : Real) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + 2
      have h11 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h12 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    have h10 : (329 / 250 : Real) < values7 (4 : Fin 13) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change (329 / 250 : Real) < Real.sqrt (values6 (4 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (108241 / 62500 : Real) < values6 (4 : Fin 8)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (108241 / 62500 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (11716114081 / 3906250000 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (11716114081 / 3906250000 : Real) < 1 + 2
      have h13 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h14 : (19999 / 10000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_387 :
    values14 (387 : Fin 455) < values14 (388 : Fin 455) := by
  have hleft : values14 (387 : Fin 455) < (3049 / 1000 : Real) := by
    rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    change values6 (4 : Fin 8) + values7 (4 : Fin 13) < (3049 / 1000 : Real)
    have h1 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    have h2 : values7 (4 : Fin 13) < (13161 / 10000 : Real) := by
      rw [show values7 (4 : Fin 13) = Real.sqrt (values6 (4 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (4 : Fin 8)) < (13161 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (13161 / 10000 : Real))]
      norm_num
      change values6 (4 : Fin 8) < (173211921 / 100000000 : Real)
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (173211921 / 100000000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (173211921 / 100000000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (30002369576510241 / 10000000000000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (30002369576510241 / 10000000000000000 : Real)
      have h5 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h6 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (3049 / 1000 : Real) < values14 (388 : Fin 455) := by
    rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    change (3049 / 1000 : Real) < 1 + values12 (93 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (257 / 125 : Real) < values12 (93 : Fin 154) := by
      rw [show values12 (93 : Fin 154) = 1 + values10 (6 : Fin 54) by a158415_twelve_table]
      change (257 / 125 : Real) < 1 + values10 (6 : Fin 54)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (5283 / 5000 : Real) < values10 (6 : Fin 54) := by
        rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by a158415_twelve_table]
        change (5283 / 5000 : Real) < Real.sqrt (values9 (6 : Fin 33))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (27910089 / 25000000 : Real) < values9 (6 : Fin 33)
        rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
        change (27910089 / 25000000 : Real) < Real.sqrt (values8 (6 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (778973067987921 / 625000000000000 : Real) < values8 (6 : Fin 20)
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change (778973067987921 / 625000000000000 : Real) < Real.sqrt (values7 (6 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (606799040650514192623401902241 / 390625000000000000000000000000 : Real) < values7 (6 : Fin 13)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change (606799040650514192623401902241 / 390625000000000000000000000000 : Real) < Real.sqrt (values6 (6 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (368205075734384375603679426432501731123764140261697320822081 / 152587890625000000000000000000000000000000000000000000000000 : Real) < values6 (6 : Fin 8)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change (368205075734384375603679426432501731123764140261697320822081 / 152587890625000000000000000000000000000000000000000000000000 : Real) < 1 + Real.sqrt 2
        have h11 : (9999 / 10000 : Real) < 1 := by
          norm_num
        have h12 : (707 / 500 : Real) < Real.sqrt 2 := by
          change (707 / 500 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_388 :
    values14 (388 : Fin 455) < values14 (389 : Fin 455) := by
  have hleft : values14 (388 : Fin 455) < (3057 / 1000 : Real) := by
    rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    change 1 + values12 (93 : Fin 154) < (3057 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (93 : Fin 154) < (20567 / 10000 : Real) := by
      rw [show values12 (93 : Fin 154) = 1 + values10 (6 : Fin 54) by a158415_twelve_table]
      change 1 + values10 (6 : Fin 54) < (20567 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values10 (6 : Fin 54) < (3302 / 3125 : Real) := by
        rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by a158415_twelve_table]
        change Real.sqrt (values9 (6 : Fin 33)) < (3302 / 3125 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3302 / 3125 : Real))]
        norm_num
        change values9 (6 : Fin 33) < (10903204 / 9765625 : Real)
        rw [show values9 (6 : Fin 33) = Real.sqrt (values8 (6 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (6 : Fin 20)) < (10903204 / 9765625 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10903204 / 9765625 : Real))]
        norm_num
        change values8 (6 : Fin 20) < (118879857465616 / 95367431640625 : Real)
        rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (6 : Fin 13)) < (118879857465616 / 95367431640625 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (118879857465616 / 95367431640625 : Real))]
        norm_num
        change values7 (6 : Fin 13) < (14132420511045176210622259456 / 9094947017729282379150390625 : Real)
        rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (6 : Fin 8)) < (14132420511045176210622259456 / 9094947017729282379150390625 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14132420511045176210622259456 / 9094947017729282379150390625 : Real))]
        norm_num
        change values6 (6 : Fin 8) < (199725309501010399532216592108282390780104690350581415936 / 82718061255302767487140869206996285356581211090087890625 : Real)
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (199725309501010399532216592108282390780104690350581415936 / 82718061255302767487140869206996285356581211090087890625 : Real)
        have h5 : 1 < (10001 / 10000 : Real) := by
          norm_num
        have h6 : Real.sqrt 2 < (14143 / 10000 : Real) := by
          change Real.sqrt (2) < (14143 / 10000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (3057 / 1000 : Real) < values14 (389 : Fin 455) := by
    rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    change (3057 / 1000 : Real) < Real.sqrt 2 + values9 (16 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (413 / 250 : Real) < values9 (16 : Fin 33) := by
      rw [show values9 (16 : Fin 33) = Real.sqrt (values8 (16 : Fin 20)) by a158415_twelve_table]
      change (413 / 250 : Real) < Real.sqrt (values8 (16 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (170569 / 62500 : Real) < values8 (16 : Fin 20)
      rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
      change (170569 / 62500 : Real) < 1 + values6 (4 : Fin 8)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (433 / 250 : Real) < values6 (4 : Fin 8) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change (433 / 250 : Real) < Real.sqrt (values5 (4 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (187489 / 62500 : Real) < values5 (4 : Fin 5)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change (187489 / 62500 : Real) < 1 + 2
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_389 :
    values14 (389 : Fin 455) < values14 (390 : Fin 455) := by
  have hleft : values14 (389 : Fin 455) < (767 / 250 : Real) := by
    rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (16 : Fin 33) < (767 / 250 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (16 : Fin 33) < (1653 / 1000 : Real) := by
      rw [show values9 (16 : Fin 33) = Real.sqrt (values8 (16 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (16 : Fin 20)) < (1653 / 1000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1653 / 1000 : Real))]
      norm_num
      change values8 (16 : Fin 20) < (2732409 / 1000000 : Real)
      rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (4 : Fin 8) < (2732409 / 1000000 : Real)
      have h3 : 1 < (10001 / 10000 : Real) := by
        norm_num
      have h4 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
        rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
        norm_num
        change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
        rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
        change 1 + 2 < (300017041 / 100000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : 2 < (200001 / 100000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (767 / 250 : Real) < values14 (390 : Fin 455) := by
    rw [show values14 (390 : Fin 455) = 1 + values12 (94 : Fin 154) by rfl]
    change (767 / 250 : Real) < 1 + values12 (94 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (2071 / 1000 : Real) < values12 (94 : Fin 154) := by
      rw [show values12 (94 : Fin 154) = 1 + values10 (7 : Fin 54) by a158415_twelve_table]
      change (2071 / 1000 : Real) < 1 + values10 (7 : Fin 54)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (107107 / 100000 : Real) < values10 (7 : Fin 54) := by
        rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by a158415_twelve_table]
        change (107107 / 100000 : Real) < Real.sqrt (values9 (7 : Fin 33))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11471909449 / 10000000000 : Real) < values9 (7 : Fin 33)
        rw [show values9 (7 : Fin 33) = Real.sqrt (values8 (7 : Fin 20)) by a158415_twelve_table]
        change (11471909449 / 10000000000 : Real) < Real.sqrt (values8 (7 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (131604706406055483601 / 100000000000000000000 : Real) < values8 (7 : Fin 20)
        rw [show values8 (7 : Fin 20) = Real.sqrt (values7 (7 : Fin 13)) by a158415_twelve_table]
        change (131604706406055483601 / 100000000000000000000 : Real) < Real.sqrt (values7 (7 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (17319798748224061242875908374441979927201 / 10000000000000000000000000000000000000000 : Real) < values7 (7 : Fin 13)
        rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
        change (17319798748224061242875908374441979927201 / 10000000000000000000000000000000000000000 : Real) < Real.sqrt (values6 (7 : Fin 8))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (299975428678983758771725167006604935084832579527969043002229878818396601259694401 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < values6 (7 : Fin 8)
        rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
        change (299975428678983758771725167006604935084832579527969043002229878818396601259694401 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 : Real) < 1 + 2
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : Real) < 2 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_394 :
    values14 (394 : Fin 455) < values14 (395 : Fin 455) := by
  have hleft : values14 (394 : Fin 455) < (3117 / 1000 : Real) := by
    rw [show values14 (394 : Fin 455) = 1 + values12 (98 : Fin 154) by rfl]
    change 1 + values12 (98 : Fin 154) < (3117 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (98 : Fin 154) < (4233 / 2000 : Real) := by
      rw [show values12 (98 : Fin 154) = 1 + values10 (10 : Fin 54) by a158415_twelve_table]
      change 1 + values10 (10 : Fin 54) < (4233 / 2000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values10 (10 : Fin 54) < (111647 / 100000 : Real) := by
        rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by a158415_twelve_table]
        change Real.sqrt (values9 (10 : Fin 33)) < (111647 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (111647 / 100000 : Real))]
        norm_num
        change values9 (10 : Fin 33) < (12465052609 / 10000000000 : Real)
        rw [show values9 (10 : Fin 33) = Real.sqrt (values8 (10 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (10 : Fin 20)) < (12465052609 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (12465052609 / 10000000000 : Real))]
        norm_num
        change values8 (10 : Fin 20) < (155377536545137706881 / 100000000000000000000 : Real)
        rw [show values8 (10 : Fin 20) = Real.sqrt (values7 (10 : Fin 13)) by a158415_twelve_table]
        change Real.sqrt (values7 (10 : Fin 13)) < (155377536545137706881 / 100000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (155377536545137706881 / 100000000000000000000 : Real))]
        norm_num
        change values7 (10 : Fin 13) < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : Real)
        rw [show values7 (10 : Fin 13) = 1 + values5 (2 : Fin 5) by a158415_twelve_table]
        change 1 + values5 (2 : Fin 5) < (24142178862835603648895169895475074748161 / 10000000000000000000000000000000000000000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values5 (2 : Fin 5) < (707107 / 500000 : Real) := by
          rw [show values5 (2 : Fin 5) = Real.sqrt (2) by a158415_twelve_table]
          change Real.sqrt (2) < (707107 / 500000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (3117 / 1000 : Real) < values14 (395 : Fin 455) := by
    rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    change (3117 / 1000 : Real) < Real.sqrt 2 + values9 (17 : Fin 33)
    have h7 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h8 : (433 / 250 : Real) < values9 (17 : Fin 33) := by
      rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values8 (17 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values8 (17 : Fin 20)
      rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + values6 (5 : Fin 8)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : Real) < values6 (5 : Fin 8) := by
        rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
        change (199999 / 100000 : Real) < 1 + 1
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_395 :
    values14 (395 : Fin 455) < values14 (396 : Fin 455) := by
  have hleft : values14 (395 : Fin 455) < (3147 / 1000 : Real) := by
    rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (17 : Fin 33) < (3147 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (17 : Fin 33) < (17321 / 10000 : Real) := by
      rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (17 : Fin 20)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values8 (17 : Fin 20) < (300017041 / 100000000 : Real)
      rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (5 : Fin 8) < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values6 (5 : Fin 8) < (200001 / 100000 : Real) := by
        rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
        change 1 + 1 < (200001 / 100000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        linarith
      linarith
    linarith
  have hright : (3147 / 1000 : Real) < values14 (396 : Fin 455) := by
    rw [show values14 (396 : Fin 455) = 1 + values12 (99 : Fin 154) by rfl]
    change (3147 / 1000 : Real) < 1 + values12 (99 : Fin 154)
    have h7 : (99999 / 100000 : Real) < 1 := by
      norm_num
    have h8 : (1342 / 625 : Real) < values12 (99 : Fin 154) := by
      rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by a158415_twelve_table]
      change (1342 / 625 : Real) < 1 + values10 (11 : Fin 54)
      have h9 : (9999999 / 10000000 : Real) < 1 := by
        norm_num
      have h10 : (573601 / 500000 : Real) < values10 (11 : Fin 54) := by
        rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by a158415_twelve_table]
        change (573601 / 500000 : Real) < Real.sqrt (values9 (11 : Fin 33))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (329018107201 / 250000000000 : Real) < values9 (11 : Fin 33)
        rw [show values9 (11 : Fin 33) = Real.sqrt (values8 (11 : Fin 20)) by a158415_twelve_table]
        change (329018107201 / 250000000000 : Real) < Real.sqrt (values8 (11 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (108252914866128728054401 / 62500000000000000000000 : Real) < values8 (11 : Fin 20)
        rw [show values8 (11 : Fin 20) = Real.sqrt (values7 (11 : Fin 13)) by a158415_twelve_table]
        change (108252914866128728054401 / 62500000000000000000000 : Real) < Real.sqrt (values7 (11 : Fin 13))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : Real) < values7 (11 : Fin 13)
        rw [show values7 (11 : Fin 13) = 1 + values5 (3 : Fin 5) by a158415_twelve_table]
        change (11718693577013314172183891110162521866815468801 / 3906250000000000000000000000000000000000000000 : Real) < 1 + values5 (3 : Fin 5)
        have h11 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h12 : (1999999 / 1000000 : Real) < values5 (3 : Fin 5) := by
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (1999999 / 1000000 : Real) < 1 + 1
          have h13 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          have h14 : (9999999 / 10000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_401 :
    values14 (401 : Fin 455) < values14 (402 : Fin 455) := by
  have hleft : values14 (401 : Fin 455) < (3247 / 1000 : Real) := by
    rw [show values14 (401 : Fin 455) = 1 + values12 (104 : Fin 154) by rfl]
    change 1 + values12 (104 : Fin 154) < (3247 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (104 : Fin 154) < (11233 / 5000 : Real) := by
      rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by a158415_twelve_table]
      change 1 + values10 (15 : Fin 54) < (11233 / 5000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values10 (15 : Fin 54) < (124651 / 100000 : Real) := by
        rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by a158415_twelve_table]
        change Real.sqrt (values9 (15 : Fin 33)) < (124651 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (124651 / 100000 : Real))]
        norm_num
        change values9 (15 : Fin 33) < (15537871801 / 10000000000 : Real)
        rw [show values9 (15 : Fin 33) = Real.sqrt (values8 (15 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (15 : Fin 20)) < (15537871801 / 10000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (15537871801 / 10000000000 : Real))]
        norm_num
        change values8 (15 : Fin 20) < (241425460104310983601 / 100000000000000000000 : Real)
        rw [show values8 (15 : Fin 20) = 1 + values6 (3 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (3 : Fin 8) < (241425460104310983601 / 100000000000000000000 : Real)
        have h5 : 1 < (100001 / 100000 : Real) := by
          norm_num
        have h6 : values6 (3 : Fin 8) < (70711 / 50000 : Real) := by
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (3 : Fin 5)) < (70711 / 50000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
          norm_num
          change values5 (3 : Fin 5) < (5000045521 / 2500000000 : Real)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change 1 + 1 < (5000045521 / 2500000000 : Real)
          have h7 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          have h8 : 1 < (1000001 / 1000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (3247 / 1000 : Real) < values14 (402 : Fin 455) := by
    rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    change (3247 / 1000 : Real) < Real.sqrt 2 + values9 (18 : Fin 33)
    have h9 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h10 : (1847 / 1000 : Real) < values9 (18 : Fin 33) := by
      rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
      change (1847 / 1000 : Real) < Real.sqrt (values8 (18 : Fin 20))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (3411409 / 1000000 : Real) < values8 (18 : Fin 20)
      rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
      change (3411409 / 1000000 : Real) < 1 + values6 (6 : Fin 8)
      have h11 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h12 : (1207 / 500 : Real) < values6 (6 : Fin 8) := by
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change (1207 / 500 : Real) < 1 + Real.sqrt 2
        have h13 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h14 : (7071 / 5000 : Real) < Real.sqrt 2 := by
          change (7071 / 5000 : Real) < Real.sqrt (2)
          apply Real.lt_sqrt_of_sq_lt
          norm_num
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_402 :
    values14 (402 : Fin 455) < values14 (403 : Fin 455) := by
  have hleft : values14 (402 : Fin 455) < (1631 / 500 : Real) := by
    rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (18 : Fin 33) < (1631 / 500 : Real)
    have h1 : Real.sqrt 2 < (70711 / 50000 : Real) := by
      change Real.sqrt (2) < (70711 / 50000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
      norm_num
    have h2 : values9 (18 : Fin 33) < (23097 / 12500 : Real) := by
      rw [show values9 (18 : Fin 33) = Real.sqrt (values8 (18 : Fin 20)) by a158415_twelve_table]
      change Real.sqrt (values8 (18 : Fin 20)) < (23097 / 12500 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (23097 / 12500 : Real))]
      norm_num
      change values8 (18 : Fin 20) < (533471409 / 156250000 : Real)
      rw [show values8 (18 : Fin 20) = 1 + values6 (6 : Fin 8) by a158415_twelve_table]
      change 1 + values6 (6 : Fin 8) < (533471409 / 156250000 : Real)
      have h3 : 1 < (1000001 / 1000000 : Real) := by
        norm_num
      have h4 : values6 (6 : Fin 8) < (1207107 / 500000 : Real) := by
        rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
        change 1 + Real.sqrt 2 < (1207107 / 500000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : Real.sqrt 2 < (1767767 / 1250000 : Real) := by
          change Real.sqrt (2) < (1767767 / 1250000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (1767767 / 1250000 : Real))]
          norm_num
        linarith
      linarith
    linarith
  have hright : (1631 / 500 : Real) < values14 (403 : Fin 455) := by
    rw [show values14 (403 : Fin 455) = 1 + values12 (105 : Fin 154) by rfl]
    change (1631 / 500 : Real) < 1 + values12 (105 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (2279 / 1000 : Real) < values12 (105 : Fin 154) := by
      rw [show values12 (105 : Fin 154) = values5 (1 : Fin 5) + values6 (1 : Fin 8) by a158415_twelve_table]
      change (2279 / 1000 : Real) < values5 (1 : Fin 5) + values6 (1 : Fin 8)
      have h9 : (1189 / 1000 : Real) < values5 (1 : Fin 5) := by
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (1189 / 1000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (1413721 / 1000000 : Real) < Real.sqrt 2
        change (1413721 / 1000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h10 : (2181 / 2000 : Real) < values6 (1 : Fin 8) := by
        rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
        change (2181 / 2000 : Real) < Real.sqrt (values5 (1 : Fin 5))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (4756761 / 4000000 : Real) < values5 (1 : Fin 5)
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change (4756761 / 4000000 : Real) < Real.sqrt (Real.sqrt 2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (22626775211121 / 16000000000000 : Real) < Real.sqrt 2
        change (22626775211121 / 16000000000000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_404 :
    values14 (404 : Fin 455) < values14 (405 : Fin 455) := by
  have hleft : values14 (404 : Fin 455) < (32857 / 10000 : Real) := by
    rw [show values14 (404 : Fin 455) = 1 + values12 (106 : Fin 154) by rfl]
    change 1 + values12 (106 : Fin 154) < (32857 / 10000 : Real)
    have h1 : 1 < (100001 / 100000 : Real) := by
      norm_num
    have h2 : values12 (106 : Fin 154) < (45713 / 20000 : Real) := by
      rw [show values12 (106 : Fin 154) = 1 + values10 (16 : Fin 54) by a158415_twelve_table]
      change 1 + values10 (16 : Fin 54) < (45713 / 20000 : Real)
      have h3 : 1 < (10000001 / 10000000 : Real) := by
        norm_num
      have h4 : values10 (16 : Fin 54) < (3214121 / 2500000 : Real) := by
        rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by a158415_twelve_table]
        change Real.sqrt (values9 (16 : Fin 33)) < (3214121 / 2500000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (3214121 / 2500000 : Real))]
        norm_num
        change values9 (16 : Fin 33) < (10330573802641 / 6250000000000 : Real)
        rw [show values9 (16 : Fin 33) = Real.sqrt (values8 (16 : Fin 20)) by a158415_twelve_table]
        change Real.sqrt (values8 (16 : Fin 20)) < (10330573802641 / 6250000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (10330573802641 / 6250000000000 : Real))]
        norm_num
        change values8 (16 : Fin 20) < (106720755091812530818574881 / 39062500000000000000000000 : Real)
        rw [show values8 (16 : Fin 20) = 1 + values6 (4 : Fin 8) by a158415_twelve_table]
        change 1 + values6 (4 : Fin 8) < (106720755091812530818574881 / 39062500000000000000000000 : Real)
        have h5 : 1 < (10000001 / 10000000 : Real) := by
          norm_num
        have h6 : values6 (4 : Fin 8) < (17320509 / 10000000 : Real) := by
          rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
          change Real.sqrt (values5 (4 : Fin 5)) < (17320509 / 10000000 : Real)
          rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17320509 / 10000000 : Real))]
          norm_num
          change values5 (4 : Fin 5) < (300000032019081 / 100000000000000 : Real)
          rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
          change 1 + 2 < (300000032019081 / 100000000000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : 2 < (20000001 / 10000000 : Real) := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  have hright : (32857 / 10000 : Real) < values14 (405 : Fin 455) := by
    rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    change (32857 / 10000 : Real) < values6 (4 : Fin 8) + values7 (6 : Fin 13)
    have h9 : (34641 / 20000 : Real) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (34641 / 20000 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (1199998881 / 400000000 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (1199998881 / 400000000 : Real) < 1 + 2
      have h11 : (9999999 / 10000000 : Real) < 1 := by
        norm_num
      have h12 : (19999999 / 10000000 : Real) < 2 := by
        norm_num
      linarith
    have h10 : (155377 / 100000 : Real) < values7 (6 : Fin 13) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change (155377 / 100000 : Real) < Real.sqrt (values6 (6 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (24142012129 / 10000000000 : Real) < values6 (6 : Fin 8)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change (24142012129 / 10000000000 : Real) < 1 + Real.sqrt 2
      have h13 : (999999 / 1000000 : Real) < 1 := by
        norm_num
      have h14 : (141421 / 100000 : Real) < Real.sqrt 2 := by
        change (141421 / 100000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_405 :
    values14 (405 : Fin 455) < values14 (406 : Fin 455) := by
  have hleft : values14 (405 : Fin 455) < (1643 / 500 : Real) := by
    rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    change values6 (4 : Fin 8) + values7 (6 : Fin 13) < (1643 / 500 : Real)
    have h1 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    have h2 : values7 (6 : Fin 13) < (7769 / 5000 : Real) := by
      rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (6 : Fin 8)) < (7769 / 5000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (7769 / 5000 : Real))]
      norm_num
      change values6 (6 : Fin 8) < (60357361 / 25000000 : Real)
      rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
      change 1 + Real.sqrt 2 < (60357361 / 25000000 : Real)
      have h5 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h6 : Real.sqrt 2 < (70711 / 50000 : Real) := by
        change Real.sqrt (2) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (1643 / 500 : Real) < values14 (406 : Fin 455) := by
    rw [show values14 (406 : Fin 455) = 1 + values12 (107 : Fin 154) by rfl]
    change (1643 / 500 : Real) < 1 + values12 (107 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (579 / 250 : Real) < values12 (107 : Fin 154) := by
      rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by a158415_twelve_table]
      change (579 / 250 : Real) < 1 + values10 (17 : Fin 54)
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (131607 / 100000 : Real) < values10 (17 : Fin 54) := by
        rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by a158415_twelve_table]
        change (131607 / 100000 : Real) < Real.sqrt (values9 (17 : Fin 33))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (17320402449 / 10000000000 : Real) < values9 (17 : Fin 33)
        rw [show values9 (17 : Fin 33) = Real.sqrt (values8 (17 : Fin 20)) by a158415_twelve_table]
        change (17320402449 / 10000000000 : Real) < Real.sqrt (values8 (17 : Fin 20))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (299996340995325197601 / 100000000000000000000 : Real) < values8 (17 : Fin 20)
        rw [show values8 (17 : Fin 20) = 1 + values6 (5 : Fin 8) by a158415_twelve_table]
        change (299996340995325197601 / 100000000000000000000 : Real) < 1 + values6 (5 : Fin 8)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (199999 / 100000 : Real) < values6 (5 : Fin 8) := by
          rw [show values6 (5 : Fin 8) = 1 + 1 by a158415_twelve_table]
          change (199999 / 100000 : Real) < 1 + 1
          have h13 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h14 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_413 :
    values14 (413 : Fin 455) < values14 (414 : Fin 455) := by
  have hleft : values14 (413 : Fin 455) < (3459 / 1000 : Real) := by
    rw [show values14 (413 : Fin 455) = 1 + values12 (114 : Fin 154) by rfl]
    change 1 + values12 (114 : Fin 154) < (3459 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (114 : Fin 154) < (4917 / 2000 : Real) := by
      rw [show values12 (114 : Fin 154) = Real.sqrt 2 + values7 (1 : Fin 13) by a158415_twelve_table]
      change Real.sqrt 2 + values7 (1 : Fin 13) < (4917 / 2000 : Real)
      have h3 : Real.sqrt 2 < (707107 / 500000 : Real) := by
        change Real.sqrt (2) < (707107 / 500000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (707107 / 500000 : Real))]
        norm_num
      have h4 : values7 (1 : Fin 13) < (522137 / 500000 : Real) := by
        rw [show values7 (1 : Fin 13) = Real.sqrt (values6 (1 : Fin 8)) by a158415_twelve_table]
        change Real.sqrt (values6 (1 : Fin 8)) < (522137 / 500000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (522137 / 500000 : Real))]
        norm_num
        change values6 (1 : Fin 8) < (272627046769 / 250000000000 : Real)
        rw [show values6 (1 : Fin 8) = Real.sqrt (values5 (1 : Fin 5)) by a158415_twelve_table]
        change Real.sqrt (values5 (1 : Fin 5)) < (272627046769 / 250000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (272627046769 / 250000000000 : Real))]
        norm_num
        change values5 (1 : Fin 5) < (74325506629986513339361 / 62500000000000000000000 : Real)
        rw [show values5 (1 : Fin 5) = Real.sqrt (Real.sqrt 2) by a158415_twelve_table]
        change Real.sqrt (Real.sqrt 2) < (74325506629986513339361 / 62500000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (74325506629986513339361 / 62500000000000000000000 : Real))]
        norm_num
        change Real.sqrt 2 < (5524280935804169151130519072816875191551888321 / 3906250000000000000000000000000000000000000000 : Real)
        change Real.sqrt (2) < (5524280935804169151130519072816875191551888321 / 3906250000000000000000000000000000000000000000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (5524280935804169151130519072816875191551888321 / 3906250000000000000000000000000000000000000000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (3459 / 1000 : Real) < values14 (414 : Fin 455) := by
    rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    change (3459 / 1000 : Real) < values6 (4 : Fin 8) + values7 (7 : Fin 13)
    have h5 : (433 / 250 : Real) < values6 (4 : Fin 8) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values5 (4 : Fin 5))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values5 (4 : Fin 5)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + 2
      have h7 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h8 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    have h6 : (433 / 250 : Real) < values7 (7 : Fin 13) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change (433 / 250 : Real) < Real.sqrt (values6 (7 : Fin 8))
      apply Real.lt_sqrt_of_sq_lt
      norm_num
      change (187489 / 62500 : Real) < values6 (7 : Fin 8)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change (187489 / 62500 : Real) < 1 + 2
      have h9 : (99999 / 100000 : Real) < 1 := by
        norm_num
      have h10 : (199999 / 100000 : Real) < 2 := by
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_414 :
    values14 (414 : Fin 455) < values14 (415 : Fin 455) := by
  have hleft : values14 (414 : Fin 455) < (693 / 200 : Real) := by
    rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    change values6 (4 : Fin 8) + values7 (7 : Fin 13) < (693 / 200 : Real)
    have h1 : values6 (4 : Fin 8) < (17321 / 10000 : Real) := by
      rw [show values6 (4 : Fin 8) = Real.sqrt (values5 (4 : Fin 5)) by a158415_twelve_table]
      change Real.sqrt (values5 (4 : Fin 5)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values5 (4 : Fin 5) < (300017041 / 100000000 : Real)
      rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    have h2 : values7 (7 : Fin 13) < (17321 / 10000 : Real) := by
      rw [show values7 (7 : Fin 13) = Real.sqrt (values6 (7 : Fin 8)) by a158415_twelve_table]
      change Real.sqrt (values6 (7 : Fin 8)) < (17321 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (17321 / 10000 : Real))]
      norm_num
      change values6 (7 : Fin 8) < (300017041 / 100000000 : Real)
      rw [show values6 (7 : Fin 8) = 1 + 2 by a158415_twelve_table]
      change 1 + 2 < (300017041 / 100000000 : Real)
      have h5 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h6 : 2 < (200001 / 100000 : Real) := by
        norm_num
      linarith
    linarith
  have hright : (693 / 200 : Real) < values14 (415 : Fin 455) := by
    rw [show values14 (415 : Fin 455) = 1 + values12 (115 : Fin 154) by rfl]
    change (693 / 200 : Real) < 1 + values12 (115 : Fin 154)
    have h7 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h8 : (2479 / 1000 : Real) < values12 (115 : Fin 154) := by
      rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by a158415_twelve_table]
      change (2479 / 1000 : Real) < 1 + values10 (22 : Fin 54)
      have h9 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h10 : (2959 / 2000 : Real) < values10 (22 : Fin 54) := by
        rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by a158415_twelve_table]
        change (2959 / 2000 : Real) < Real.sqrt (values9 (22 : Fin 33))
        apply Real.lt_sqrt_of_sq_lt
        norm_num
        change (8755681 / 4000000 : Real) < values9 (22 : Fin 33)
        rw [show values9 (22 : Fin 33) = 1 + values7 (3 : Fin 13) by a158415_twelve_table]
        change (8755681 / 4000000 : Real) < 1 + values7 (3 : Fin 13)
        have h11 : (99999 / 100000 : Real) < 1 := by
          norm_num
        have h12 : (2973 / 2500 : Real) < values7 (3 : Fin 13) := by
          rw [show values7 (3 : Fin 13) = Real.sqrt (values6 (3 : Fin 8)) by a158415_twelve_table]
          change (2973 / 2500 : Real) < Real.sqrt (values6 (3 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (8838729 / 6250000 : Real) < values6 (3 : Fin 8)
          rw [show values6 (3 : Fin 8) = Real.sqrt (values5 (3 : Fin 5)) by a158415_twelve_table]
          change (8838729 / 6250000 : Real) < Real.sqrt (values5 (3 : Fin 5))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (78123130335441 / 39062500000000 : Real) < values5 (3 : Fin 5)
          rw [show values5 (3 : Fin 5) = 1 + 1 by a158415_twelve_table]
          change (78123130335441 / 39062500000000 : Real) < 1 + 1
          have h13 : (99999 / 100000 : Real) < 1 := by
            norm_num
          have h14 : (99999 / 100000 : Real) < 1 := by
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_437 :
    values14 (437 : Fin 455) < values14 (438 : Fin 455) := by
  have hleft : values14 (437 : Fin 455) < (4237 / 1000 : Real) := by
    rw [show values14 (437 : Fin 455) = 1 + values12 (137 : Fin 154) by rfl]
    change 1 + values12 (137 : Fin 154) < (4237 / 1000 : Real)
    have h1 : 1 < (10001 / 10000 : Real) := by
      norm_num
    have h2 : values12 (137 : Fin 154) < (32361 / 10000 : Real) := by
      rw [show values12 (137 : Fin 154) = 1 + values10 (37 : Fin 54) by a158415_twelve_table]
      change 1 + values10 (37 : Fin 54) < (32361 / 10000 : Real)
      have h3 : 1 < (100001 / 100000 : Real) := by
        norm_num
      have h4 : values10 (37 : Fin 54) < (223607 / 100000 : Real) := by
        rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by a158415_twelve_table]
        change Real.sqrt (values9 (32 : Fin 33)) < (223607 / 100000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (223607 / 100000 : Real))]
        norm_num
        change values9 (32 : Fin 33) < (50000090449 / 10000000000 : Real)
        rw [show values9 (32 : Fin 33) = 1 + values7 (12 : Fin 13) by a158415_twelve_table]
        change 1 + values7 (12 : Fin 13) < (50000090449 / 10000000000 : Real)
        have h5 : 1 < (1000001 / 1000000 : Real) := by
          norm_num
        have h6 : values7 (12 : Fin 13) < (4000001 / 1000000 : Real) := by
          rw [show values7 (12 : Fin 13) = 1 + values5 (4 : Fin 5) by a158415_twelve_table]
          change 1 + values5 (4 : Fin 5) < (4000001 / 1000000 : Real)
          have h7 : 1 < (10000001 / 10000000 : Real) := by
            norm_num
          have h8 : values5 (4 : Fin 5) < (30000001 / 10000000 : Real) := by
            rw [show values5 (4 : Fin 5) = 1 + 2 by a158415_twelve_table]
            change 1 + 2 < (30000001 / 10000000 : Real)
            have h9 : 1 < (100000001 / 100000000 : Real) := by
              norm_num
            have h10 : 2 < (200000001 / 100000000 : Real) := by
              norm_num
            linarith
          linarith
        linarith
      linarith
    linarith
  have hright : (4237 / 1000 : Real) < values14 (438 : Fin 455) := by
    rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    change (4237 / 1000 : Real) < Real.sqrt 2 + values9 (27 : Fin 33)
    have h11 : (707 / 500 : Real) < Real.sqrt 2 := by
      change (707 / 500 : Real) < Real.sqrt (2)
      apply Real.lt_sqrt_of_sq_lt
      norm_num
    have h12 : (707 / 250 : Real) < values9 (27 : Fin 33) := by
      rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
      change (707 / 250 : Real) < Real.sqrt 2 + Real.sqrt 2
      have h13 : (7071 / 5000 : Real) < Real.sqrt 2 := by
        change (7071 / 5000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      have h14 : (7071 / 5000 : Real) < Real.sqrt 2 := by
        change (7071 / 5000 : Real) < Real.sqrt (2)
        apply Real.lt_sqrt_of_sq_lt
        norm_num
      linarith
    linarith
  linarith

set_option linter.unusedTactic false in
theorem values14_special_438 :
    values14 (438 : Fin 455) < values14 (439 : Fin 455) := by
  have hleft : values14 (438 : Fin 455) < (4243 / 1000 : Real) := by
    rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    change Real.sqrt 2 + values9 (27 : Fin 33) < (4243 / 1000 : Real)
    have h1 : Real.sqrt 2 < (14143 / 10000 : Real) := by
      change Real.sqrt (2) < (14143 / 10000 : Real)
      rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (14143 / 10000 : Real))]
      norm_num
    have h2 : values9 (27 : Fin 33) < (5657 / 2000 : Real) := by
      rw [show values9 (27 : Fin 33) = Real.sqrt 2 + Real.sqrt 2 by a158415_twelve_table]
      change Real.sqrt 2 + Real.sqrt 2 < (5657 / 2000 : Real)
      have h3 : Real.sqrt 2 < (70711 / 50000 : Real) := by
        change Real.sqrt (2) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
      have h4 : Real.sqrt 2 < (70711 / 50000 : Real) := by
        change Real.sqrt (2) < (70711 / 50000 : Real)
        rw [Real.sqrt_lt' (by norm_num : (0 : Real) < (70711 / 50000 : Real))]
        norm_num
      linarith
    linarith
  have hright : (4243 / 1000 : Real) < values14 (439 : Fin 455) := by
    rw [show values14 (439 : Fin 455) = 1 + values12 (138 : Fin 154) by rfl]
    change (4243 / 1000 : Real) < 1 + values12 (138 : Fin 154)
    have h5 : (999 / 1000 : Real) < 1 := by
      norm_num
    have h6 : (1623 / 500 : Real) < values12 (138 : Fin 154) := by
      rw [show values12 (138 : Fin 154) = 1 + values10 (38 : Fin 54) by a158415_twelve_table]
      change (1623 / 500 : Real) < 1 + values10 (38 : Fin 54)
      have h7 : (9999 / 10000 : Real) < 1 := by
        norm_num
      have h8 : (4493 / 2000 : Real) < values10 (38 : Fin 54) := by
        rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by a158415_twelve_table]
        change (4493 / 2000 : Real) < 1 + values8 (6 : Fin 20)
        have h9 : (999999 / 1000000 : Real) < 1 := by
          norm_num
        have h10 : (155813 / 125000 : Real) < values8 (6 : Fin 20) := by
          rw [show values8 (6 : Fin 20) = Real.sqrt (values7 (6 : Fin 13)) by a158415_twelve_table]
          change (155813 / 125000 : Real) < Real.sqrt (values7 (6 : Fin 13))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (24277690969 / 15625000000 : Real) < values7 (6 : Fin 13)
          rw [show values7 (6 : Fin 13) = Real.sqrt (values6 (6 : Fin 8)) by a158415_twelve_table]
          change (24277690969 / 15625000000 : Real) < Real.sqrt (values6 (6 : Fin 8))
          apply Real.lt_sqrt_of_sq_lt
          norm_num
          change (589406278786264158961 / 244140625000000000000 : Real) < values6 (6 : Fin 8)
          rw [show values6 (6 : Fin 8) = 1 + Real.sqrt 2 by a158415_twelve_table]
          change (589406278786264158961 / 244140625000000000000 : Real) < 1 + Real.sqrt 2
          have h11 : (999999 / 1000000 : Real) < 1 := by
            norm_num
          have h12 : (1414213 / 1000000 : Real) < Real.sqrt 2 := by
            change (1414213 / 1000000 : Real) < Real.sqrt (2)
            apply Real.lt_sqrt_of_sq_lt
            norm_num
          linarith
        linarith
      linarith
    linarith
  linarith
set_option maxHeartbeats 2000000 in
theorem values14_strictMono : StrictMono values14 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact sqrt_values13_strictMono (by decide)
  next => exact values14_special_249
  next =>
    change 1 + values12 (1 : Fin 154) < 1 + values12 (2 : Fin 154)
    linarith [values12_strictMono (by native_decide : (1 : Fin 154) < 2)]
  next =>
    change 1 + values12 (2 : Fin 154) < 1 + values12 (3 : Fin 154)
    linarith [values12_strictMono (by native_decide : (2 : Fin 154) < 3)]
  next =>
    change 1 + values12 (3 : Fin 154) < 1 + values12 (4 : Fin 154)
    linarith [values12_strictMono (by native_decide : (3 : Fin 154) < 4)]
  next =>
    change 1 + values12 (4 : Fin 154) < 1 + values12 (5 : Fin 154)
    linarith [values12_strictMono (by native_decide : (4 : Fin 154) < 5)]
  next => exact values14_special_254
  next => exact values14_special_255
  next =>
    change 1 + values12 (6 : Fin 154) < 1 + values12 (7 : Fin 154)
    linarith [values12_strictMono (by native_decide : (6 : Fin 154) < 7)]
  next =>
    change 1 + values12 (7 : Fin 154) < 1 + values12 (8 : Fin 154)
    linarith [values12_strictMono (by native_decide : (7 : Fin 154) < 8)]
  next => exact values14_special_258
  next => exact values14_special_259
  next =>
    change 1 + values12 (9 : Fin 154) < 1 + values12 (10 : Fin 154)
    linarith [values12_strictMono (by native_decide : (9 : Fin 154) < 10)]
  next =>
    change 1 + values12 (10 : Fin 154) < 1 + values12 (11 : Fin 154)
    linarith [values12_strictMono (by native_decide : (10 : Fin 154) < 11)]
  next => exact values14_special_262
  next => exact values14_special_263
  next => exact values14_special_264
  next => exact values14_special_265
  next =>
    change 1 + values12 (13 : Fin 154) < 1 + values12 (14 : Fin 154)
    linarith [values12_strictMono (by native_decide : (13 : Fin 154) < 14)]
  next =>
    change 1 + values12 (14 : Fin 154) < 1 + values12 (15 : Fin 154)
    linarith [values12_strictMono (by native_decide : (14 : Fin 154) < 15)]
  next =>
    change 1 + values12 (15 : Fin 154) < 1 + values12 (16 : Fin 154)
    linarith [values12_strictMono (by native_decide : (15 : Fin 154) < 16)]
  next =>
    change 1 + values12 (16 : Fin 154) < 1 + values12 (17 : Fin 154)
    linarith [values12_strictMono (by native_decide : (16 : Fin 154) < 17)]
  next => exact values14_special_270
  next => exact values14_special_271
  next =>
    change 1 + values12 (18 : Fin 154) < 1 + values12 (19 : Fin 154)
    linarith [values12_strictMono (by native_decide : (18 : Fin 154) < 19)]
  next =>
    change 1 + values12 (19 : Fin 154) < 1 + values12 (20 : Fin 154)
    linarith [values12_strictMono (by native_decide : (19 : Fin 154) < 20)]
  next =>
    change 1 + values12 (20 : Fin 154) < 1 + values12 (21 : Fin 154)
    linarith [values12_strictMono (by native_decide : (20 : Fin 154) < 21)]
  next => exact values14_special_275
  next => exact values14_special_276
  next =>
    change 1 + values12 (22 : Fin 154) < 1 + values12 (23 : Fin 154)
    linarith [values12_strictMono (by native_decide : (22 : Fin 154) < 23)]
  next =>
    change 1 + values12 (23 : Fin 154) < 1 + values12 (24 : Fin 154)
    linarith [values12_strictMono (by native_decide : (23 : Fin 154) < 24)]
  next =>
    change 1 + values12 (24 : Fin 154) < 1 + values12 (25 : Fin 154)
    linarith [values12_strictMono (by native_decide : (24 : Fin 154) < 25)]
  next =>
    change 1 + values12 (25 : Fin 154) < 1 + values12 (26 : Fin 154)
    linarith [values12_strictMono (by native_decide : (25 : Fin 154) < 26)]
  next => exact values14_special_281
  next => exact values14_special_282
  next => exact values14_special_283
  next =>
    change 1 + values12 (27 : Fin 154) < 1 + values12 (28 : Fin 154)
    linarith [values12_strictMono (by native_decide : (27 : Fin 154) < 28)]
  next =>
    change 1 + values12 (28 : Fin 154) < 1 + values12 (29 : Fin 154)
    linarith [values12_strictMono (by native_decide : (28 : Fin 154) < 29)]
  next =>
    change 1 + values12 (29 : Fin 154) < 1 + values12 (30 : Fin 154)
    linarith [values12_strictMono (by native_decide : (29 : Fin 154) < 30)]
  next => exact values14_special_287
  next => exact values14_special_288
  next => exact values14_special_289
  next =>
    change 1 + values12 (31 : Fin 154) < 1 + values12 (32 : Fin 154)
    linarith [values12_strictMono (by native_decide : (31 : Fin 154) < 32)]
  next =>
    change 1 + values12 (32 : Fin 154) < 1 + values12 (33 : Fin 154)
    linarith [values12_strictMono (by native_decide : (32 : Fin 154) < 33)]
  next => exact values14_special_292
  next => exact values14_special_293
  next =>
    change 1 + values12 (34 : Fin 154) < 1 + values12 (35 : Fin 154)
    linarith [values12_strictMono (by native_decide : (34 : Fin 154) < 35)]
  next => exact values14_special_295
  next => exact values14_special_296
  next =>
    change 1 + values12 (36 : Fin 154) < 1 + values12 (37 : Fin 154)
    linarith [values12_strictMono (by native_decide : (36 : Fin 154) < 37)]
  next =>
    change 1 + values12 (37 : Fin 154) < 1 + values12 (38 : Fin 154)
    linarith [values12_strictMono (by native_decide : (37 : Fin 154) < 38)]
  next => exact values14_special_299
  next => exact values14_special_300
  next => exact values14_special_301
  next => exact values14_special_302
  next =>
    change 1 + values12 (40 : Fin 154) < 1 + values12 (41 : Fin 154)
    linarith [values12_strictMono (by native_decide : (40 : Fin 154) < 41)]
  next =>
    change 1 + values12 (41 : Fin 154) < 1 + values12 (42 : Fin 154)
    linarith [values12_strictMono (by native_decide : (41 : Fin 154) < 42)]
  next =>
    change 1 + values12 (42 : Fin 154) < 1 + values12 (43 : Fin 154)
    linarith [values12_strictMono (by native_decide : (42 : Fin 154) < 43)]
  next => exact values14_special_306
  next => exact values14_special_307
  next => exact values14_special_308
  next =>
    change 1 + values12 (44 : Fin 154) < 1 + values12 (45 : Fin 154)
    linarith [values12_strictMono (by native_decide : (44 : Fin 154) < 45)]
  next =>
    change 1 + values12 (45 : Fin 154) < 1 + values12 (46 : Fin 154)
    linarith [values12_strictMono (by native_decide : (45 : Fin 154) < 46)]
  next =>
    change 1 + values12 (46 : Fin 154) < 1 + values12 (47 : Fin 154)
    linarith [values12_strictMono (by native_decide : (46 : Fin 154) < 47)]
  next => exact values14_special_312
  next => exact values14_special_313
  next => exact values14_special_314
  next => exact values14_special_315
  next => exact values14_special_316
  next => exact values14_special_317
  next => exact values14_special_318
  next => exact values14_special_319
  next =>
    change 1 + values12 (51 : Fin 154) < 1 + values12 (52 : Fin 154)
    linarith [values12_strictMono (by native_decide : (51 : Fin 154) < 52)]
  next =>
    change 1 + values12 (52 : Fin 154) < 1 + values12 (53 : Fin 154)
    linarith [values12_strictMono (by native_decide : (52 : Fin 154) < 53)]
  next => exact values14_special_322
  next => exact values14_special_323
  next => exact values14_special_324
  next => exact values14_special_325
  next => exact values14_special_326
  next =>
    change 1 + values12 (55 : Fin 154) < 1 + values12 (56 : Fin 154)
    linarith [values12_strictMono (by native_decide : (55 : Fin 154) < 56)]
  next =>
    change 1 + values12 (56 : Fin 154) < 1 + values12 (57 : Fin 154)
    linarith [values12_strictMono (by native_decide : (56 : Fin 154) < 57)]
  next => exact values14_special_329
  next => exact values14_special_330
  next => exact values14_special_331
  next => exact values14_special_332
  next =>
    change 1 + values12 (59 : Fin 154) < 1 + values12 (60 : Fin 154)
    linarith [values12_strictMono (by native_decide : (59 : Fin 154) < 60)]
  next => exact values14_special_334
  next => exact values14_special_335
  next =>
    change 1 + values12 (61 : Fin 154) < 1 + values12 (62 : Fin 154)
    linarith [values12_strictMono (by native_decide : (61 : Fin 154) < 62)]
  next =>
    change 1 + values12 (62 : Fin 154) < 1 + values12 (63 : Fin 154)
    linarith [values12_strictMono (by native_decide : (62 : Fin 154) < 63)]
  next => exact values14_special_338
  next => exact values14_special_339
  next => exact values14_special_340
  next => exact values14_special_341
  next => exact values14_special_342
  next =>
    change 1 + values12 (65 : Fin 154) < 1 + values12 (66 : Fin 154)
    linarith [values12_strictMono (by native_decide : (65 : Fin 154) < 66)]
  next => exact values14_special_344
  next => exact values14_special_345
  next =>
    change 1 + values12 (67 : Fin 154) < 1 + values12 (68 : Fin 154)
    linarith [values12_strictMono (by native_decide : (67 : Fin 154) < 68)]
  next =>
    change 1 + values12 (68 : Fin 154) < 1 + values12 (69 : Fin 154)
    linarith [values12_strictMono (by native_decide : (68 : Fin 154) < 69)]
  next =>
    change 1 + values12 (69 : Fin 154) < 1 + values12 (70 : Fin 154)
    linarith [values12_strictMono (by native_decide : (69 : Fin 154) < 70)]
  next => exact values14_special_349
  next => exact values14_special_350
  next =>
    change 1 + values12 (71 : Fin 154) < 1 + values12 (72 : Fin 154)
    linarith [values12_strictMono (by native_decide : (71 : Fin 154) < 72)]
  next => exact values14_special_352
  next => exact values14_special_353
  next => exact values14_special_354
  next => exact values14_special_355
  next => exact values14_special_356
  next => exact values14_special_357
  next => exact values14_special_358
  next =>
    change 1 + values12 (74 : Fin 154) < 1 + values12 (75 : Fin 154)
    linarith [values12_strictMono (by native_decide : (74 : Fin 154) < 75)]
  next => exact values14_special_360
  next => exact values14_special_361
  next => exact values14_special_362
  next => exact values14_special_363
  next =>
    change 1 + values12 (77 : Fin 154) < 1 + values12 (78 : Fin 154)
    linarith [values12_strictMono (by native_decide : (77 : Fin 154) < 78)]
  next =>
    change 1 + values12 (78 : Fin 154) < 1 + values12 (79 : Fin 154)
    linarith [values12_strictMono (by native_decide : (78 : Fin 154) < 79)]
  next => exact values14_special_366
  next => exact values14_special_367
  next =>
    change 1 + values12 (80 : Fin 154) < 1 + values12 (81 : Fin 154)
    linarith [values12_strictMono (by native_decide : (80 : Fin 154) < 81)]
  next => exact values14_special_369
  next => exact values14_special_370
  next => exact values14_special_371
  next => exact values14_special_372
  next => exact values14_special_373
  next => exact values14_special_374
  next => exact values14_special_375
  next => exact values14_special_376
  next =>
    change 1 + values12 (84 : Fin 154) < 1 + values12 (85 : Fin 154)
    linarith [values12_strictMono (by native_decide : (84 : Fin 154) < 85)]
  next => exact values14_special_378
  next => exact values14_special_379
  next =>
    change 1 + values12 (86 : Fin 154) < 1 + values12 (87 : Fin 154)
    linarith [values12_strictMono (by native_decide : (86 : Fin 154) < 87)]
  next =>
    change 1 + values12 (87 : Fin 154) < 1 + values12 (88 : Fin 154)
    linarith [values12_strictMono (by native_decide : (87 : Fin 154) < 88)]
  next =>
    change 1 + values12 (88 : Fin 154) < 1 + values12 (89 : Fin 154)
    linarith [values12_strictMono (by native_decide : (88 : Fin 154) < 89)]
  next =>
    change 1 + values12 (89 : Fin 154) < 1 + values12 (90 : Fin 154)
    linarith [values12_strictMono (by native_decide : (89 : Fin 154) < 90)]
  next =>
    change 1 + values12 (90 : Fin 154) < 1 + values12 (91 : Fin 154)
    linarith [values12_strictMono (by native_decide : (90 : Fin 154) < 91)]
  next =>
    change 1 + values12 (91 : Fin 154) < 1 + values12 (92 : Fin 154)
    linarith [values12_strictMono (by native_decide : (91 : Fin 154) < 92)]
  next => exact values14_special_386
  next => exact values14_special_387
  next => exact values14_special_388
  next => exact values14_special_389
  next =>
    change 1 + values12 (94 : Fin 154) < 1 + values12 (95 : Fin 154)
    linarith [values12_strictMono (by native_decide : (94 : Fin 154) < 95)]
  next =>
    change 1 + values12 (95 : Fin 154) < 1 + values12 (96 : Fin 154)
    linarith [values12_strictMono (by native_decide : (95 : Fin 154) < 96)]
  next =>
    change 1 + values12 (96 : Fin 154) < 1 + values12 (97 : Fin 154)
    linarith [values12_strictMono (by native_decide : (96 : Fin 154) < 97)]
  next =>
    change 1 + values12 (97 : Fin 154) < 1 + values12 (98 : Fin 154)
    linarith [values12_strictMono (by native_decide : (97 : Fin 154) < 98)]
  next => exact values14_special_394
  next => exact values14_special_395
  next =>
    change 1 + values12 (99 : Fin 154) < 1 + values12 (100 : Fin 154)
    linarith [values12_strictMono (by native_decide : (99 : Fin 154) < 100)]
  next =>
    change 1 + values12 (100 : Fin 154) < 1 + values12 (101 : Fin 154)
    linarith [values12_strictMono (by native_decide : (100 : Fin 154) < 101)]
  next =>
    change 1 + values12 (101 : Fin 154) < 1 + values12 (102 : Fin 154)
    linarith [values12_strictMono (by native_decide : (101 : Fin 154) < 102)]
  next =>
    change 1 + values12 (102 : Fin 154) < 1 + values12 (103 : Fin 154)
    linarith [values12_strictMono (by native_decide : (102 : Fin 154) < 103)]
  next =>
    change 1 + values12 (103 : Fin 154) < 1 + values12 (104 : Fin 154)
    linarith [values12_strictMono (by native_decide : (103 : Fin 154) < 104)]
  next => exact values14_special_401
  next => exact values14_special_402
  next =>
    change 1 + values12 (105 : Fin 154) < 1 + values12 (106 : Fin 154)
    linarith [values12_strictMono (by native_decide : (105 : Fin 154) < 106)]
  next => exact values14_special_404
  next => exact values14_special_405
  next =>
    change 1 + values12 (107 : Fin 154) < 1 + values12 (108 : Fin 154)
    linarith [values12_strictMono (by native_decide : (107 : Fin 154) < 108)]
  next =>
    change 1 + values12 (108 : Fin 154) < 1 + values12 (109 : Fin 154)
    linarith [values12_strictMono (by native_decide : (108 : Fin 154) < 109)]
  next =>
    change 1 + values12 (109 : Fin 154) < 1 + values12 (110 : Fin 154)
    linarith [values12_strictMono (by native_decide : (109 : Fin 154) < 110)]
  next =>
    change 1 + values12 (110 : Fin 154) < 1 + values12 (111 : Fin 154)
    linarith [values12_strictMono (by native_decide : (110 : Fin 154) < 111)]
  next =>
    change 1 + values12 (111 : Fin 154) < 1 + values12 (112 : Fin 154)
    linarith [values12_strictMono (by native_decide : (111 : Fin 154) < 112)]
  next =>
    change 1 + values12 (112 : Fin 154) < 1 + values12 (113 : Fin 154)
    linarith [values12_strictMono (by native_decide : (112 : Fin 154) < 113)]
  next =>
    change 1 + values12 (113 : Fin 154) < 1 + values12 (114 : Fin 154)
    linarith [values12_strictMono (by native_decide : (113 : Fin 154) < 114)]
  next => exact values14_special_413
  next => exact values14_special_414
  next =>
    change 1 + values12 (115 : Fin 154) < 1 + values12 (116 : Fin 154)
    linarith [values12_strictMono (by native_decide : (115 : Fin 154) < 116)]
  next =>
    change 1 + values12 (116 : Fin 154) < 1 + values12 (117 : Fin 154)
    linarith [values12_strictMono (by native_decide : (116 : Fin 154) < 117)]
  next =>
    change 1 + values12 (117 : Fin 154) < 1 + values12 (118 : Fin 154)
    linarith [values12_strictMono (by native_decide : (117 : Fin 154) < 118)]
  next =>
    change 1 + values12 (118 : Fin 154) < 1 + values12 (119 : Fin 154)
    linarith [values12_strictMono (by native_decide : (118 : Fin 154) < 119)]
  next =>
    change 1 + values12 (119 : Fin 154) < 1 + values12 (120 : Fin 154)
    linarith [values12_strictMono (by native_decide : (119 : Fin 154) < 120)]
  next =>
    change 1 + values12 (120 : Fin 154) < 1 + values12 (121 : Fin 154)
    linarith [values12_strictMono (by native_decide : (120 : Fin 154) < 121)]
  next =>
    change 1 + values12 (121 : Fin 154) < 1 + values12 (122 : Fin 154)
    linarith [values12_strictMono (by native_decide : (121 : Fin 154) < 122)]
  next =>
    change 1 + values12 (122 : Fin 154) < 1 + values12 (123 : Fin 154)
    linarith [values12_strictMono (by native_decide : (122 : Fin 154) < 123)]
  next =>
    change 1 + values12 (123 : Fin 154) < 1 + values12 (124 : Fin 154)
    linarith [values12_strictMono (by native_decide : (123 : Fin 154) < 124)]
  next =>
    change 1 + values12 (124 : Fin 154) < 1 + values12 (125 : Fin 154)
    linarith [values12_strictMono (by native_decide : (124 : Fin 154) < 125)]
  next =>
    change 1 + values12 (125 : Fin 154) < 1 + values12 (126 : Fin 154)
    linarith [values12_strictMono (by native_decide : (125 : Fin 154) < 126)]
  next =>
    change 1 + values12 (126 : Fin 154) < 1 + values12 (127 : Fin 154)
    linarith [values12_strictMono (by native_decide : (126 : Fin 154) < 127)]
  next =>
    change 1 + values12 (127 : Fin 154) < 1 + values12 (128 : Fin 154)
    linarith [values12_strictMono (by native_decide : (127 : Fin 154) < 128)]
  next =>
    change 1 + values12 (128 : Fin 154) < 1 + values12 (129 : Fin 154)
    linarith [values12_strictMono (by native_decide : (128 : Fin 154) < 129)]
  next =>
    change 1 + values12 (129 : Fin 154) < 1 + values12 (130 : Fin 154)
    linarith [values12_strictMono (by native_decide : (129 : Fin 154) < 130)]
  next =>
    change 1 + values12 (130 : Fin 154) < 1 + values12 (131 : Fin 154)
    linarith [values12_strictMono (by native_decide : (130 : Fin 154) < 131)]
  next =>
    change 1 + values12 (131 : Fin 154) < 1 + values12 (132 : Fin 154)
    linarith [values12_strictMono (by native_decide : (131 : Fin 154) < 132)]
  next =>
    change 1 + values12 (132 : Fin 154) < 1 + values12 (133 : Fin 154)
    linarith [values12_strictMono (by native_decide : (132 : Fin 154) < 133)]
  next =>
    change 1 + values12 (133 : Fin 154) < 1 + values12 (134 : Fin 154)
    linarith [values12_strictMono (by native_decide : (133 : Fin 154) < 134)]
  next =>
    change 1 + values12 (134 : Fin 154) < 1 + values12 (135 : Fin 154)
    linarith [values12_strictMono (by native_decide : (134 : Fin 154) < 135)]
  next =>
    change 1 + values12 (135 : Fin 154) < 1 + values12 (136 : Fin 154)
    linarith [values12_strictMono (by native_decide : (135 : Fin 154) < 136)]
  next =>
    change 1 + values12 (136 : Fin 154) < 1 + values12 (137 : Fin 154)
    linarith [values12_strictMono (by native_decide : (136 : Fin 154) < 137)]
  next => exact values14_special_437
  next => exact values14_special_438
  next =>
    change 1 + values12 (138 : Fin 154) < 1 + values12 (139 : Fin 154)
    linarith [values12_strictMono (by native_decide : (138 : Fin 154) < 139)]
  next =>
    change 1 + values12 (139 : Fin 154) < 1 + values12 (140 : Fin 154)
    linarith [values12_strictMono (by native_decide : (139 : Fin 154) < 140)]
  next =>
    change 1 + values12 (140 : Fin 154) < 1 + values12 (141 : Fin 154)
    linarith [values12_strictMono (by native_decide : (140 : Fin 154) < 141)]
  next =>
    change 1 + values12 (141 : Fin 154) < 1 + values12 (142 : Fin 154)
    linarith [values12_strictMono (by native_decide : (141 : Fin 154) < 142)]
  next =>
    change 1 + values12 (142 : Fin 154) < 1 + values12 (143 : Fin 154)
    linarith [values12_strictMono (by native_decide : (142 : Fin 154) < 143)]
  next =>
    change 1 + values12 (143 : Fin 154) < 1 + values12 (144 : Fin 154)
    linarith [values12_strictMono (by native_decide : (143 : Fin 154) < 144)]
  next =>
    change 1 + values12 (144 : Fin 154) < 1 + values12 (145 : Fin 154)
    linarith [values12_strictMono (by native_decide : (144 : Fin 154) < 145)]
  next =>
    change 1 + values12 (145 : Fin 154) < 1 + values12 (146 : Fin 154)
    linarith [values12_strictMono (by native_decide : (145 : Fin 154) < 146)]
  next =>
    change 1 + values12 (146 : Fin 154) < 1 + values12 (147 : Fin 154)
    linarith [values12_strictMono (by native_decide : (146 : Fin 154) < 147)]
  next =>
    change 1 + values12 (147 : Fin 154) < 1 + values12 (148 : Fin 154)
    linarith [values12_strictMono (by native_decide : (147 : Fin 154) < 148)]
  next =>
    change 1 + values12 (148 : Fin 154) < 1 + values12 (149 : Fin 154)
    linarith [values12_strictMono (by native_decide : (148 : Fin 154) < 149)]
  next =>
    change 1 + values12 (149 : Fin 154) < 1 + values12 (150 : Fin 154)
    linarith [values12_strictMono (by native_decide : (149 : Fin 154) < 150)]
  next =>
    change 1 + values12 (150 : Fin 154) < 1 + values12 (151 : Fin 154)
    linarith [values12_strictMono (by native_decide : (150 : Fin 154) < 151)]
  next =>
    change 1 + values12 (151 : Fin 154) < 1 + values12 (152 : Fin 154)
    linarith [values12_strictMono (by native_decide : (151 : Fin 154) < 152)]
  next =>
    change 1 + values12 (152 : Fin 154) < 1 + values12 (153 : Fin 154)
    linarith [values12_strictMono (by native_decide : (152 : Fin 154) < 153)]
theorem values14_range_ncard :
    (Set.range values14).ncard = 455 := by
  rw [Set.ncard_range_of_injective values14_strictMono.injective]
  norm_num

@[simp] theorem sqrt_values13_mem_recursiveValueSet_fourteen (i : Fin 264) :
    Real.sqrt (values13 i) ∈ recursiveValueSet 14 := by
  rw [recursiveValueSet]
  exact Or.inl ⟨values13 i, values13_mem_recursiveValueSet i, rfl⟩

@[simp] theorem one_add_values12_mem_recursiveValueSet_fourteen (i : Fin 154) :
    1 + values12 i ∈ recursiveValueSet 14 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨0, by decide⟩, 1, ?_, values12 i, ?_, rfl⟩
  · simp [recursiveValueSet]
  · change values12 i ∈ recursiveValueSet 12
    rw [recursiveValueSet_twelve]
    exact ⟨i, rfl⟩

@[simp] theorem values6_add_values7_mem_recursiveValueSet_fourteen
    (i : Fin 8) (j : Fin 13) :
    values6 i + values7 j ∈ recursiveValueSet 14 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨5, by decide⟩, values6 i, ?_, values7 j, ?_, rfl⟩
  · change values6 i ∈ recursiveValueSet 6
    rw [recursiveValueSet_six_eq_range_values6]
    exact ⟨i, rfl⟩
  · change values7 j ∈ recursiveValueSet 7
    rw [recursiveValueSet_seven]
    exact ⟨j, rfl⟩

@[simp] theorem values5_add_values8_mem_recursiveValueSet_fourteen
    (i : Fin 5) (j : Fin 20) :
    values5 i + values8 j ∈ recursiveValueSet 14 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨4, by decide⟩, values5 i, ?_, values8 j, ?_, rfl⟩
  · change values5 i ∈ recursiveValueSet 5
    rw [recursiveValueSet_five_eq_range_values5]
    exact ⟨i, rfl⟩
  · change values8 j ∈ recursiveValueSet 8
    rw [recursiveValueSet_eight]
    exact ⟨j, rfl⟩

@[simp] theorem sqrt_two_add_values9_mem_recursiveValueSet_fourteen (i : Fin 33) :
    Real.sqrt 2 + values9 i ∈ recursiveValueSet 14 := by
  rw [recursiveValueSet]
  right
  refine ⟨⟨3, by decide⟩, Real.sqrt 2, ?_, values9 i, ?_, rfl⟩
  · rw [recursiveValueSet_four]
    simp
  · change values9 i ∈ recursiveValueSet 9
    rw [recursiveValueSet_nine]
    exact ⟨i, rfl⟩

set_option maxHeartbeats 1000000 in
theorem values14_mem_recursiveValueSet (i : Fin 455) :
    values14 i ∈ recursiveValueSet 14 := by
  fin_cases i
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (0 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (1 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (2 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (3 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (4 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (5 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (6 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (7 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (8 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (9 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (10 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (11 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (12 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (13 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (14 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (15 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (16 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (17 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (18 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (19 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (20 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (21 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (22 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (23 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (24 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (25 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (26 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (27 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (28 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (29 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (30 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (31 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (32 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (33 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (34 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (35 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (36 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (37 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (38 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (39 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (40 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (41 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (42 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (43 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (44 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (45 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (46 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (47 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (48 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (49 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (50 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (51 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (52 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (53 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (54 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (55 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (56 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (57 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (58 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (59 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (60 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (61 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (62 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (63 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (64 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (65 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (66 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (67 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (68 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (69 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (70 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (71 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (72 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (73 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (74 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (75 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (76 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (77 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (78 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (79 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (80 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (81 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (82 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (83 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (84 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (85 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (86 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (87 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (88 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (89 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (90 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (91 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (92 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (93 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (94 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (95 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (96 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (97 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (98 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (99 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (100 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (101 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (102 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (103 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (104 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (105 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (106 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (107 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (108 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (109 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (110 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (111 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (112 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (113 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (114 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (115 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (116 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (117 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (118 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (119 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (120 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (121 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (122 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (123 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (124 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (125 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (126 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (127 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (128 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (129 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (130 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (131 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (132 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (133 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (134 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (135 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (136 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (137 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (138 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (139 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (140 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (141 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (142 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (143 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (144 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (145 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (146 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (147 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (148 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (149 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (150 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (151 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (152 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (153 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (154 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (155 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (156 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (157 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (158 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (159 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (160 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (161 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (162 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (163 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (164 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (165 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (166 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (167 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (168 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (169 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (170 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (171 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (172 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (173 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (174 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (175 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (176 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (177 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (178 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (179 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (180 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (181 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (182 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (183 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (184 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (185 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (186 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (187 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (188 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (189 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (190 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (191 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (192 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (193 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (194 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (195 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (196 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (197 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (198 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (199 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (200 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (201 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (202 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (203 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (204 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (205 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (206 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (207 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (208 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (209 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (210 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (211 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (212 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (213 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (214 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (215 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (216 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (217 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (218 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (219 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (220 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (221 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (222 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (223 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (224 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (225 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (226 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (227 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (228 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (229 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (230 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (231 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (232 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (233 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (234 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (235 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (236 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (237 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (238 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (239 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (240 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (241 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (242 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (243 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (244 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (245 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (246 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (247 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (248 : Fin 264)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (249 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (1 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (2 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (3 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (4 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (5 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (250 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (6 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (7 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (8 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (251 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (9 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (10 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (11 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (252 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (12 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (253 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (13 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (14 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (15 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (16 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (17 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (254 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (18 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (19 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (20 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (21 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (255 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (22 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (23 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (24 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (25 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (26 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (256 : Fin 264)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (1 : Fin 8) (1 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (27 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (28 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (29 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (30 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (257 : Fin 264)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (1 : Fin 8) (2 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (31 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (32 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (33 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (258 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (34 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (35 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (1 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (36 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (37 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (38 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (2 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (39 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (259 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (40 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (41 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (42 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (43 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (260 : Fin 264)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (3 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (44 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (45 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (46 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (47 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (261 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (48 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (4 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (49 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (5 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (50 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (1 : Fin 8) (4 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (51 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (52 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (53 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (1 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (54 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (6 : Fin 20)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (2 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (55 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (56 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (57 : Fin 154)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (262 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (58 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (3 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (59 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (60 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (4 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (61 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (62 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (63 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (5 : Fin 33)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (7 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (64 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (6 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (65 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (66 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (7 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (67 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (68 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (69 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (70 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (8 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (71 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (72 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (9 : Fin 33)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (1 : Fin 8) (6 : Fin 13)
  next => exact sqrt_values13_mem_recursiveValueSet_fourteen (263 : Fin 264)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (73 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (10 : Fin 33)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (9 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (74 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (75 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (11 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (76 : Fin 154)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (10 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (77 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (78 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (79 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (4 : Fin 8) (1 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (80 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (81 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (1 : Fin 8) (7 : Fin 13)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (12 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (82 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (13 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (83 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (14 : Fin 33)
  next => exact values5_add_values8_mem_recursiveValueSet_fourteen (1 : Fin 5) (11 : Fin 20)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (84 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (85 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (15 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (86 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (87 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (88 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (89 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (90 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (91 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (92 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (4 : Fin 8) (4 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (93 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (16 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (94 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (95 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (96 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (97 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (98 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (17 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (99 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (100 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (101 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (102 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (103 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (104 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (18 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (105 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (106 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (4 : Fin 8) (6 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (107 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (108 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (109 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (110 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (111 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (112 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (113 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (114 : Fin 154)
  next => exact values6_add_values7_mem_recursiveValueSet_fourteen (4 : Fin 8) (7 : Fin 13)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (115 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (116 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (117 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (118 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (119 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (120 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (121 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (122 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (123 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (124 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (125 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (126 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (127 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (128 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (129 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (130 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (131 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (132 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (133 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (134 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (135 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (136 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (137 : Fin 154)
  next => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen (27 : Fin 33)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (138 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (139 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (140 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (141 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (142 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (143 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (144 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (145 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (146 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (147 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (148 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (149 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (150 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (151 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (152 : Fin 154)
  next => exact one_add_values12_mem_recursiveValueSet_fourteen (153 : Fin 154)
theorem values14_range_subset_recursiveValueSet_fourteen :
    Set.range values14 ⊆ recursiveValueSet 14 := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact values14_mem_recursiveValueSet i
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_values13_mem_range_values14 (i : Fin 264) :
    (Set.range values14) (Real.sqrt (values13 i)) := by
  fin_cases i
  next =>
    exact Exists.intro (0 : Fin 455) (by
      change Real.sqrt (values13 (0 : Fin 264)) = Real.sqrt (values13 (0 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (1 : Fin 455) (by
      change Real.sqrt (values13 (1 : Fin 264)) = Real.sqrt (values13 (1 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (2 : Fin 455) (by
      change Real.sqrt (values13 (2 : Fin 264)) = Real.sqrt (values13 (2 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (3 : Fin 455) (by
      change Real.sqrt (values13 (3 : Fin 264)) = Real.sqrt (values13 (3 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (4 : Fin 455) (by
      change Real.sqrt (values13 (4 : Fin 264)) = Real.sqrt (values13 (4 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (5 : Fin 455) (by
      change Real.sqrt (values13 (5 : Fin 264)) = Real.sqrt (values13 (5 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (6 : Fin 455) (by
      change Real.sqrt (values13 (6 : Fin 264)) = Real.sqrt (values13 (6 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (7 : Fin 455) (by
      change Real.sqrt (values13 (7 : Fin 264)) = Real.sqrt (values13 (7 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (8 : Fin 455) (by
      change Real.sqrt (values13 (8 : Fin 264)) = Real.sqrt (values13 (8 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (9 : Fin 455) (by
      change Real.sqrt (values13 (9 : Fin 264)) = Real.sqrt (values13 (9 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (10 : Fin 455) (by
      change Real.sqrt (values13 (10 : Fin 264)) = Real.sqrt (values13 (10 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (11 : Fin 455) (by
      change Real.sqrt (values13 (11 : Fin 264)) = Real.sqrt (values13 (11 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (12 : Fin 455) (by
      change Real.sqrt (values13 (12 : Fin 264)) = Real.sqrt (values13 (12 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (13 : Fin 455) (by
      change Real.sqrt (values13 (13 : Fin 264)) = Real.sqrt (values13 (13 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (14 : Fin 455) (by
      change Real.sqrt (values13 (14 : Fin 264)) = Real.sqrt (values13 (14 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (15 : Fin 455) (by
      change Real.sqrt (values13 (15 : Fin 264)) = Real.sqrt (values13 (15 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (16 : Fin 455) (by
      change Real.sqrt (values13 (16 : Fin 264)) = Real.sqrt (values13 (16 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (17 : Fin 455) (by
      change Real.sqrt (values13 (17 : Fin 264)) = Real.sqrt (values13 (17 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (18 : Fin 455) (by
      change Real.sqrt (values13 (18 : Fin 264)) = Real.sqrt (values13 (18 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (19 : Fin 455) (by
      change Real.sqrt (values13 (19 : Fin 264)) = Real.sqrt (values13 (19 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (20 : Fin 455) (by
      change Real.sqrt (values13 (20 : Fin 264)) = Real.sqrt (values13 (20 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (21 : Fin 455) (by
      change Real.sqrt (values13 (21 : Fin 264)) = Real.sqrt (values13 (21 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (22 : Fin 455) (by
      change Real.sqrt (values13 (22 : Fin 264)) = Real.sqrt (values13 (22 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (23 : Fin 455) (by
      change Real.sqrt (values13 (23 : Fin 264)) = Real.sqrt (values13 (23 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (24 : Fin 455) (by
      change Real.sqrt (values13 (24 : Fin 264)) = Real.sqrt (values13 (24 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (25 : Fin 455) (by
      change Real.sqrt (values13 (25 : Fin 264)) = Real.sqrt (values13 (25 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (26 : Fin 455) (by
      change Real.sqrt (values13 (26 : Fin 264)) = Real.sqrt (values13 (26 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (27 : Fin 455) (by
      change Real.sqrt (values13 (27 : Fin 264)) = Real.sqrt (values13 (27 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (28 : Fin 455) (by
      change Real.sqrt (values13 (28 : Fin 264)) = Real.sqrt (values13 (28 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (29 : Fin 455) (by
      change Real.sqrt (values13 (29 : Fin 264)) = Real.sqrt (values13 (29 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (30 : Fin 455) (by
      change Real.sqrt (values13 (30 : Fin 264)) = Real.sqrt (values13 (30 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (31 : Fin 455) (by
      change Real.sqrt (values13 (31 : Fin 264)) = Real.sqrt (values13 (31 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (32 : Fin 455) (by
      change Real.sqrt (values13 (32 : Fin 264)) = Real.sqrt (values13 (32 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (33 : Fin 455) (by
      change Real.sqrt (values13 (33 : Fin 264)) = Real.sqrt (values13 (33 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (34 : Fin 455) (by
      change Real.sqrt (values13 (34 : Fin 264)) = Real.sqrt (values13 (34 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (35 : Fin 455) (by
      change Real.sqrt (values13 (35 : Fin 264)) = Real.sqrt (values13 (35 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (36 : Fin 455) (by
      change Real.sqrt (values13 (36 : Fin 264)) = Real.sqrt (values13 (36 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (37 : Fin 455) (by
      change Real.sqrt (values13 (37 : Fin 264)) = Real.sqrt (values13 (37 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (38 : Fin 455) (by
      change Real.sqrt (values13 (38 : Fin 264)) = Real.sqrt (values13 (38 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (39 : Fin 455) (by
      change Real.sqrt (values13 (39 : Fin 264)) = Real.sqrt (values13 (39 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (40 : Fin 455) (by
      change Real.sqrt (values13 (40 : Fin 264)) = Real.sqrt (values13 (40 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (41 : Fin 455) (by
      change Real.sqrt (values13 (41 : Fin 264)) = Real.sqrt (values13 (41 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (42 : Fin 455) (by
      change Real.sqrt (values13 (42 : Fin 264)) = Real.sqrt (values13 (42 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (43 : Fin 455) (by
      change Real.sqrt (values13 (43 : Fin 264)) = Real.sqrt (values13 (43 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (44 : Fin 455) (by
      change Real.sqrt (values13 (44 : Fin 264)) = Real.sqrt (values13 (44 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (45 : Fin 455) (by
      change Real.sqrt (values13 (45 : Fin 264)) = Real.sqrt (values13 (45 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (46 : Fin 455) (by
      change Real.sqrt (values13 (46 : Fin 264)) = Real.sqrt (values13 (46 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (47 : Fin 455) (by
      change Real.sqrt (values13 (47 : Fin 264)) = Real.sqrt (values13 (47 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (48 : Fin 455) (by
      change Real.sqrt (values13 (48 : Fin 264)) = Real.sqrt (values13 (48 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (49 : Fin 455) (by
      change Real.sqrt (values13 (49 : Fin 264)) = Real.sqrt (values13 (49 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (50 : Fin 455) (by
      change Real.sqrt (values13 (50 : Fin 264)) = Real.sqrt (values13 (50 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (51 : Fin 455) (by
      change Real.sqrt (values13 (51 : Fin 264)) = Real.sqrt (values13 (51 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (52 : Fin 455) (by
      change Real.sqrt (values13 (52 : Fin 264)) = Real.sqrt (values13 (52 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (53 : Fin 455) (by
      change Real.sqrt (values13 (53 : Fin 264)) = Real.sqrt (values13 (53 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (54 : Fin 455) (by
      change Real.sqrt (values13 (54 : Fin 264)) = Real.sqrt (values13 (54 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (55 : Fin 455) (by
      change Real.sqrt (values13 (55 : Fin 264)) = Real.sqrt (values13 (55 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (56 : Fin 455) (by
      change Real.sqrt (values13 (56 : Fin 264)) = Real.sqrt (values13 (56 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (57 : Fin 455) (by
      change Real.sqrt (values13 (57 : Fin 264)) = Real.sqrt (values13 (57 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (58 : Fin 455) (by
      change Real.sqrt (values13 (58 : Fin 264)) = Real.sqrt (values13 (58 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (59 : Fin 455) (by
      change Real.sqrt (values13 (59 : Fin 264)) = Real.sqrt (values13 (59 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (60 : Fin 455) (by
      change Real.sqrt (values13 (60 : Fin 264)) = Real.sqrt (values13 (60 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (61 : Fin 455) (by
      change Real.sqrt (values13 (61 : Fin 264)) = Real.sqrt (values13 (61 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (62 : Fin 455) (by
      change Real.sqrt (values13 (62 : Fin 264)) = Real.sqrt (values13 (62 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (63 : Fin 455) (by
      change Real.sqrt (values13 (63 : Fin 264)) = Real.sqrt (values13 (63 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (64 : Fin 455) (by
      change Real.sqrt (values13 (64 : Fin 264)) = Real.sqrt (values13 (64 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (65 : Fin 455) (by
      change Real.sqrt (values13 (65 : Fin 264)) = Real.sqrt (values13 (65 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (66 : Fin 455) (by
      change Real.sqrt (values13 (66 : Fin 264)) = Real.sqrt (values13 (66 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (67 : Fin 455) (by
      change Real.sqrt (values13 (67 : Fin 264)) = Real.sqrt (values13 (67 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (68 : Fin 455) (by
      change Real.sqrt (values13 (68 : Fin 264)) = Real.sqrt (values13 (68 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (69 : Fin 455) (by
      change Real.sqrt (values13 (69 : Fin 264)) = Real.sqrt (values13 (69 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (70 : Fin 455) (by
      change Real.sqrt (values13 (70 : Fin 264)) = Real.sqrt (values13 (70 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (71 : Fin 455) (by
      change Real.sqrt (values13 (71 : Fin 264)) = Real.sqrt (values13 (71 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (72 : Fin 455) (by
      change Real.sqrt (values13 (72 : Fin 264)) = Real.sqrt (values13 (72 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (73 : Fin 455) (by
      change Real.sqrt (values13 (73 : Fin 264)) = Real.sqrt (values13 (73 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (74 : Fin 455) (by
      change Real.sqrt (values13 (74 : Fin 264)) = Real.sqrt (values13 (74 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (75 : Fin 455) (by
      change Real.sqrt (values13 (75 : Fin 264)) = Real.sqrt (values13 (75 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (76 : Fin 455) (by
      change Real.sqrt (values13 (76 : Fin 264)) = Real.sqrt (values13 (76 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (77 : Fin 455) (by
      change Real.sqrt (values13 (77 : Fin 264)) = Real.sqrt (values13 (77 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (78 : Fin 455) (by
      change Real.sqrt (values13 (78 : Fin 264)) = Real.sqrt (values13 (78 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (79 : Fin 455) (by
      change Real.sqrt (values13 (79 : Fin 264)) = Real.sqrt (values13 (79 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (80 : Fin 455) (by
      change Real.sqrt (values13 (80 : Fin 264)) = Real.sqrt (values13 (80 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (81 : Fin 455) (by
      change Real.sqrt (values13 (81 : Fin 264)) = Real.sqrt (values13 (81 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (82 : Fin 455) (by
      change Real.sqrt (values13 (82 : Fin 264)) = Real.sqrt (values13 (82 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (83 : Fin 455) (by
      change Real.sqrt (values13 (83 : Fin 264)) = Real.sqrt (values13 (83 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (84 : Fin 455) (by
      change Real.sqrt (values13 (84 : Fin 264)) = Real.sqrt (values13 (84 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (85 : Fin 455) (by
      change Real.sqrt (values13 (85 : Fin 264)) = Real.sqrt (values13 (85 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (86 : Fin 455) (by
      change Real.sqrt (values13 (86 : Fin 264)) = Real.sqrt (values13 (86 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (87 : Fin 455) (by
      change Real.sqrt (values13 (87 : Fin 264)) = Real.sqrt (values13 (87 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (88 : Fin 455) (by
      change Real.sqrt (values13 (88 : Fin 264)) = Real.sqrt (values13 (88 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (89 : Fin 455) (by
      change Real.sqrt (values13 (89 : Fin 264)) = Real.sqrt (values13 (89 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (90 : Fin 455) (by
      change Real.sqrt (values13 (90 : Fin 264)) = Real.sqrt (values13 (90 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (91 : Fin 455) (by
      change Real.sqrt (values13 (91 : Fin 264)) = Real.sqrt (values13 (91 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (92 : Fin 455) (by
      change Real.sqrt (values13 (92 : Fin 264)) = Real.sqrt (values13 (92 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (93 : Fin 455) (by
      change Real.sqrt (values13 (93 : Fin 264)) = Real.sqrt (values13 (93 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (94 : Fin 455) (by
      change Real.sqrt (values13 (94 : Fin 264)) = Real.sqrt (values13 (94 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (95 : Fin 455) (by
      change Real.sqrt (values13 (95 : Fin 264)) = Real.sqrt (values13 (95 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (96 : Fin 455) (by
      change Real.sqrt (values13 (96 : Fin 264)) = Real.sqrt (values13 (96 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (97 : Fin 455) (by
      change Real.sqrt (values13 (97 : Fin 264)) = Real.sqrt (values13 (97 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (98 : Fin 455) (by
      change Real.sqrt (values13 (98 : Fin 264)) = Real.sqrt (values13 (98 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (99 : Fin 455) (by
      change Real.sqrt (values13 (99 : Fin 264)) = Real.sqrt (values13 (99 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (100 : Fin 455) (by
      change Real.sqrt (values13 (100 : Fin 264)) = Real.sqrt (values13 (100 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (101 : Fin 455) (by
      change Real.sqrt (values13 (101 : Fin 264)) = Real.sqrt (values13 (101 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (102 : Fin 455) (by
      change Real.sqrt (values13 (102 : Fin 264)) = Real.sqrt (values13 (102 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (103 : Fin 455) (by
      change Real.sqrt (values13 (103 : Fin 264)) = Real.sqrt (values13 (103 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (104 : Fin 455) (by
      change Real.sqrt (values13 (104 : Fin 264)) = Real.sqrt (values13 (104 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (105 : Fin 455) (by
      change Real.sqrt (values13 (105 : Fin 264)) = Real.sqrt (values13 (105 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (106 : Fin 455) (by
      change Real.sqrt (values13 (106 : Fin 264)) = Real.sqrt (values13 (106 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (107 : Fin 455) (by
      change Real.sqrt (values13 (107 : Fin 264)) = Real.sqrt (values13 (107 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (108 : Fin 455) (by
      change Real.sqrt (values13 (108 : Fin 264)) = Real.sqrt (values13 (108 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (109 : Fin 455) (by
      change Real.sqrt (values13 (109 : Fin 264)) = Real.sqrt (values13 (109 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (110 : Fin 455) (by
      change Real.sqrt (values13 (110 : Fin 264)) = Real.sqrt (values13 (110 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (111 : Fin 455) (by
      change Real.sqrt (values13 (111 : Fin 264)) = Real.sqrt (values13 (111 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (112 : Fin 455) (by
      change Real.sqrt (values13 (112 : Fin 264)) = Real.sqrt (values13 (112 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (113 : Fin 455) (by
      change Real.sqrt (values13 (113 : Fin 264)) = Real.sqrt (values13 (113 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (114 : Fin 455) (by
      change Real.sqrt (values13 (114 : Fin 264)) = Real.sqrt (values13 (114 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (115 : Fin 455) (by
      change Real.sqrt (values13 (115 : Fin 264)) = Real.sqrt (values13 (115 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (116 : Fin 455) (by
      change Real.sqrt (values13 (116 : Fin 264)) = Real.sqrt (values13 (116 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (117 : Fin 455) (by
      change Real.sqrt (values13 (117 : Fin 264)) = Real.sqrt (values13 (117 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (118 : Fin 455) (by
      change Real.sqrt (values13 (118 : Fin 264)) = Real.sqrt (values13 (118 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (119 : Fin 455) (by
      change Real.sqrt (values13 (119 : Fin 264)) = Real.sqrt (values13 (119 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (120 : Fin 455) (by
      change Real.sqrt (values13 (120 : Fin 264)) = Real.sqrt (values13 (120 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (121 : Fin 455) (by
      change Real.sqrt (values13 (121 : Fin 264)) = Real.sqrt (values13 (121 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (122 : Fin 455) (by
      change Real.sqrt (values13 (122 : Fin 264)) = Real.sqrt (values13 (122 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (123 : Fin 455) (by
      change Real.sqrt (values13 (123 : Fin 264)) = Real.sqrt (values13 (123 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (124 : Fin 455) (by
      change Real.sqrt (values13 (124 : Fin 264)) = Real.sqrt (values13 (124 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (125 : Fin 455) (by
      change Real.sqrt (values13 (125 : Fin 264)) = Real.sqrt (values13 (125 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (126 : Fin 455) (by
      change Real.sqrt (values13 (126 : Fin 264)) = Real.sqrt (values13 (126 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (127 : Fin 455) (by
      change Real.sqrt (values13 (127 : Fin 264)) = Real.sqrt (values13 (127 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (128 : Fin 455) (by
      change Real.sqrt (values13 (128 : Fin 264)) = Real.sqrt (values13 (128 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (129 : Fin 455) (by
      change Real.sqrt (values13 (129 : Fin 264)) = Real.sqrt (values13 (129 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (130 : Fin 455) (by
      change Real.sqrt (values13 (130 : Fin 264)) = Real.sqrt (values13 (130 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (131 : Fin 455) (by
      change Real.sqrt (values13 (131 : Fin 264)) = Real.sqrt (values13 (131 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (132 : Fin 455) (by
      change Real.sqrt (values13 (132 : Fin 264)) = Real.sqrt (values13 (132 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (133 : Fin 455) (by
      change Real.sqrt (values13 (133 : Fin 264)) = Real.sqrt (values13 (133 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (134 : Fin 455) (by
      change Real.sqrt (values13 (134 : Fin 264)) = Real.sqrt (values13 (134 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (135 : Fin 455) (by
      change Real.sqrt (values13 (135 : Fin 264)) = Real.sqrt (values13 (135 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (136 : Fin 455) (by
      change Real.sqrt (values13 (136 : Fin 264)) = Real.sqrt (values13 (136 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (137 : Fin 455) (by
      change Real.sqrt (values13 (137 : Fin 264)) = Real.sqrt (values13 (137 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (138 : Fin 455) (by
      change Real.sqrt (values13 (138 : Fin 264)) = Real.sqrt (values13 (138 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (139 : Fin 455) (by
      change Real.sqrt (values13 (139 : Fin 264)) = Real.sqrt (values13 (139 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (140 : Fin 455) (by
      change Real.sqrt (values13 (140 : Fin 264)) = Real.sqrt (values13 (140 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (141 : Fin 455) (by
      change Real.sqrt (values13 (141 : Fin 264)) = Real.sqrt (values13 (141 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (142 : Fin 455) (by
      change Real.sqrt (values13 (142 : Fin 264)) = Real.sqrt (values13 (142 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (143 : Fin 455) (by
      change Real.sqrt (values13 (143 : Fin 264)) = Real.sqrt (values13 (143 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (144 : Fin 455) (by
      change Real.sqrt (values13 (144 : Fin 264)) = Real.sqrt (values13 (144 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (145 : Fin 455) (by
      change Real.sqrt (values13 (145 : Fin 264)) = Real.sqrt (values13 (145 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (146 : Fin 455) (by
      change Real.sqrt (values13 (146 : Fin 264)) = Real.sqrt (values13 (146 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (147 : Fin 455) (by
      change Real.sqrt (values13 (147 : Fin 264)) = Real.sqrt (values13 (147 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (148 : Fin 455) (by
      change Real.sqrt (values13 (148 : Fin 264)) = Real.sqrt (values13 (148 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (149 : Fin 455) (by
      change Real.sqrt (values13 (149 : Fin 264)) = Real.sqrt (values13 (149 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (150 : Fin 455) (by
      change Real.sqrt (values13 (150 : Fin 264)) = Real.sqrt (values13 (150 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (151 : Fin 455) (by
      change Real.sqrt (values13 (151 : Fin 264)) = Real.sqrt (values13 (151 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (152 : Fin 455) (by
      change Real.sqrt (values13 (152 : Fin 264)) = Real.sqrt (values13 (152 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (153 : Fin 455) (by
      change Real.sqrt (values13 (153 : Fin 264)) = Real.sqrt (values13 (153 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (154 : Fin 455) (by
      change Real.sqrt (values13 (154 : Fin 264)) = Real.sqrt (values13 (154 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (155 : Fin 455) (by
      change Real.sqrt (values13 (155 : Fin 264)) = Real.sqrt (values13 (155 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (156 : Fin 455) (by
      change Real.sqrt (values13 (156 : Fin 264)) = Real.sqrt (values13 (156 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (157 : Fin 455) (by
      change Real.sqrt (values13 (157 : Fin 264)) = Real.sqrt (values13 (157 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (158 : Fin 455) (by
      change Real.sqrt (values13 (158 : Fin 264)) = Real.sqrt (values13 (158 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (159 : Fin 455) (by
      change Real.sqrt (values13 (159 : Fin 264)) = Real.sqrt (values13 (159 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (160 : Fin 455) (by
      change Real.sqrt (values13 (160 : Fin 264)) = Real.sqrt (values13 (160 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (161 : Fin 455) (by
      change Real.sqrt (values13 (161 : Fin 264)) = Real.sqrt (values13 (161 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (162 : Fin 455) (by
      change Real.sqrt (values13 (162 : Fin 264)) = Real.sqrt (values13 (162 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (163 : Fin 455) (by
      change Real.sqrt (values13 (163 : Fin 264)) = Real.sqrt (values13 (163 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (164 : Fin 455) (by
      change Real.sqrt (values13 (164 : Fin 264)) = Real.sqrt (values13 (164 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (165 : Fin 455) (by
      change Real.sqrt (values13 (165 : Fin 264)) = Real.sqrt (values13 (165 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (166 : Fin 455) (by
      change Real.sqrt (values13 (166 : Fin 264)) = Real.sqrt (values13 (166 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (167 : Fin 455) (by
      change Real.sqrt (values13 (167 : Fin 264)) = Real.sqrt (values13 (167 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (168 : Fin 455) (by
      change Real.sqrt (values13 (168 : Fin 264)) = Real.sqrt (values13 (168 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (169 : Fin 455) (by
      change Real.sqrt (values13 (169 : Fin 264)) = Real.sqrt (values13 (169 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (170 : Fin 455) (by
      change Real.sqrt (values13 (170 : Fin 264)) = Real.sqrt (values13 (170 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (171 : Fin 455) (by
      change Real.sqrt (values13 (171 : Fin 264)) = Real.sqrt (values13 (171 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (172 : Fin 455) (by
      change Real.sqrt (values13 (172 : Fin 264)) = Real.sqrt (values13 (172 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (173 : Fin 455) (by
      change Real.sqrt (values13 (173 : Fin 264)) = Real.sqrt (values13 (173 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (174 : Fin 455) (by
      change Real.sqrt (values13 (174 : Fin 264)) = Real.sqrt (values13 (174 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (175 : Fin 455) (by
      change Real.sqrt (values13 (175 : Fin 264)) = Real.sqrt (values13 (175 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (176 : Fin 455) (by
      change Real.sqrt (values13 (176 : Fin 264)) = Real.sqrt (values13 (176 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (177 : Fin 455) (by
      change Real.sqrt (values13 (177 : Fin 264)) = Real.sqrt (values13 (177 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (178 : Fin 455) (by
      change Real.sqrt (values13 (178 : Fin 264)) = Real.sqrt (values13 (178 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (179 : Fin 455) (by
      change Real.sqrt (values13 (179 : Fin 264)) = Real.sqrt (values13 (179 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (180 : Fin 455) (by
      change Real.sqrt (values13 (180 : Fin 264)) = Real.sqrt (values13 (180 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (181 : Fin 455) (by
      change Real.sqrt (values13 (181 : Fin 264)) = Real.sqrt (values13 (181 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (182 : Fin 455) (by
      change Real.sqrt (values13 (182 : Fin 264)) = Real.sqrt (values13 (182 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (183 : Fin 455) (by
      change Real.sqrt (values13 (183 : Fin 264)) = Real.sqrt (values13 (183 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (184 : Fin 455) (by
      change Real.sqrt (values13 (184 : Fin 264)) = Real.sqrt (values13 (184 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (185 : Fin 455) (by
      change Real.sqrt (values13 (185 : Fin 264)) = Real.sqrt (values13 (185 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (186 : Fin 455) (by
      change Real.sqrt (values13 (186 : Fin 264)) = Real.sqrt (values13 (186 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (187 : Fin 455) (by
      change Real.sqrt (values13 (187 : Fin 264)) = Real.sqrt (values13 (187 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (188 : Fin 455) (by
      change Real.sqrt (values13 (188 : Fin 264)) = Real.sqrt (values13 (188 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (189 : Fin 455) (by
      change Real.sqrt (values13 (189 : Fin 264)) = Real.sqrt (values13 (189 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (190 : Fin 455) (by
      change Real.sqrt (values13 (190 : Fin 264)) = Real.sqrt (values13 (190 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (191 : Fin 455) (by
      change Real.sqrt (values13 (191 : Fin 264)) = Real.sqrt (values13 (191 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (192 : Fin 455) (by
      change Real.sqrt (values13 (192 : Fin 264)) = Real.sqrt (values13 (192 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (193 : Fin 455) (by
      change Real.sqrt (values13 (193 : Fin 264)) = Real.sqrt (values13 (193 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (194 : Fin 455) (by
      change Real.sqrt (values13 (194 : Fin 264)) = Real.sqrt (values13 (194 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (195 : Fin 455) (by
      change Real.sqrt (values13 (195 : Fin 264)) = Real.sqrt (values13 (195 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (196 : Fin 455) (by
      change Real.sqrt (values13 (196 : Fin 264)) = Real.sqrt (values13 (196 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (197 : Fin 455) (by
      change Real.sqrt (values13 (197 : Fin 264)) = Real.sqrt (values13 (197 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (198 : Fin 455) (by
      change Real.sqrt (values13 (198 : Fin 264)) = Real.sqrt (values13 (198 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (199 : Fin 455) (by
      change Real.sqrt (values13 (199 : Fin 264)) = Real.sqrt (values13 (199 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (200 : Fin 455) (by
      change Real.sqrt (values13 (200 : Fin 264)) = Real.sqrt (values13 (200 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (201 : Fin 455) (by
      change Real.sqrt (values13 (201 : Fin 264)) = Real.sqrt (values13 (201 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (202 : Fin 455) (by
      change Real.sqrt (values13 (202 : Fin 264)) = Real.sqrt (values13 (202 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (203 : Fin 455) (by
      change Real.sqrt (values13 (203 : Fin 264)) = Real.sqrt (values13 (203 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (204 : Fin 455) (by
      change Real.sqrt (values13 (204 : Fin 264)) = Real.sqrt (values13 (204 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (205 : Fin 455) (by
      change Real.sqrt (values13 (205 : Fin 264)) = Real.sqrt (values13 (205 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (206 : Fin 455) (by
      change Real.sqrt (values13 (206 : Fin 264)) = Real.sqrt (values13 (206 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (207 : Fin 455) (by
      change Real.sqrt (values13 (207 : Fin 264)) = Real.sqrt (values13 (207 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (208 : Fin 455) (by
      change Real.sqrt (values13 (208 : Fin 264)) = Real.sqrt (values13 (208 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (209 : Fin 455) (by
      change Real.sqrt (values13 (209 : Fin 264)) = Real.sqrt (values13 (209 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (210 : Fin 455) (by
      change Real.sqrt (values13 (210 : Fin 264)) = Real.sqrt (values13 (210 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (211 : Fin 455) (by
      change Real.sqrt (values13 (211 : Fin 264)) = Real.sqrt (values13 (211 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (212 : Fin 455) (by
      change Real.sqrt (values13 (212 : Fin 264)) = Real.sqrt (values13 (212 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (213 : Fin 455) (by
      change Real.sqrt (values13 (213 : Fin 264)) = Real.sqrt (values13 (213 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (214 : Fin 455) (by
      change Real.sqrt (values13 (214 : Fin 264)) = Real.sqrt (values13 (214 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (215 : Fin 455) (by
      change Real.sqrt (values13 (215 : Fin 264)) = Real.sqrt (values13 (215 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (216 : Fin 455) (by
      change Real.sqrt (values13 (216 : Fin 264)) = Real.sqrt (values13 (216 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (217 : Fin 455) (by
      change Real.sqrt (values13 (217 : Fin 264)) = Real.sqrt (values13 (217 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (218 : Fin 455) (by
      change Real.sqrt (values13 (218 : Fin 264)) = Real.sqrt (values13 (218 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (219 : Fin 455) (by
      change Real.sqrt (values13 (219 : Fin 264)) = Real.sqrt (values13 (219 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (220 : Fin 455) (by
      change Real.sqrt (values13 (220 : Fin 264)) = Real.sqrt (values13 (220 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (221 : Fin 455) (by
      change Real.sqrt (values13 (221 : Fin 264)) = Real.sqrt (values13 (221 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (222 : Fin 455) (by
      change Real.sqrt (values13 (222 : Fin 264)) = Real.sqrt (values13 (222 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (223 : Fin 455) (by
      change Real.sqrt (values13 (223 : Fin 264)) = Real.sqrt (values13 (223 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (224 : Fin 455) (by
      change Real.sqrt (values13 (224 : Fin 264)) = Real.sqrt (values13 (224 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (225 : Fin 455) (by
      change Real.sqrt (values13 (225 : Fin 264)) = Real.sqrt (values13 (225 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (226 : Fin 455) (by
      change Real.sqrt (values13 (226 : Fin 264)) = Real.sqrt (values13 (226 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (227 : Fin 455) (by
      change Real.sqrt (values13 (227 : Fin 264)) = Real.sqrt (values13 (227 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (228 : Fin 455) (by
      change Real.sqrt (values13 (228 : Fin 264)) = Real.sqrt (values13 (228 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (229 : Fin 455) (by
      change Real.sqrt (values13 (229 : Fin 264)) = Real.sqrt (values13 (229 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (230 : Fin 455) (by
      change Real.sqrt (values13 (230 : Fin 264)) = Real.sqrt (values13 (230 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (231 : Fin 455) (by
      change Real.sqrt (values13 (231 : Fin 264)) = Real.sqrt (values13 (231 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (232 : Fin 455) (by
      change Real.sqrt (values13 (232 : Fin 264)) = Real.sqrt (values13 (232 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (233 : Fin 455) (by
      change Real.sqrt (values13 (233 : Fin 264)) = Real.sqrt (values13 (233 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (234 : Fin 455) (by
      change Real.sqrt (values13 (234 : Fin 264)) = Real.sqrt (values13 (234 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (235 : Fin 455) (by
      change Real.sqrt (values13 (235 : Fin 264)) = Real.sqrt (values13 (235 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (236 : Fin 455) (by
      change Real.sqrt (values13 (236 : Fin 264)) = Real.sqrt (values13 (236 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (237 : Fin 455) (by
      change Real.sqrt (values13 (237 : Fin 264)) = Real.sqrt (values13 (237 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (238 : Fin 455) (by
      change Real.sqrt (values13 (238 : Fin 264)) = Real.sqrt (values13 (238 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (239 : Fin 455) (by
      change Real.sqrt (values13 (239 : Fin 264)) = Real.sqrt (values13 (239 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (240 : Fin 455) (by
      change Real.sqrt (values13 (240 : Fin 264)) = Real.sqrt (values13 (240 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (241 : Fin 455) (by
      change Real.sqrt (values13 (241 : Fin 264)) = Real.sqrt (values13 (241 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (242 : Fin 455) (by
      change Real.sqrt (values13 (242 : Fin 264)) = Real.sqrt (values13 (242 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (243 : Fin 455) (by
      change Real.sqrt (values13 (243 : Fin 264)) = Real.sqrt (values13 (243 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (244 : Fin 455) (by
      change Real.sqrt (values13 (244 : Fin 264)) = Real.sqrt (values13 (244 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (245 : Fin 455) (by
      change Real.sqrt (values13 (245 : Fin 264)) = Real.sqrt (values13 (245 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (246 : Fin 455) (by
      change Real.sqrt (values13 (246 : Fin 264)) = Real.sqrt (values13 (246 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (247 : Fin 455) (by
      change Real.sqrt (values13 (247 : Fin 264)) = Real.sqrt (values13 (247 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (248 : Fin 455) (by
      change Real.sqrt (values13 (248 : Fin 264)) = Real.sqrt (values13 (248 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = Real.sqrt (values13 (249 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (255 : Fin 455) (by
      change Real.sqrt (values13 (250 : Fin 264)) = Real.sqrt (values13 (250 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (259 : Fin 455) (by
      change Real.sqrt (values13 (251 : Fin 264)) = Real.sqrt (values13 (251 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (263 : Fin 455) (by
      change Real.sqrt (values13 (252 : Fin 264)) = Real.sqrt (values13 (252 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (265 : Fin 455) (by
      change Real.sqrt (values13 (253 : Fin 264)) = Real.sqrt (values13 (253 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (271 : Fin 455) (by
      change Real.sqrt (values13 (254 : Fin 264)) = Real.sqrt (values13 (254 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (276 : Fin 455) (by
      change Real.sqrt (values13 (255 : Fin 264)) = Real.sqrt (values13 (255 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (282 : Fin 455) (by
      change Real.sqrt (values13 (256 : Fin 264)) = Real.sqrt (values13 (256 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (288 : Fin 455) (by
      change Real.sqrt (values13 (257 : Fin 264)) = Real.sqrt (values13 (257 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (293 : Fin 455) (by
      change Real.sqrt (values13 (258 : Fin 264)) = Real.sqrt (values13 (258 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (302 : Fin 455) (by
      change Real.sqrt (values13 (259 : Fin 264)) = Real.sqrt (values13 (259 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (307 : Fin 455) (by
      change Real.sqrt (values13 (260 : Fin 264)) = Real.sqrt (values13 (260 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (313 : Fin 455) (by
      change Real.sqrt (values13 (261 : Fin 264)) = Real.sqrt (values13 (261 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (330 : Fin 455) (by
      change Real.sqrt (values13 (262 : Fin 264)) = Real.sqrt (values13 (262 : Fin 264))
      rfl
    )
  next =>
    exact Exists.intro (355 : Fin 455) (by
      change Real.sqrt (values13 (263 : Fin 264)) = Real.sqrt (values13 (263 : Fin 264))
      rfl
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values12_mem_range_values14 (i : Fin 154) :
    (Set.range values14) (1 + values12 i) := by
  fin_cases i
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = 1 + values12 (0 : Fin 154)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (250 : Fin 455) (by
      change 1 + values12 (1 : Fin 154) = 1 + values12 (1 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (251 : Fin 455) (by
      change 1 + values12 (2 : Fin 154) = 1 + values12 (2 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (252 : Fin 455) (by
      change 1 + values12 (3 : Fin 154) = 1 + values12 (3 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (253 : Fin 455) (by
      change 1 + values12 (4 : Fin 154) = 1 + values12 (4 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (254 : Fin 455) (by
      change 1 + values12 (5 : Fin 154) = 1 + values12 (5 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (256 : Fin 455) (by
      change 1 + values12 (6 : Fin 154) = 1 + values12 (6 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (257 : Fin 455) (by
      change 1 + values12 (7 : Fin 154) = 1 + values12 (7 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (258 : Fin 455) (by
      change 1 + values12 (8 : Fin 154) = 1 + values12 (8 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (260 : Fin 455) (by
      change 1 + values12 (9 : Fin 154) = 1 + values12 (9 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (261 : Fin 455) (by
      change 1 + values12 (10 : Fin 154) = 1 + values12 (10 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (262 : Fin 455) (by
      change 1 + values12 (11 : Fin 154) = 1 + values12 (11 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = 1 + values12 (12 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (266 : Fin 455) (by
      change 1 + values12 (13 : Fin 154) = 1 + values12 (13 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (267 : Fin 455) (by
      change 1 + values12 (14 : Fin 154) = 1 + values12 (14 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (268 : Fin 455) (by
      change 1 + values12 (15 : Fin 154) = 1 + values12 (15 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (269 : Fin 455) (by
      change 1 + values12 (16 : Fin 154) = 1 + values12 (16 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (270 : Fin 455) (by
      change 1 + values12 (17 : Fin 154) = 1 + values12 (17 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (272 : Fin 455) (by
      change 1 + values12 (18 : Fin 154) = 1 + values12 (18 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = 1 + values12 (19 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (274 : Fin 455) (by
      change 1 + values12 (20 : Fin 154) = 1 + values12 (20 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (275 : Fin 455) (by
      change 1 + values12 (21 : Fin 154) = 1 + values12 (21 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (277 : Fin 455) (by
      change 1 + values12 (22 : Fin 154) = 1 + values12 (22 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (278 : Fin 455) (by
      change 1 + values12 (23 : Fin 154) = 1 + values12 (23 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (279 : Fin 455) (by
      change 1 + values12 (24 : Fin 154) = 1 + values12 (24 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (280 : Fin 455) (by
      change 1 + values12 (25 : Fin 154) = 1 + values12 (25 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (281 : Fin 455) (by
      change 1 + values12 (26 : Fin 154) = 1 + values12 (26 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (284 : Fin 455) (by
      change 1 + values12 (27 : Fin 154) = 1 + values12 (27 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (285 : Fin 455) (by
      change 1 + values12 (28 : Fin 154) = 1 + values12 (28 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (286 : Fin 455) (by
      change 1 + values12 (29 : Fin 154) = 1 + values12 (29 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (287 : Fin 455) (by
      change 1 + values12 (30 : Fin 154) = 1 + values12 (30 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = 1 + values12 (31 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (291 : Fin 455) (by
      change 1 + values12 (32 : Fin 154) = 1 + values12 (32 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (292 : Fin 455) (by
      change 1 + values12 (33 : Fin 154) = 1 + values12 (33 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (294 : Fin 455) (by
      change 1 + values12 (34 : Fin 154) = 1 + values12 (34 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (295 : Fin 455) (by
      change 1 + values12 (35 : Fin 154) = 1 + values12 (35 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (297 : Fin 455) (by
      change 1 + values12 (36 : Fin 154) = 1 + values12 (36 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (298 : Fin 455) (by
      change 1 + values12 (37 : Fin 154) = 1 + values12 (37 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (299 : Fin 455) (by
      change 1 + values12 (38 : Fin 154) = 1 + values12 (38 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (301 : Fin 455) (by
      change 1 + values12 (39 : Fin 154) = 1 + values12 (39 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (303 : Fin 455) (by
      change 1 + values12 (40 : Fin 154) = 1 + values12 (40 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (304 : Fin 455) (by
      change 1 + values12 (41 : Fin 154) = 1 + values12 (41 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (305 : Fin 455) (by
      change 1 + values12 (42 : Fin 154) = 1 + values12 (42 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (306 : Fin 455) (by
      change 1 + values12 (43 : Fin 154) = 1 + values12 (43 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (309 : Fin 455) (by
      change 1 + values12 (44 : Fin 154) = 1 + values12 (44 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (310 : Fin 455) (by
      change 1 + values12 (45 : Fin 154) = 1 + values12 (45 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = 1 + values12 (46 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (312 : Fin 455) (by
      change 1 + values12 (47 : Fin 154) = 1 + values12 (47 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (314 : Fin 455) (by
      change 1 + values12 (48 : Fin 154) = 1 + values12 (48 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (316 : Fin 455) (by
      change 1 + values12 (49 : Fin 154) = 1 + values12 (49 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (318 : Fin 455) (by
      change 1 + values12 (50 : Fin 154) = 1 + values12 (50 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = 1 + values12 (51 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (321 : Fin 455) (by
      change 1 + values12 (52 : Fin 154) = 1 + values12 (52 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (322 : Fin 455) (by
      change 1 + values12 (53 : Fin 154) = 1 + values12 (53 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (324 : Fin 455) (by
      change 1 + values12 (54 : Fin 154) = 1 + values12 (54 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (327 : Fin 455) (by
      change 1 + values12 (55 : Fin 154) = 1 + values12 (55 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (328 : Fin 455) (by
      change 1 + values12 (56 : Fin 154) = 1 + values12 (56 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (329 : Fin 455) (by
      change 1 + values12 (57 : Fin 154) = 1 + values12 (57 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (331 : Fin 455) (by
      change 1 + values12 (58 : Fin 154) = 1 + values12 (58 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (333 : Fin 455) (by
      change 1 + values12 (59 : Fin 154) = 1 + values12 (59 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (334 : Fin 455) (by
      change 1 + values12 (60 : Fin 154) = 1 + values12 (60 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (336 : Fin 455) (by
      change 1 + values12 (61 : Fin 154) = 1 + values12 (61 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (337 : Fin 455) (by
      change 1 + values12 (62 : Fin 154) = 1 + values12 (62 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (338 : Fin 455) (by
      change 1 + values12 (63 : Fin 154) = 1 + values12 (63 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (341 : Fin 455) (by
      change 1 + values12 (64 : Fin 154) = 1 + values12 (64 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (343 : Fin 455) (by
      change 1 + values12 (65 : Fin 154) = 1 + values12 (65 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = 1 + values12 (66 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (346 : Fin 455) (by
      change 1 + values12 (67 : Fin 154) = 1 + values12 (67 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (347 : Fin 455) (by
      change 1 + values12 (68 : Fin 154) = 1 + values12 (68 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (348 : Fin 455) (by
      change 1 + values12 (69 : Fin 154) = 1 + values12 (69 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (349 : Fin 455) (by
      change 1 + values12 (70 : Fin 154) = 1 + values12 (70 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (351 : Fin 455) (by
      change 1 + values12 (71 : Fin 154) = 1 + values12 (71 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (352 : Fin 455) (by
      change 1 + values12 (72 : Fin 154) = 1 + values12 (72 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (356 : Fin 455) (by
      change 1 + values12 (73 : Fin 154) = 1 + values12 (73 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (359 : Fin 455) (by
      change 1 + values12 (74 : Fin 154) = 1 + values12 (74 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (360 : Fin 455) (by
      change 1 + values12 (75 : Fin 154) = 1 + values12 (75 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = 1 + values12 (76 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (364 : Fin 455) (by
      change 1 + values12 (77 : Fin 154) = 1 + values12 (77 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (365 : Fin 455) (by
      change 1 + values12 (78 : Fin 154) = 1 + values12 (78 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (366 : Fin 455) (by
      change 1 + values12 (79 : Fin 154) = 1 + values12 (79 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (368 : Fin 455) (by
      change 1 + values12 (80 : Fin 154) = 1 + values12 (80 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (369 : Fin 455) (by
      change 1 + values12 (81 : Fin 154) = 1 + values12 (81 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (372 : Fin 455) (by
      change 1 + values12 (82 : Fin 154) = 1 + values12 (82 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (374 : Fin 455) (by
      change 1 + values12 (83 : Fin 154) = 1 + values12 (83 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (377 : Fin 455) (by
      change 1 + values12 (84 : Fin 154) = 1 + values12 (84 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (378 : Fin 455) (by
      change 1 + values12 (85 : Fin 154) = 1 + values12 (85 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 1 + values12 (86 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (381 : Fin 455) (by
      change 1 + values12 (87 : Fin 154) = 1 + values12 (87 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (382 : Fin 455) (by
      change 1 + values12 (88 : Fin 154) = 1 + values12 (88 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = 1 + values12 (89 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (384 : Fin 455) (by
      change 1 + values12 (90 : Fin 154) = 1 + values12 (90 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 1 + values12 (91 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (386 : Fin 455) (by
      change 1 + values12 (92 : Fin 154) = 1 + values12 (92 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (388 : Fin 455) (by
      change 1 + values12 (93 : Fin 154) = 1 + values12 (93 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (390 : Fin 455) (by
      change 1 + values12 (94 : Fin 154) = 1 + values12 (94 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 1 + values12 (95 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (392 : Fin 455) (by
      change 1 + values12 (96 : Fin 154) = 1 + values12 (96 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (393 : Fin 455) (by
      change 1 + values12 (97 : Fin 154) = 1 + values12 (97 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (394 : Fin 455) (by
      change 1 + values12 (98 : Fin 154) = 1 + values12 (98 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = 1 + values12 (99 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 1 + values12 (100 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (398 : Fin 455) (by
      change 1 + values12 (101 : Fin 154) = 1 + values12 (101 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (399 : Fin 455) (by
      change 1 + values12 (102 : Fin 154) = 1 + values12 (102 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (400 : Fin 455) (by
      change 1 + values12 (103 : Fin 154) = 1 + values12 (103 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = 1 + values12 (104 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (403 : Fin 455) (by
      change 1 + values12 (105 : Fin 154) = 1 + values12 (105 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (404 : Fin 455) (by
      change 1 + values12 (106 : Fin 154) = 1 + values12 (106 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 1 + values12 (107 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (407 : Fin 455) (by
      change 1 + values12 (108 : Fin 154) = 1 + values12 (108 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (408 : Fin 455) (by
      change 1 + values12 (109 : Fin 154) = 1 + values12 (109 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 1 + values12 (110 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (410 : Fin 455) (by
      change 1 + values12 (111 : Fin 154) = 1 + values12 (111 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (411 : Fin 455) (by
      change 1 + values12 (112 : Fin 154) = 1 + values12 (112 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (412 : Fin 455) (by
      change 1 + values12 (113 : Fin 154) = 1 + values12 (113 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (413 : Fin 455) (by
      change 1 + values12 (114 : Fin 154) = 1 + values12 (114 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = 1 + values12 (115 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = 1 + values12 (116 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (417 : Fin 455) (by
      change 1 + values12 (117 : Fin 154) = 1 + values12 (117 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 1 + values12 (118 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (419 : Fin 455) (by
      change 1 + values12 (119 : Fin 154) = 1 + values12 (119 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = 1 + values12 (120 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (421 : Fin 455) (by
      change 1 + values12 (121 : Fin 154) = 1 + values12 (121 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (422 : Fin 455) (by
      change 1 + values12 (122 : Fin 154) = 1 + values12 (122 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (423 : Fin 455) (by
      change 1 + values12 (123 : Fin 154) = 1 + values12 (123 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 1 + values12 (124 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (425 : Fin 455) (by
      change 1 + values12 (125 : Fin 154) = 1 + values12 (125 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = 1 + values12 (126 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (427 : Fin 455) (by
      change 1 + values12 (127 : Fin 154) = 1 + values12 (127 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (428 : Fin 455) (by
      change 1 + values12 (128 : Fin 154) = 1 + values12 (128 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (429 : Fin 455) (by
      change 1 + values12 (129 : Fin 154) = 1 + values12 (129 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 1 + values12 (130 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (431 : Fin 455) (by
      change 1 + values12 (131 : Fin 154) = 1 + values12 (131 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = 1 + values12 (132 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = 1 + values12 (133 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = 1 + values12 (134 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (435 : Fin 455) (by
      change 1 + values12 (135 : Fin 154) = 1 + values12 (135 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 1 + values12 (136 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (437 : Fin 455) (by
      change 1 + values12 (137 : Fin 154) = 1 + values12 (137 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (439 : Fin 455) (by
      change 1 + values12 (138 : Fin 154) = 1 + values12 (138 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = 1 + values12 (139 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 1 + values12 (140 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (442 : Fin 455) (by
      change 1 + values12 (141 : Fin 154) = 1 + values12 (141 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = 1 + values12 (142 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (444 : Fin 455) (by
      change 1 + values12 (143 : Fin 154) = 1 + values12 (143 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = 1 + values12 (144 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = 1 + values12 (145 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 1 + values12 (146 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (448 : Fin 455) (by
      change 1 + values12 (147 : Fin 154) = 1 + values12 (147 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = 1 + values12 (148 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = 1 + values12 (149 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (451 : Fin 455) (by
      change 1 + values12 (150 : Fin 154) = 1 + values12 (150 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 1 + values12 (151 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (453 : Fin 455) (by
      change 1 + values12 (152 : Fin 154) = 1 + values12 (152 : Fin 154)
      rfl
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = 1 + values12 (153 : Fin 154)
      rfl
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values11_mem_range_values14 (i : Fin 91) :
    (Set.range values14) (1 + values11 i) := by
  fin_cases i
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = 1 + values11 (0 : Fin 91)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (251 : Fin 455) (by
      change 1 + values12 (2 : Fin 154) = 1 + values11 (1 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (252 : Fin 455) (by
      change 1 + values12 (3 : Fin 154) = 1 + values11 (2 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (254 : Fin 455) (by
      change 1 + values12 (5 : Fin 154) = 1 + values11 (3 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (257 : Fin 455) (by
      change 1 + values12 (7 : Fin 154) = 1 + values11 (4 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (258 : Fin 455) (by
      change 1 + values12 (8 : Fin 154) = 1 + values11 (5 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (261 : Fin 455) (by
      change 1 + values12 (10 : Fin 154) = 1 + values11 (6 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (262 : Fin 455) (by
      change 1 + values12 (11 : Fin 154) = 1 + values11 (7 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = 1 + values11 (8 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (267 : Fin 455) (by
      change 1 + values12 (14 : Fin 154) = 1 + values11 (9 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (268 : Fin 455) (by
      change 1 + values12 (15 : Fin 154) = 1 + values11 (10 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (270 : Fin 455) (by
      change 1 + values12 (17 : Fin 154) = 1 + values11 (11 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = 1 + values11 (12 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (275 : Fin 455) (by
      change 1 + values12 (21 : Fin 154) = 1 + values11 (13 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (277 : Fin 455) (by
      change 1 + values12 (22 : Fin 154) = 1 + values11 (14 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (279 : Fin 455) (by
      change 1 + values12 (24 : Fin 154) = 1 + values11 (15 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (281 : Fin 455) (by
      change 1 + values12 (26 : Fin 154) = 1 + values11 (16 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (285 : Fin 455) (by
      change 1 + values12 (28 : Fin 154) = 1 + values11 (17 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (287 : Fin 455) (by
      change 1 + values12 (30 : Fin 154) = 1 + values11 (18 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = 1 + values11 (19 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (292 : Fin 455) (by
      change 1 + values12 (33 : Fin 154) = 1 + values11 (20 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (294 : Fin 455) (by
      change 1 + values12 (34 : Fin 154) = 1 + values11 (21 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (297 : Fin 455) (by
      change 1 + values12 (36 : Fin 154) = 1 + values11 (22 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (301 : Fin 455) (by
      change 1 + values12 (39 : Fin 154) = 1 + values11 (23 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (303 : Fin 455) (by
      change 1 + values12 (40 : Fin 154) = 1 + values11 (24 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (305 : Fin 455) (by
      change 1 + values12 (42 : Fin 154) = 1 + values11 (25 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (309 : Fin 455) (by
      change 1 + values12 (44 : Fin 154) = 1 + values11 (26 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (310 : Fin 455) (by
      change 1 + values12 (45 : Fin 154) = 1 + values11 (27 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = 1 + values11 (28 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (314 : Fin 455) (by
      change 1 + values12 (48 : Fin 154) = 1 + values11 (29 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (316 : Fin 455) (by
      change 1 + values12 (49 : Fin 154) = 1 + values11 (30 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = 1 + values11 (31 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (322 : Fin 455) (by
      change 1 + values12 (53 : Fin 154) = 1 + values11 (32 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (324 : Fin 455) (by
      change 1 + values12 (54 : Fin 154) = 1 + values11 (33 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (328 : Fin 455) (by
      change 1 + values12 (56 : Fin 154) = 1 + values11 (34 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (333 : Fin 455) (by
      change 1 + values12 (59 : Fin 154) = 1 + values11 (35 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (334 : Fin 455) (by
      change 1 + values12 (60 : Fin 154) = 1 + values11 (36 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (337 : Fin 455) (by
      change 1 + values12 (62 : Fin 154) = 1 + values11 (37 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (338 : Fin 455) (by
      change 1 + values12 (63 : Fin 154) = 1 + values11 (38 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (341 : Fin 455) (by
      change 1 + values12 (64 : Fin 154) = 1 + values11 (39 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = 1 + values11 (40 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (347 : Fin 455) (by
      change 1 + values12 (68 : Fin 154) = 1 + values11 (41 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (349 : Fin 455) (by
      change 1 + values12 (70 : Fin 154) = 1 + values11 (42 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (351 : Fin 455) (by
      change 1 + values12 (71 : Fin 154) = 1 + values11 (43 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (356 : Fin 455) (by
      change 1 + values12 (73 : Fin 154) = 1 + values11 (44 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (359 : Fin 455) (by
      change 1 + values12 (74 : Fin 154) = 1 + values11 (45 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = 1 + values11 (46 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (365 : Fin 455) (by
      change 1 + values12 (78 : Fin 154) = 1 + values11 (47 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (368 : Fin 455) (by
      change 1 + values12 (80 : Fin 154) = 1 + values11 (48 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (372 : Fin 455) (by
      change 1 + values12 (82 : Fin 154) = 1 + values11 (49 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (377 : Fin 455) (by
      change 1 + values12 (84 : Fin 154) = 1 + values11 (50 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 1 + values11 (51 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (382 : Fin 455) (by
      change 1 + values12 (88 : Fin 154) = 1 + values11 (52 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = 1 + values11 (53 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 1 + values11 (54 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (390 : Fin 455) (by
      change 1 + values12 (94 : Fin 154) = 1 + values11 (55 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 1 + values11 (56 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (392 : Fin 455) (by
      change 1 + values12 (96 : Fin 154) = 1 + values11 (57 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (394 : Fin 455) (by
      change 1 + values12 (98 : Fin 154) = 1 + values11 (58 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = 1 + values11 (59 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 1 + values11 (60 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (399 : Fin 455) (by
      change 1 + values12 (102 : Fin 154) = 1 + values11 (61 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (400 : Fin 455) (by
      change 1 + values12 (103 : Fin 154) = 1 + values11 (62 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = 1 + values11 (63 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 1 + values11 (64 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (408 : Fin 455) (by
      change 1 + values12 (109 : Fin 154) = 1 + values11 (65 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 1 + values11 (66 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (411 : Fin 455) (by
      change 1 + values12 (112 : Fin 154) = 1 + values11 (67 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = 1 + values11 (68 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = 1 + values11 (69 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 1 + values11 (70 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = 1 + values11 (71 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (421 : Fin 455) (by
      change 1 + values12 (121 : Fin 154) = 1 + values11 (72 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 1 + values11 (73 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = 1 + values11 (74 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (427 : Fin 455) (by
      change 1 + values12 (127 : Fin 154) = 1 + values11 (75 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 1 + values11 (76 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = 1 + values11 (77 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = 1 + values11 (78 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = 1 + values11 (79 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 1 + values11 (80 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = 1 + values11 (81 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 1 + values11 (82 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = 1 + values11 (83 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = 1 + values11 (84 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = 1 + values11 (85 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 1 + values11 (86 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = 1 + values11 (87 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = 1 + values11 (88 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 1 + values11 (89 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = 1 + values11 (90 : Fin 91)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values10_mem_range_values14 (i : Fin 54) :
    (Set.range values14) (1 + values10 i) := by
  fin_cases i
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = 1 + values10 (0 : Fin 54)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (252 : Fin 455) (by
      change 1 + values12 (3 : Fin 154) = 1 + values10 (1 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (254 : Fin 455) (by
      change 1 + values12 (5 : Fin 154) = 1 + values10 (2 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (258 : Fin 455) (by
      change 1 + values12 (8 : Fin 154) = 1 + values10 (3 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (262 : Fin 455) (by
      change 1 + values12 (11 : Fin 154) = 1 + values10 (4 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = 1 + values10 (5 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (268 : Fin 455) (by
      change 1 + values12 (15 : Fin 154) = 1 + values10 (6 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (270 : Fin 455) (by
      change 1 + values12 (17 : Fin 154) = 1 + values10 (7 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = 1 + values10 (8 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (277 : Fin 455) (by
      change 1 + values12 (22 : Fin 154) = 1 + values10 (9 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (279 : Fin 455) (by
      change 1 + values12 (24 : Fin 154) = 1 + values10 (10 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (285 : Fin 455) (by
      change 1 + values12 (28 : Fin 154) = 1 + values10 (11 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = 1 + values10 (12 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (294 : Fin 455) (by
      change 1 + values12 (34 : Fin 154) = 1 + values10 (13 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (297 : Fin 455) (by
      change 1 + values12 (36 : Fin 154) = 1 + values10 (14 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (303 : Fin 455) (by
      change 1 + values12 (40 : Fin 154) = 1 + values10 (15 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (309 : Fin 455) (by
      change 1 + values12 (44 : Fin 154) = 1 + values10 (16 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = 1 + values10 (17 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (316 : Fin 455) (by
      change 1 + values12 (49 : Fin 154) = 1 + values10 (18 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = 1 + values10 (19 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (324 : Fin 455) (by
      change 1 + values12 (54 : Fin 154) = 1 + values10 (20 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (328 : Fin 455) (by
      change 1 + values12 (56 : Fin 154) = 1 + values10 (21 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (334 : Fin 455) (by
      change 1 + values12 (60 : Fin 154) = 1 + values10 (22 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (341 : Fin 455) (by
      change 1 + values12 (64 : Fin 154) = 1 + values10 (23 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = 1 + values10 (24 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (349 : Fin 455) (by
      change 1 + values12 (70 : Fin 154) = 1 + values10 (25 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (356 : Fin 455) (by
      change 1 + values12 (73 : Fin 154) = 1 + values10 (26 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (359 : Fin 455) (by
      change 1 + values12 (74 : Fin 154) = 1 + values10 (27 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = 1 + values10 (28 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (368 : Fin 455) (by
      change 1 + values12 (80 : Fin 154) = 1 + values10 (29 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (372 : Fin 455) (by
      change 1 + values12 (82 : Fin 154) = 1 + values10 (30 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 1 + values10 (31 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = 1 + values10 (32 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 1 + values10 (33 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 1 + values10 (34 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = 1 + values10 (35 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 1 + values10 (36 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (400 : Fin 455) (by
      change 1 + values12 (103 : Fin 154) = 1 + values10 (37 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = 1 + values10 (38 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 1 + values10 (39 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 1 + values10 (40 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = 1 + values10 (41 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 1 + values10 (42 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = 1 + values10 (43 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 1 + values10 (44 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = 1 + values10 (45 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 1 + values10 (46 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = 1 + values10 (47 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 1 + values10 (48 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 1 + values10 (49 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = 1 + values10 (50 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 1 + values10 (51 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = 1 + values10 (52 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 1 + values10 (53 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values10_mem_range_values14 (i : Fin 54) :
    (Set.range values14) (2 + values10 i) := by
  fin_cases i
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 2 + values10 (0 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (381 : Fin 455) (by
      change 1 + values12 (87 : Fin 154) = 2 + values10 (1 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (382 : Fin 455) (by
      change 1 + values12 (88 : Fin 154) = 2 + values10 (2 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = 2 + values10 (3 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (384 : Fin 455) (by
      change 1 + values12 (90 : Fin 154) = 2 + values10 (4 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 2 + values10 (5 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (388 : Fin 455) (by
      change 1 + values12 (93 : Fin 154) = 2 + values10 (6 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (390 : Fin 455) (by
      change 1 + values12 (94 : Fin 154) = 2 + values10 (7 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 2 + values10 (8 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (393 : Fin 455) (by
      change 1 + values12 (97 : Fin 154) = 2 + values10 (9 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (394 : Fin 455) (by
      change 1 + values12 (98 : Fin 154) = 2 + values10 (10 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = 2 + values10 (11 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 2 + values10 (12 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (398 : Fin 455) (by
      change 1 + values12 (101 : Fin 154) = 2 + values10 (13 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (399 : Fin 455) (by
      change 1 + values12 (102 : Fin 154) = 2 + values10 (14 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = 2 + values10 (15 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (404 : Fin 455) (by
      change 1 + values12 (106 : Fin 154) = 2 + values10 (16 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 2 + values10 (17 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (407 : Fin 455) (by
      change 1 + values12 (108 : Fin 154) = 2 + values10 (18 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 2 + values10 (19 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (410 : Fin 455) (by
      change 1 + values12 (111 : Fin 154) = 2 + values10 (20 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (411 : Fin 455) (by
      change 1 + values12 (112 : Fin 154) = 2 + values10 (21 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = 2 + values10 (22 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (417 : Fin 455) (by
      change 1 + values12 (117 : Fin 154) = 2 + values10 (23 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 2 + values10 (24 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (419 : Fin 455) (by
      change 1 + values12 (119 : Fin 154) = 2 + values10 (25 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (421 : Fin 455) (by
      change 1 + values12 (121 : Fin 154) = 2 + values10 (26 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (422 : Fin 455) (by
      change 1 + values12 (122 : Fin 154) = 2 + values10 (27 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 2 + values10 (28 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (425 : Fin 455) (by
      change 1 + values12 (125 : Fin 154) = 2 + values10 (29 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (427 : Fin 455) (by
      change 1 + values12 (127 : Fin 154) = 2 + values10 (30 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 2 + values10 (31 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (431 : Fin 455) (by
      change 1 + values12 (131 : Fin 154) = 2 + values10 (32 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = 2 + values10 (33 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = 2 + values10 (34 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (435 : Fin 455) (by
      change 1 + values12 (135 : Fin 154) = 2 + values10 (35 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 2 + values10 (36 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (437 : Fin 455) (by
      change 1 + values12 (137 : Fin 154) = 2 + values10 (37 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (439 : Fin 455) (by
      change 1 + values12 (138 : Fin 154) = 2 + values10 (38 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = 2 + values10 (39 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 2 + values10 (40 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (442 : Fin 455) (by
      change 1 + values12 (141 : Fin 154) = 2 + values10 (41 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = 2 + values10 (42 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (444 : Fin 455) (by
      change 1 + values12 (143 : Fin 154) = 2 + values10 (43 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = 2 + values10 (44 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = 2 + values10 (45 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 2 + values10 (46 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (448 : Fin 455) (by
      change 1 + values12 (147 : Fin 154) = 2 + values10 (47 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = 2 + values10 (48 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = 2 + values10 (49 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (451 : Fin 455) (by
      change 1 + values12 (150 : Fin 154) = 2 + values10 (50 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 2 + values10 (51 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (453 : Fin 455) (by
      change 1 + values12 (152 : Fin 154) = 2 + values10 (52 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = 2 + values10 (53 : Fin 54)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem one_add_values9_mem_range_values14 (i : Fin 33) :
    (Set.range values14) (1 + values9 i) := by
  fin_cases i
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = 1 + values9 (0 : Fin 33)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (254 : Fin 455) (by
      change 1 + values12 (5 : Fin 154) = 1 + values9 (1 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (258 : Fin 455) (by
      change 1 + values12 (8 : Fin 154) = 1 + values9 (2 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = 1 + values9 (3 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (270 : Fin 455) (by
      change 1 + values12 (17 : Fin 154) = 1 + values9 (4 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = 1 + values9 (5 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (279 : Fin 455) (by
      change 1 + values12 (24 : Fin 154) = 1 + values9 (6 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (285 : Fin 455) (by
      change 1 + values12 (28 : Fin 154) = 1 + values9 (7 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = 1 + values9 (8 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (297 : Fin 455) (by
      change 1 + values12 (36 : Fin 154) = 1 + values9 (9 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (303 : Fin 455) (by
      change 1 + values12 (40 : Fin 154) = 1 + values9 (10 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = 1 + values9 (11 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = 1 + values9 (12 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (328 : Fin 455) (by
      change 1 + values12 (56 : Fin 154) = 1 + values9 (13 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (334 : Fin 455) (by
      change 1 + values12 (60 : Fin 154) = 1 + values9 (14 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = 1 + values9 (15 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (356 : Fin 455) (by
      change 1 + values12 (73 : Fin 154) = 1 + values9 (16 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = 1 + values9 (17 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (372 : Fin 455) (by
      change 1 + values12 (82 : Fin 154) = 1 + values9 (18 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 1 + values9 (19 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 1 + values9 (20 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 1 + values9 (21 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 1 + values9 (22 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 1 + values9 (23 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 1 + values9 (24 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 1 + values9 (25 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 1 + values9 (26 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = 1 + values9 (27 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 1 + values9 (28 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 1 + values9 (29 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 1 + values9 (30 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 1 + values9 (31 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 1 + values9 (32 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_two_add_values9_mem_range_values14 (i : Fin 33) :
    (Set.range values14) (Real.sqrt 2 + values9 i) := by
  fin_cases i
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = Real.sqrt 2 + values9 (0 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (323 : Fin 455) (by
      change Real.sqrt 2 + values9 (1 : Fin 33) = Real.sqrt 2 + values9 (1 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (326 : Fin 455) (by
      change Real.sqrt 2 + values9 (2 : Fin 33) = Real.sqrt 2 + values9 (2 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (332 : Fin 455) (by
      change Real.sqrt 2 + values9 (3 : Fin 33) = Real.sqrt 2 + values9 (3 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (335 : Fin 455) (by
      change Real.sqrt 2 + values9 (4 : Fin 33) = Real.sqrt 2 + values9 (4 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (339 : Fin 455) (by
      change Real.sqrt 2 + values9 (5 : Fin 33) = Real.sqrt 2 + values9 (5 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (342 : Fin 455) (by
      change Real.sqrt 2 + values9 (6 : Fin 33) = Real.sqrt 2 + values9 (6 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (345 : Fin 455) (by
      change Real.sqrt 2 + values9 (7 : Fin 33) = Real.sqrt 2 + values9 (7 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (350 : Fin 455) (by
      change Real.sqrt 2 + values9 (8 : Fin 33) = Real.sqrt 2 + values9 (8 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (353 : Fin 455) (by
      change Real.sqrt 2 + values9 (9 : Fin 33) = Real.sqrt 2 + values9 (9 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (357 : Fin 455) (by
      change Real.sqrt 2 + values9 (10 : Fin 33) = Real.sqrt 2 + values9 (10 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (361 : Fin 455) (by
      change Real.sqrt 2 + values9 (11 : Fin 33) = Real.sqrt 2 + values9 (11 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (371 : Fin 455) (by
      change Real.sqrt 2 + values9 (12 : Fin 33) = Real.sqrt 2 + values9 (12 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (373 : Fin 455) (by
      change Real.sqrt 2 + values9 (13 : Fin 33) = Real.sqrt 2 + values9 (13 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (375 : Fin 455) (by
      change Real.sqrt 2 + values9 (14 : Fin 33) = Real.sqrt 2 + values9 (14 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (379 : Fin 455) (by
      change Real.sqrt 2 + values9 (15 : Fin 33) = Real.sqrt 2 + values9 (15 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (389 : Fin 455) (by
      change Real.sqrt 2 + values9 (16 : Fin 33) = Real.sqrt 2 + values9 (16 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (395 : Fin 455) (by
      change Real.sqrt 2 + values9 (17 : Fin 33) = Real.sqrt 2 + values9 (17 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (402 : Fin 455) (by
      change Real.sqrt 2 + values9 (18 : Fin 33) = Real.sqrt 2 + values9 (18 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = Real.sqrt 2 + values9 (19 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (413 : Fin 455) (by
      change 1 + values12 (114 : Fin 154) = Real.sqrt 2 + values9 (20 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = Real.sqrt 2 + values9 (21 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = Real.sqrt 2 + values9 (22 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (423 : Fin 455) (by
      change 1 + values12 (123 : Fin 154) = Real.sqrt 2 + values9 (23 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = Real.sqrt 2 + values9 (24 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (429 : Fin 455) (by
      change 1 + values12 (129 : Fin 154) = Real.sqrt 2 + values9 (25 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = Real.sqrt 2 + values9 (26 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (438 : Fin 455) (by
      change Real.sqrt 2 + values9 (27 : Fin 33) = Real.sqrt 2 + values9 (27 : Fin 33)
      rfl
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = Real.sqrt 2 + values9 (28 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (444 : Fin 455) (by
      change 1 + values12 (143 : Fin 154) = Real.sqrt 2 + values9 (29 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = Real.sqrt 2 + values9 (30 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = Real.sqrt 2 + values9 (31 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (453 : Fin 455) (by
      change 1 + values12 (152 : Fin 154) = Real.sqrt 2 + values9 (32 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem two_add_values9_mem_range_values14 (i : Fin 33) :
    (Set.range values14) (2 + values9 i) := by
  fin_cases i
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = 2 + values9 (0 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (382 : Fin 455) (by
      change 1 + values12 (88 : Fin 154) = 2 + values9 (1 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = 2 + values9 (2 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = 2 + values9 (3 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (390 : Fin 455) (by
      change 1 + values12 (94 : Fin 154) = 2 + values9 (4 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = 2 + values9 (5 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (394 : Fin 455) (by
      change 1 + values12 (98 : Fin 154) = 2 + values9 (6 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = 2 + values9 (7 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = 2 + values9 (8 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (399 : Fin 455) (by
      change 1 + values12 (102 : Fin 154) = 2 + values9 (9 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = 2 + values9 (10 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = 2 + values9 (11 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = 2 + values9 (12 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (411 : Fin 455) (by
      change 1 + values12 (112 : Fin 154) = 2 + values9 (13 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = 2 + values9 (14 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = 2 + values9 (15 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (421 : Fin 455) (by
      change 1 + values12 (121 : Fin 154) = 2 + values9 (16 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = 2 + values9 (17 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (427 : Fin 455) (by
      change 1 + values12 (127 : Fin 154) = 2 + values9 (18 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = 2 + values9 (19 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = 2 + values9 (20 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = 2 + values9 (21 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = 2 + values9 (22 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = 2 + values9 (23 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = 2 + values9 (24 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = 2 + values9 (25 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = 2 + values9 (26 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = 2 + values9 (27 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = 2 + values9 (28 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = 2 + values9 (29 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = 2 + values9 (30 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = 2 + values9 (31 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = 2 + values9 (32 : Fin 33)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values5_add_values8_mem_range_values14 (i : Fin 5) (j : Fin 20) :
    (Set.range values14) (values5 i + values8 j) := by
  fin_cases i <;> fin_cases j
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = values5 (0 : Fin 5) + values8 (0 : Fin 20)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (258 : Fin 455) (by
      change 1 + values12 (8 : Fin 154) = values5 (0 : Fin 5) + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = values5 (0 : Fin 5) + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = values5 (0 : Fin 5) + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (285 : Fin 455) (by
      change 1 + values12 (28 : Fin 154) = values5 (0 : Fin 5) + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = values5 (0 : Fin 5) + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (303 : Fin 455) (by
      change 1 + values12 (40 : Fin 154) = values5 (0 : Fin 5) + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = values5 (0 : Fin 5) + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = values5 (0 : Fin 5) + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (334 : Fin 455) (by
      change 1 + values12 (60 : Fin 154) = values5 (0 : Fin 5) + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = values5 (0 : Fin 5) + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = values5 (0 : Fin 5) + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = values5 (0 : Fin 5) + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = values5 (0 : Fin 5) + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values5 (0 : Fin 5) + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values5 (0 : Fin 5) + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = values5 (0 : Fin 5) + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values5 (0 : Fin 5) + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values5 (0 : Fin 5) + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values5 (0 : Fin 5) + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = values5 (1 : Fin 5) + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (296 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (1 : Fin 20) = values5 (1 : Fin 5) + values8 (1 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (300 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (2 : Fin 20) = values5 (1 : Fin 5) + values8 (2 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (308 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (3 : Fin 20) = values5 (1 : Fin 5) + values8 (3 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (315 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (4 : Fin 20) = values5 (1 : Fin 5) + values8 (4 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (317 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (5 : Fin 20) = values5 (1 : Fin 5) + values8 (5 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (325 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (6 : Fin 20) = values5 (1 : Fin 5) + values8 (6 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (340 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (7 : Fin 20) = values5 (1 : Fin 5) + values8 (7 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (350 : Fin 455) (by
      change Real.sqrt 2 + values9 (8 : Fin 33) = values5 (1 : Fin 5) + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (358 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (9 : Fin 20) = values5 (1 : Fin 5) + values8 (9 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (363 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (10 : Fin 20) = values5 (1 : Fin 5) + values8 (10 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (376 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (11 : Fin 20) = values5 (1 : Fin 5) + values8 (11 : Fin 20)
      rfl
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values5 (1 : Fin 5) + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (403 : Fin 455) (by
      change 1 + values12 (105 : Fin 154) = values5 (1 : Fin 5) + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (408 : Fin 455) (by
      change 1 + values12 (109 : Fin 154) = values5 (1 : Fin 5) + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = values5 (1 : Fin 5) + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (428 : Fin 455) (by
      change 1 + values12 (128 : Fin 154) = values5 (1 : Fin 5) + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values5 (1 : Fin 5) + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (444 : Fin 455) (by
      change 1 + values12 (143 : Fin 154) = values5 (1 : Fin 5) + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = values5 (1 : Fin 5) + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = values5 (2 : Fin 5) + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (326 : Fin 455) (by
      change Real.sqrt 2 + values9 (2 : Fin 33) = values5 (2 : Fin 5) + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (332 : Fin 455) (by
      change Real.sqrt 2 + values9 (3 : Fin 33) = values5 (2 : Fin 5) + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (339 : Fin 455) (by
      change Real.sqrt 2 + values9 (5 : Fin 33) = values5 (2 : Fin 5) + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (345 : Fin 455) (by
      change Real.sqrt 2 + values9 (7 : Fin 33) = values5 (2 : Fin 5) + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (350 : Fin 455) (by
      change Real.sqrt 2 + values9 (8 : Fin 33) = values5 (2 : Fin 5) + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (357 : Fin 455) (by
      change Real.sqrt 2 + values9 (10 : Fin 33) = values5 (2 : Fin 5) + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (361 : Fin 455) (by
      change Real.sqrt 2 + values9 (11 : Fin 33) = values5 (2 : Fin 5) + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (371 : Fin 455) (by
      change Real.sqrt 2 + values9 (12 : Fin 33) = values5 (2 : Fin 5) + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (375 : Fin 455) (by
      change Real.sqrt 2 + values9 (14 : Fin 33) = values5 (2 : Fin 5) + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (379 : Fin 455) (by
      change Real.sqrt 2 + values9 (15 : Fin 33) = values5 (2 : Fin 5) + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (395 : Fin 455) (by
      change Real.sqrt 2 + values9 (17 : Fin 33) = values5 (2 : Fin 5) + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values5 (2 : Fin 5) + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = values5 (2 : Fin 5) + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = values5 (2 : Fin 5) + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = values5 (2 : Fin 5) + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = values5 (2 : Fin 5) + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values5 (2 : Fin 5) + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = values5 (2 : Fin 5) + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values5 (2 : Fin 5) + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = values5 (3 : Fin 5) + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (383 : Fin 455) (by
      change 1 + values12 (89 : Fin 154) = values5 (3 : Fin 5) + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = values5 (3 : Fin 5) + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = values5 (3 : Fin 5) + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (396 : Fin 455) (by
      change 1 + values12 (99 : Fin 154) = values5 (3 : Fin 5) + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values5 (3 : Fin 5) + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (401 : Fin 455) (by
      change 1 + values12 (104 : Fin 154) = values5 (3 : Fin 5) + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = values5 (3 : Fin 5) + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values5 (3 : Fin 5) + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (415 : Fin 455) (by
      change 1 + values12 (115 : Fin 154) = values5 (3 : Fin 5) + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = values5 (3 : Fin 5) + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = values5 (3 : Fin 5) + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values5 (3 : Fin 5) + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = values5 (3 : Fin 5) + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values5 (3 : Fin 5) + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values5 (3 : Fin 5) + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = values5 (3 : Fin 5) + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values5 (3 : Fin 5) + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values5 (3 : Fin 5) + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = values5 (3 : Fin 5) + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values5 (4 : Fin 5) + values8 (0 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (431 : Fin 455) (by
      change 1 + values12 (131 : Fin 154) = values5 (4 : Fin 5) + values8 (1 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = values5 (4 : Fin 5) + values8 (2 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = values5 (4 : Fin 5) + values8 (3 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (435 : Fin 455) (by
      change 1 + values12 (135 : Fin 154) = values5 (4 : Fin 5) + values8 (4 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values5 (4 : Fin 5) + values8 (5 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (439 : Fin 455) (by
      change 1 + values12 (138 : Fin 154) = values5 (4 : Fin 5) + values8 (6 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = values5 (4 : Fin 5) + values8 (7 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values5 (4 : Fin 5) + values8 (8 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (442 : Fin 455) (by
      change 1 + values12 (141 : Fin 154) = values5 (4 : Fin 5) + values8 (9 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = values5 (4 : Fin 5) + values8 (10 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = values5 (4 : Fin 5) + values8 (11 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values5 (4 : Fin 5) + values8 (12 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (448 : Fin 455) (by
      change 1 + values12 (147 : Fin 154) = values5 (4 : Fin 5) + values8 (13 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = values5 (4 : Fin 5) + values8 (14 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values5 (4 : Fin 5) + values8 (15 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (451 : Fin 455) (by
      change 1 + values12 (150 : Fin 154) = values5 (4 : Fin 5) + values8 (16 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = values5 (4 : Fin 5) + values8 (17 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (453 : Fin 455) (by
      change 1 + values12 (152 : Fin 154) = values5 (4 : Fin 5) + values8 (18 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = values5 (4 : Fin 5) + values8 (19 : Fin 20)
      a158415_twelve_table <;> try rw [sqrt_four]
    )

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values6_add_values7_mem_range_values14 (i : Fin 8) (j : Fin 13) :
    (Set.range values14) (values6 i + values7 j) := by
  fin_cases i <;> fin_cases j
  next =>
    exact Exists.intro (249 : Fin 455) (by
      change Real.sqrt (values13 (249 : Fin 264)) = values6 (0 : Fin 8) + values7 (0 : Fin 13)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (264 : Fin 455) (by
      change 1 + values12 (12 : Fin 154) = values6 (0 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = values6 (0 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = values6 (0 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (311 : Fin 455) (by
      change 1 + values12 (46 : Fin 154) = values6 (0 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = values6 (0 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (344 : Fin 455) (by
      change 1 + values12 (66 : Fin 154) = values6 (0 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = values6 (0 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = values6 (0 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values6 (0 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values6 (0 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values6 (0 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values6 (0 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (273 : Fin 455) (by
      change 1 + values12 (19 : Fin 154) = values6 (1 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (283 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (1 : Fin 13) = values6 (1 : Fin 8) + values7 (1 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (289 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (2 : Fin 13) = values6 (1 : Fin 8) + values7 (2 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (308 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (3 : Fin 20) = values6 (1 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (319 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (4 : Fin 13) = values6 (1 : Fin 8) + values7 (4 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (339 : Fin 455) (by
      change Real.sqrt 2 + values9 (5 : Fin 33) = values6 (1 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (354 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (6 : Fin 13) = values6 (1 : Fin 8) + values7 (6 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (370 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (7 : Fin 13) = values6 (1 : Fin 8) + values7 (7 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = values6 (1 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (403 : Fin 455) (by
      change 1 + values12 (105 : Fin 154) = values6 (1 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = values6 (1 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = values6 (1 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (448 : Fin 455) (by
      change 1 + values12 (147 : Fin 154) = values6 (1 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (290 : Fin 455) (by
      change 1 + values12 (31 : Fin 154) = values6 (2 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (300 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (2 : Fin 20) = values6 (2 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (308 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (3 : Fin 20) = values6 (2 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (317 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (5 : Fin 20) = values6 (2 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (340 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (7 : Fin 20) = values6 (2 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (350 : Fin 455) (by
      change Real.sqrt 2 + values9 (8 : Fin 33) = values6 (2 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (363 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (10 : Fin 20) = values6 (2 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (376 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (11 : Fin 20) = values6 (2 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values6 (2 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (408 : Fin 455) (by
      change 1 + values12 (109 : Fin 154) = values6 (2 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = values6 (2 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values6 (2 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = values6 (2 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (320 : Fin 455) (by
      change 1 + values12 (51 : Fin 154) = values6 (3 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (332 : Fin 455) (by
      change Real.sqrt 2 + values9 (3 : Fin 33) = values6 (3 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (339 : Fin 455) (by
      change Real.sqrt 2 + values9 (5 : Fin 33) = values6 (3 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (350 : Fin 455) (by
      change Real.sqrt 2 + values9 (8 : Fin 33) = values6 (3 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (361 : Fin 455) (by
      change Real.sqrt 2 + values9 (11 : Fin 33) = values6 (3 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (371 : Fin 455) (by
      change Real.sqrt 2 + values9 (12 : Fin 33) = values6 (3 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (379 : Fin 455) (by
      change Real.sqrt 2 + values9 (15 : Fin 33) = values6 (3 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (395 : Fin 455) (by
      change Real.sqrt 2 + values9 (17 : Fin 33) = values6 (3 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values6 (3 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = values6 (3 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = values6 (3 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values6 (3 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values6 (3 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (362 : Fin 455) (by
      change 1 + values12 (76 : Fin 154) = values6 (4 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (367 : Fin 455) (by
      change values6 (4 : Fin 8) + values7 (1 : Fin 13) = values6 (4 : Fin 8) + values7 (1 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (370 : Fin 455) (by
      change values6 (1 : Fin 8) + values7 (7 : Fin 13) = values6 (4 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (376 : Fin 455) (by
      change values5 (1 : Fin 5) + values8 (11 : Fin 20) = values6 (4 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (387 : Fin 455) (by
      change values6 (4 : Fin 8) + values7 (4 : Fin 13) = values6 (4 : Fin 8) + values7 (4 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (395 : Fin 455) (by
      change Real.sqrt 2 + values9 (17 : Fin 33) = values6 (4 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (405 : Fin 455) (by
      change values6 (4 : Fin 8) + values7 (6 : Fin 13) = values6 (4 : Fin 8) + values7 (6 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (414 : Fin 455) (by
      change values6 (4 : Fin 8) + values7 (7 : Fin 13) = values6 (4 : Fin 8) + values7 (7 : Fin 13)
      rfl
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = values6 (4 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (428 : Fin 455) (by
      change 1 + values12 (128 : Fin 154) = values6 (4 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = values6 (4 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = values6 (4 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (451 : Fin 455) (by
      change 1 + values12 (150 : Fin 154) = values6 (4 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (380 : Fin 455) (by
      change 1 + values12 (86 : Fin 154) = values6 (5 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (385 : Fin 455) (by
      change 1 + values12 (91 : Fin 154) = values6 (5 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (391 : Fin 455) (by
      change 1 + values12 (95 : Fin 154) = values6 (5 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (397 : Fin 455) (by
      change 1 + values12 (100 : Fin 154) = values6 (5 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (406 : Fin 455) (by
      change 1 + values12 (107 : Fin 154) = values6 (5 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values6 (5 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (418 : Fin 455) (by
      change 1 + values12 (118 : Fin 154) = values6 (5 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (424 : Fin 455) (by
      change 1 + values12 (124 : Fin 154) = values6 (5 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values6 (5 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values6 (5 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values6 (5 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values6 (5 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = values6 (5 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (409 : Fin 455) (by
      change 1 + values12 (110 : Fin 154) = values6 (6 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (413 : Fin 455) (by
      change 1 + values12 (114 : Fin 154) = values6 (6 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (416 : Fin 455) (by
      change 1 + values12 (116 : Fin 154) = values6 (6 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (420 : Fin 455) (by
      change 1 + values12 (120 : Fin 154) = values6 (6 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (423 : Fin 455) (by
      change 1 + values12 (123 : Fin 154) = values6 (6 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (426 : Fin 455) (by
      change 1 + values12 (126 : Fin 154) = values6 (6 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (429 : Fin 455) (by
      change 1 + values12 (129 : Fin 154) = values6 (6 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (434 : Fin 455) (by
      change 1 + values12 (134 : Fin 154) = values6 (6 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values6 (6 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (444 : Fin 455) (by
      change 1 + values12 (143 : Fin 154) = values6 (6 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (446 : Fin 455) (by
      change 1 + values12 (145 : Fin 154) = values6 (6 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values6 (6 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (453 : Fin 455) (by
      change 1 + values12 (152 : Fin 154) = values6 (6 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (430 : Fin 455) (by
      change 1 + values12 (130 : Fin 154) = values6 (7 : Fin 8) + values7 (0 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (432 : Fin 455) (by
      change 1 + values12 (132 : Fin 154) = values6 (7 : Fin 8) + values7 (1 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (433 : Fin 455) (by
      change 1 + values12 (133 : Fin 154) = values6 (7 : Fin 8) + values7 (2 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (436 : Fin 455) (by
      change 1 + values12 (136 : Fin 154) = values6 (7 : Fin 8) + values7 (3 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (440 : Fin 455) (by
      change 1 + values12 (139 : Fin 154) = values6 (7 : Fin 8) + values7 (4 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (441 : Fin 455) (by
      change 1 + values12 (140 : Fin 154) = values6 (7 : Fin 8) + values7 (5 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (443 : Fin 455) (by
      change 1 + values12 (142 : Fin 154) = values6 (7 : Fin 8) + values7 (6 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (445 : Fin 455) (by
      change 1 + values12 (144 : Fin 154) = values6 (7 : Fin 8) + values7 (7 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (447 : Fin 455) (by
      change 1 + values12 (146 : Fin 154) = values6 (7 : Fin 8) + values7 (8 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (449 : Fin 455) (by
      change 1 + values12 (148 : Fin 154) = values6 (7 : Fin 8) + values7 (9 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (450 : Fin 455) (by
      change 1 + values12 (149 : Fin 154) = values6 (7 : Fin 8) + values7 (10 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (452 : Fin 455) (by
      change 1 + values12 (151 : Fin 154) = values6 (7 : Fin 8) + values7 (11 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
  next =>
    exact Exists.intro (454 : Fin 455) (by
      change 1 + values12 (153 : Fin 154) = values6 (7 : Fin 8) + values7 (12 : Fin 13)
      a158415_twelve_table <;> try rw [sqrt_four]
    )
theorem recursiveValueSet_fourteen_unary_subset_range :
    ((fun x : ℝ => Real.sqrt x) '' recursiveValueSet 13) ⊆ Set.range values14 := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  rw [recursiveValueSet_thirteen] at hy
  rcases hy with ⟨i, rfl⟩
  exact sqrt_values13_mem_range_values14 i

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
      rw [recursiveValueSet_eleven] at hb'
      simp only [Set.mem_singleton_iff] at ha
      rcases ha with rfl
      rcases hb' with ⟨i, rfl⟩
      exact one_add_values11_mem_range_values14 i
    · rw [recursiveValueSet_three] at ha
      have hb' : b ∈ recursiveValueSet 10 := by simpa using hb
      rw [recursiveValueSet_ten] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl
      · exact one_add_values10_mem_range_values14 i
      · exact two_add_values10_mem_range_values14 i
    · rw [recursiveValueSet_four] at ha
      have hb' : b ∈ recursiveValueSet 9 := by simpa using hb
      rw [recursiveValueSet_nine] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases hb' with ⟨i, rfl⟩
      rcases ha with rfl | rfl | rfl
      · exact one_add_values9_mem_range_values14 i
      · exact sqrt_two_add_values9_mem_range_values14 i
      · exact two_add_values9_mem_range_values14 i
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
        simpa [add_comm] using one_add_values9_mem_range_values14 i
      · change (Set.range values14) (values9 i + Real.sqrt 2)
        simpa [add_comm] using sqrt_two_add_values9_mem_range_values14 i
      · change (Set.range values14) (values9 i + 2)
        simpa [add_comm] using two_add_values9_mem_range_values14 i
    · rw [recursiveValueSet_ten] at ha
      have hb' : b ∈ recursiveValueSet 3 := by simpa using hb
      rw [recursiveValueSet_three] at hb'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl | rfl
      · change (Set.range values14) (values10 i + 1)
        simpa [add_comm] using one_add_values10_mem_range_values14 i
      · change (Set.range values14) (values10 i + 2)
        simpa [add_comm] using two_add_values10_mem_range_values14 i
    · rw [recursiveValueSet_eleven] at ha
      have hb' : b ∈ recursiveValueSet 2 := by simpa using hb
      rw [recursiveValueSet_two] at hb'
      simp only [Set.mem_singleton_iff] at hb'
      rcases ha with ⟨i, rfl⟩
      rcases hb' with rfl
      change (Set.range values14) (values11 i + 1)
      simpa [add_comm] using one_add_values11_mem_range_values14 i
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
