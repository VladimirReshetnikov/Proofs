import A158415.Certificates.N13.Thirteen

/-!
# Size-fourteen representative table for OEIS A158415

This module records the 455 exact representatives discovered for size 14
and proves that each table entry belongs to the recursive value set.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
inductive Values14Route where
  | sqrt13 (i : Fin 264)
  | oneAdd12 (i : Fin 154)
  | sqrtTwoAdd9 (i : Fin 33)
  | add5_8 (i : Fin 5) (j : Fin 20)
  | add6_7 (i : Fin 8) (j : Fin 13)
  deriving DecidableEq

namespace Values14Route

noncomputable def eval : Values14Route -> Real
  | sqrt13 i => Real.sqrt (values13 i)
  | oneAdd12 i => 1 + values12 i
  | sqrtTwoAdd9 i => Real.sqrt 2 + values9 i
  | add5_8 i j => values5 i + values8 j
  | add6_7 i j => values6 i + values7 j

end Values14Route

def values14RouteNat : Nat -> Values14Route
  | 0 => .sqrt13 (0 : Fin 264)
  | 1 => .sqrt13 (1 : Fin 264)
  | 2 => .sqrt13 (2 : Fin 264)
  | 3 => .sqrt13 (3 : Fin 264)
  | 4 => .sqrt13 (4 : Fin 264)
  | 5 => .sqrt13 (5 : Fin 264)
  | 6 => .sqrt13 (6 : Fin 264)
  | 7 => .sqrt13 (7 : Fin 264)
  | 8 => .sqrt13 (8 : Fin 264)
  | 9 => .sqrt13 (9 : Fin 264)
  | 10 => .sqrt13 (10 : Fin 264)
  | 11 => .sqrt13 (11 : Fin 264)
  | 12 => .sqrt13 (12 : Fin 264)
  | 13 => .sqrt13 (13 : Fin 264)
  | 14 => .sqrt13 (14 : Fin 264)
  | 15 => .sqrt13 (15 : Fin 264)
  | 16 => .sqrt13 (16 : Fin 264)
  | 17 => .sqrt13 (17 : Fin 264)
  | 18 => .sqrt13 (18 : Fin 264)
  | 19 => .sqrt13 (19 : Fin 264)
  | 20 => .sqrt13 (20 : Fin 264)
  | 21 => .sqrt13 (21 : Fin 264)
  | 22 => .sqrt13 (22 : Fin 264)
  | 23 => .sqrt13 (23 : Fin 264)
  | 24 => .sqrt13 (24 : Fin 264)
  | 25 => .sqrt13 (25 : Fin 264)
  | 26 => .sqrt13 (26 : Fin 264)
  | 27 => .sqrt13 (27 : Fin 264)
  | 28 => .sqrt13 (28 : Fin 264)
  | 29 => .sqrt13 (29 : Fin 264)
  | 30 => .sqrt13 (30 : Fin 264)
  | 31 => .sqrt13 (31 : Fin 264)
  | 32 => .sqrt13 (32 : Fin 264)
  | 33 => .sqrt13 (33 : Fin 264)
  | 34 => .sqrt13 (34 : Fin 264)
  | 35 => .sqrt13 (35 : Fin 264)
  | 36 => .sqrt13 (36 : Fin 264)
  | 37 => .sqrt13 (37 : Fin 264)
  | 38 => .sqrt13 (38 : Fin 264)
  | 39 => .sqrt13 (39 : Fin 264)
  | 40 => .sqrt13 (40 : Fin 264)
  | 41 => .sqrt13 (41 : Fin 264)
  | 42 => .sqrt13 (42 : Fin 264)
  | 43 => .sqrt13 (43 : Fin 264)
  | 44 => .sqrt13 (44 : Fin 264)
  | 45 => .sqrt13 (45 : Fin 264)
  | 46 => .sqrt13 (46 : Fin 264)
  | 47 => .sqrt13 (47 : Fin 264)
  | 48 => .sqrt13 (48 : Fin 264)
  | 49 => .sqrt13 (49 : Fin 264)
  | 50 => .sqrt13 (50 : Fin 264)
  | 51 => .sqrt13 (51 : Fin 264)
  | 52 => .sqrt13 (52 : Fin 264)
  | 53 => .sqrt13 (53 : Fin 264)
  | 54 => .sqrt13 (54 : Fin 264)
  | 55 => .sqrt13 (55 : Fin 264)
  | 56 => .sqrt13 (56 : Fin 264)
  | 57 => .sqrt13 (57 : Fin 264)
  | 58 => .sqrt13 (58 : Fin 264)
  | 59 => .sqrt13 (59 : Fin 264)
  | 60 => .sqrt13 (60 : Fin 264)
  | 61 => .sqrt13 (61 : Fin 264)
  | 62 => .sqrt13 (62 : Fin 264)
  | 63 => .sqrt13 (63 : Fin 264)
  | 64 => .sqrt13 (64 : Fin 264)
  | 65 => .sqrt13 (65 : Fin 264)
  | 66 => .sqrt13 (66 : Fin 264)
  | 67 => .sqrt13 (67 : Fin 264)
  | 68 => .sqrt13 (68 : Fin 264)
  | 69 => .sqrt13 (69 : Fin 264)
  | 70 => .sqrt13 (70 : Fin 264)
  | 71 => .sqrt13 (71 : Fin 264)
  | 72 => .sqrt13 (72 : Fin 264)
  | 73 => .sqrt13 (73 : Fin 264)
  | 74 => .sqrt13 (74 : Fin 264)
  | 75 => .sqrt13 (75 : Fin 264)
  | 76 => .sqrt13 (76 : Fin 264)
  | 77 => .sqrt13 (77 : Fin 264)
  | 78 => .sqrt13 (78 : Fin 264)
  | 79 => .sqrt13 (79 : Fin 264)
  | 80 => .sqrt13 (80 : Fin 264)
  | 81 => .sqrt13 (81 : Fin 264)
  | 82 => .sqrt13 (82 : Fin 264)
  | 83 => .sqrt13 (83 : Fin 264)
  | 84 => .sqrt13 (84 : Fin 264)
  | 85 => .sqrt13 (85 : Fin 264)
  | 86 => .sqrt13 (86 : Fin 264)
  | 87 => .sqrt13 (87 : Fin 264)
  | 88 => .sqrt13 (88 : Fin 264)
  | 89 => .sqrt13 (89 : Fin 264)
  | 90 => .sqrt13 (90 : Fin 264)
  | 91 => .sqrt13 (91 : Fin 264)
  | 92 => .sqrt13 (92 : Fin 264)
  | 93 => .sqrt13 (93 : Fin 264)
  | 94 => .sqrt13 (94 : Fin 264)
  | 95 => .sqrt13 (95 : Fin 264)
  | 96 => .sqrt13 (96 : Fin 264)
  | 97 => .sqrt13 (97 : Fin 264)
  | 98 => .sqrt13 (98 : Fin 264)
  | 99 => .sqrt13 (99 : Fin 264)
  | 100 => .sqrt13 (100 : Fin 264)
  | 101 => .sqrt13 (101 : Fin 264)
  | 102 => .sqrt13 (102 : Fin 264)
  | 103 => .sqrt13 (103 : Fin 264)
  | 104 => .sqrt13 (104 : Fin 264)
  | 105 => .sqrt13 (105 : Fin 264)
  | 106 => .sqrt13 (106 : Fin 264)
  | 107 => .sqrt13 (107 : Fin 264)
  | 108 => .sqrt13 (108 : Fin 264)
  | 109 => .sqrt13 (109 : Fin 264)
  | 110 => .sqrt13 (110 : Fin 264)
  | 111 => .sqrt13 (111 : Fin 264)
  | 112 => .sqrt13 (112 : Fin 264)
  | 113 => .sqrt13 (113 : Fin 264)
  | 114 => .sqrt13 (114 : Fin 264)
  | 115 => .sqrt13 (115 : Fin 264)
  | 116 => .sqrt13 (116 : Fin 264)
  | 117 => .sqrt13 (117 : Fin 264)
  | 118 => .sqrt13 (118 : Fin 264)
  | 119 => .sqrt13 (119 : Fin 264)
  | 120 => .sqrt13 (120 : Fin 264)
  | 121 => .sqrt13 (121 : Fin 264)
  | 122 => .sqrt13 (122 : Fin 264)
  | 123 => .sqrt13 (123 : Fin 264)
  | 124 => .sqrt13 (124 : Fin 264)
  | 125 => .sqrt13 (125 : Fin 264)
  | 126 => .sqrt13 (126 : Fin 264)
  | 127 => .sqrt13 (127 : Fin 264)
  | 128 => .sqrt13 (128 : Fin 264)
  | 129 => .sqrt13 (129 : Fin 264)
  | 130 => .sqrt13 (130 : Fin 264)
  | 131 => .sqrt13 (131 : Fin 264)
  | 132 => .sqrt13 (132 : Fin 264)
  | 133 => .sqrt13 (133 : Fin 264)
  | 134 => .sqrt13 (134 : Fin 264)
  | 135 => .sqrt13 (135 : Fin 264)
  | 136 => .sqrt13 (136 : Fin 264)
  | 137 => .sqrt13 (137 : Fin 264)
  | 138 => .sqrt13 (138 : Fin 264)
  | 139 => .sqrt13 (139 : Fin 264)
  | 140 => .sqrt13 (140 : Fin 264)
  | 141 => .sqrt13 (141 : Fin 264)
  | 142 => .sqrt13 (142 : Fin 264)
  | 143 => .sqrt13 (143 : Fin 264)
  | 144 => .sqrt13 (144 : Fin 264)
  | 145 => .sqrt13 (145 : Fin 264)
  | 146 => .sqrt13 (146 : Fin 264)
  | 147 => .sqrt13 (147 : Fin 264)
  | 148 => .sqrt13 (148 : Fin 264)
  | 149 => .sqrt13 (149 : Fin 264)
  | 150 => .sqrt13 (150 : Fin 264)
  | 151 => .sqrt13 (151 : Fin 264)
  | 152 => .sqrt13 (152 : Fin 264)
  | 153 => .sqrt13 (153 : Fin 264)
  | 154 => .sqrt13 (154 : Fin 264)
  | 155 => .sqrt13 (155 : Fin 264)
  | 156 => .sqrt13 (156 : Fin 264)
  | 157 => .sqrt13 (157 : Fin 264)
  | 158 => .sqrt13 (158 : Fin 264)
  | 159 => .sqrt13 (159 : Fin 264)
  | 160 => .sqrt13 (160 : Fin 264)
  | 161 => .sqrt13 (161 : Fin 264)
  | 162 => .sqrt13 (162 : Fin 264)
  | 163 => .sqrt13 (163 : Fin 264)
  | 164 => .sqrt13 (164 : Fin 264)
  | 165 => .sqrt13 (165 : Fin 264)
  | 166 => .sqrt13 (166 : Fin 264)
  | 167 => .sqrt13 (167 : Fin 264)
  | 168 => .sqrt13 (168 : Fin 264)
  | 169 => .sqrt13 (169 : Fin 264)
  | 170 => .sqrt13 (170 : Fin 264)
  | 171 => .sqrt13 (171 : Fin 264)
  | 172 => .sqrt13 (172 : Fin 264)
  | 173 => .sqrt13 (173 : Fin 264)
  | 174 => .sqrt13 (174 : Fin 264)
  | 175 => .sqrt13 (175 : Fin 264)
  | 176 => .sqrt13 (176 : Fin 264)
  | 177 => .sqrt13 (177 : Fin 264)
  | 178 => .sqrt13 (178 : Fin 264)
  | 179 => .sqrt13 (179 : Fin 264)
  | 180 => .sqrt13 (180 : Fin 264)
  | 181 => .sqrt13 (181 : Fin 264)
  | 182 => .sqrt13 (182 : Fin 264)
  | 183 => .sqrt13 (183 : Fin 264)
  | 184 => .sqrt13 (184 : Fin 264)
  | 185 => .sqrt13 (185 : Fin 264)
  | 186 => .sqrt13 (186 : Fin 264)
  | 187 => .sqrt13 (187 : Fin 264)
  | 188 => .sqrt13 (188 : Fin 264)
  | 189 => .sqrt13 (189 : Fin 264)
  | 190 => .sqrt13 (190 : Fin 264)
  | 191 => .sqrt13 (191 : Fin 264)
  | 192 => .sqrt13 (192 : Fin 264)
  | 193 => .sqrt13 (193 : Fin 264)
  | 194 => .sqrt13 (194 : Fin 264)
  | 195 => .sqrt13 (195 : Fin 264)
  | 196 => .sqrt13 (196 : Fin 264)
  | 197 => .sqrt13 (197 : Fin 264)
  | 198 => .sqrt13 (198 : Fin 264)
  | 199 => .sqrt13 (199 : Fin 264)
  | 200 => .sqrt13 (200 : Fin 264)
  | 201 => .sqrt13 (201 : Fin 264)
  | 202 => .sqrt13 (202 : Fin 264)
  | 203 => .sqrt13 (203 : Fin 264)
  | 204 => .sqrt13 (204 : Fin 264)
  | 205 => .sqrt13 (205 : Fin 264)
  | 206 => .sqrt13 (206 : Fin 264)
  | 207 => .sqrt13 (207 : Fin 264)
  | 208 => .sqrt13 (208 : Fin 264)
  | 209 => .sqrt13 (209 : Fin 264)
  | 210 => .sqrt13 (210 : Fin 264)
  | 211 => .sqrt13 (211 : Fin 264)
  | 212 => .sqrt13 (212 : Fin 264)
  | 213 => .sqrt13 (213 : Fin 264)
  | 214 => .sqrt13 (214 : Fin 264)
  | 215 => .sqrt13 (215 : Fin 264)
  | 216 => .sqrt13 (216 : Fin 264)
  | 217 => .sqrt13 (217 : Fin 264)
  | 218 => .sqrt13 (218 : Fin 264)
  | 219 => .sqrt13 (219 : Fin 264)
  | 220 => .sqrt13 (220 : Fin 264)
  | 221 => .sqrt13 (221 : Fin 264)
  | 222 => .sqrt13 (222 : Fin 264)
  | 223 => .sqrt13 (223 : Fin 264)
  | 224 => .sqrt13 (224 : Fin 264)
  | 225 => .sqrt13 (225 : Fin 264)
  | 226 => .sqrt13 (226 : Fin 264)
  | 227 => .sqrt13 (227 : Fin 264)
  | 228 => .sqrt13 (228 : Fin 264)
  | 229 => .sqrt13 (229 : Fin 264)
  | 230 => .sqrt13 (230 : Fin 264)
  | 231 => .sqrt13 (231 : Fin 264)
  | 232 => .sqrt13 (232 : Fin 264)
  | 233 => .sqrt13 (233 : Fin 264)
  | 234 => .sqrt13 (234 : Fin 264)
  | 235 => .sqrt13 (235 : Fin 264)
  | 236 => .sqrt13 (236 : Fin 264)
  | 237 => .sqrt13 (237 : Fin 264)
  | 238 => .sqrt13 (238 : Fin 264)
  | 239 => .sqrt13 (239 : Fin 264)
  | 240 => .sqrt13 (240 : Fin 264)
  | 241 => .sqrt13 (241 : Fin 264)
  | 242 => .sqrt13 (242 : Fin 264)
  | 243 => .sqrt13 (243 : Fin 264)
  | 244 => .sqrt13 (244 : Fin 264)
  | 245 => .sqrt13 (245 : Fin 264)
  | 246 => .sqrt13 (246 : Fin 264)
  | 247 => .sqrt13 (247 : Fin 264)
  | 248 => .sqrt13 (248 : Fin 264)
  | 249 => .sqrt13 (249 : Fin 264)
  | 250 => .oneAdd12 (1 : Fin 154)
  | 251 => .oneAdd12 (2 : Fin 154)
  | 252 => .oneAdd12 (3 : Fin 154)
  | 253 => .oneAdd12 (4 : Fin 154)
  | 254 => .oneAdd12 (5 : Fin 154)
  | 255 => .sqrt13 (250 : Fin 264)
  | 256 => .oneAdd12 (6 : Fin 154)
  | 257 => .oneAdd12 (7 : Fin 154)
  | 258 => .oneAdd12 (8 : Fin 154)
  | 259 => .sqrt13 (251 : Fin 264)
  | 260 => .oneAdd12 (9 : Fin 154)
  | 261 => .oneAdd12 (10 : Fin 154)
  | 262 => .oneAdd12 (11 : Fin 154)
  | 263 => .sqrt13 (252 : Fin 264)
  | 264 => .oneAdd12 (12 : Fin 154)
  | 265 => .sqrt13 (253 : Fin 264)
  | 266 => .oneAdd12 (13 : Fin 154)
  | 267 => .oneAdd12 (14 : Fin 154)
  | 268 => .oneAdd12 (15 : Fin 154)
  | 269 => .oneAdd12 (16 : Fin 154)
  | 270 => .oneAdd12 (17 : Fin 154)
  | 271 => .sqrt13 (254 : Fin 264)
  | 272 => .oneAdd12 (18 : Fin 154)
  | 273 => .oneAdd12 (19 : Fin 154)
  | 274 => .oneAdd12 (20 : Fin 154)
  | 275 => .oneAdd12 (21 : Fin 154)
  | 276 => .sqrt13 (255 : Fin 264)
  | 277 => .oneAdd12 (22 : Fin 154)
  | 278 => .oneAdd12 (23 : Fin 154)
  | 279 => .oneAdd12 (24 : Fin 154)
  | 280 => .oneAdd12 (25 : Fin 154)
  | 281 => .oneAdd12 (26 : Fin 154)
  | 282 => .sqrt13 (256 : Fin 264)
  | 283 => .add6_7 (1 : Fin 8) (1 : Fin 13)
  | 284 => .oneAdd12 (27 : Fin 154)
  | 285 => .oneAdd12 (28 : Fin 154)
  | 286 => .oneAdd12 (29 : Fin 154)
  | 287 => .oneAdd12 (30 : Fin 154)
  | 288 => .sqrt13 (257 : Fin 264)
  | 289 => .add6_7 (1 : Fin 8) (2 : Fin 13)
  | 290 => .oneAdd12 (31 : Fin 154)
  | 291 => .oneAdd12 (32 : Fin 154)
  | 292 => .oneAdd12 (33 : Fin 154)
  | 293 => .sqrt13 (258 : Fin 264)
  | 294 => .oneAdd12 (34 : Fin 154)
  | 295 => .oneAdd12 (35 : Fin 154)
  | 296 => .add5_8 (1 : Fin 5) (1 : Fin 20)
  | 297 => .oneAdd12 (36 : Fin 154)
  | 298 => .oneAdd12 (37 : Fin 154)
  | 299 => .oneAdd12 (38 : Fin 154)
  | 300 => .add5_8 (1 : Fin 5) (2 : Fin 20)
  | 301 => .oneAdd12 (39 : Fin 154)
  | 302 => .sqrt13 (259 : Fin 264)
  | 303 => .oneAdd12 (40 : Fin 154)
  | 304 => .oneAdd12 (41 : Fin 154)
  | 305 => .oneAdd12 (42 : Fin 154)
  | 306 => .oneAdd12 (43 : Fin 154)
  | 307 => .sqrt13 (260 : Fin 264)
  | 308 => .add5_8 (1 : Fin 5) (3 : Fin 20)
  | 309 => .oneAdd12 (44 : Fin 154)
  | 310 => .oneAdd12 (45 : Fin 154)
  | 311 => .oneAdd12 (46 : Fin 154)
  | 312 => .oneAdd12 (47 : Fin 154)
  | 313 => .sqrt13 (261 : Fin 264)
  | 314 => .oneAdd12 (48 : Fin 154)
  | 315 => .add5_8 (1 : Fin 5) (4 : Fin 20)
  | 316 => .oneAdd12 (49 : Fin 154)
  | 317 => .add5_8 (1 : Fin 5) (5 : Fin 20)
  | 318 => .oneAdd12 (50 : Fin 154)
  | 319 => .add6_7 (1 : Fin 8) (4 : Fin 13)
  | 320 => .oneAdd12 (51 : Fin 154)
  | 321 => .oneAdd12 (52 : Fin 154)
  | 322 => .oneAdd12 (53 : Fin 154)
  | 323 => .sqrtTwoAdd9 (1 : Fin 33)
  | 324 => .oneAdd12 (54 : Fin 154)
  | 325 => .add5_8 (1 : Fin 5) (6 : Fin 20)
  | 326 => .sqrtTwoAdd9 (2 : Fin 33)
  | 327 => .oneAdd12 (55 : Fin 154)
  | 328 => .oneAdd12 (56 : Fin 154)
  | 329 => .oneAdd12 (57 : Fin 154)
  | 330 => .sqrt13 (262 : Fin 264)
  | 331 => .oneAdd12 (58 : Fin 154)
  | 332 => .sqrtTwoAdd9 (3 : Fin 33)
  | 333 => .oneAdd12 (59 : Fin 154)
  | 334 => .oneAdd12 (60 : Fin 154)
  | 335 => .sqrtTwoAdd9 (4 : Fin 33)
  | 336 => .oneAdd12 (61 : Fin 154)
  | 337 => .oneAdd12 (62 : Fin 154)
  | 338 => .oneAdd12 (63 : Fin 154)
  | 339 => .sqrtTwoAdd9 (5 : Fin 33)
  | 340 => .add5_8 (1 : Fin 5) (7 : Fin 20)
  | 341 => .oneAdd12 (64 : Fin 154)
  | 342 => .sqrtTwoAdd9 (6 : Fin 33)
  | 343 => .oneAdd12 (65 : Fin 154)
  | 344 => .oneAdd12 (66 : Fin 154)
  | 345 => .sqrtTwoAdd9 (7 : Fin 33)
  | 346 => .oneAdd12 (67 : Fin 154)
  | 347 => .oneAdd12 (68 : Fin 154)
  | 348 => .oneAdd12 (69 : Fin 154)
  | 349 => .oneAdd12 (70 : Fin 154)
  | 350 => .sqrtTwoAdd9 (8 : Fin 33)
  | 351 => .oneAdd12 (71 : Fin 154)
  | 352 => .oneAdd12 (72 : Fin 154)
  | 353 => .sqrtTwoAdd9 (9 : Fin 33)
  | 354 => .add6_7 (1 : Fin 8) (6 : Fin 13)
  | 355 => .sqrt13 (263 : Fin 264)
  | 356 => .oneAdd12 (73 : Fin 154)
  | 357 => .sqrtTwoAdd9 (10 : Fin 33)
  | 358 => .add5_8 (1 : Fin 5) (9 : Fin 20)
  | 359 => .oneAdd12 (74 : Fin 154)
  | 360 => .oneAdd12 (75 : Fin 154)
  | 361 => .sqrtTwoAdd9 (11 : Fin 33)
  | 362 => .oneAdd12 (76 : Fin 154)
  | 363 => .add5_8 (1 : Fin 5) (10 : Fin 20)
  | 364 => .oneAdd12 (77 : Fin 154)
  | 365 => .oneAdd12 (78 : Fin 154)
  | 366 => .oneAdd12 (79 : Fin 154)
  | 367 => .add6_7 (4 : Fin 8) (1 : Fin 13)
  | 368 => .oneAdd12 (80 : Fin 154)
  | 369 => .oneAdd12 (81 : Fin 154)
  | 370 => .add6_7 (1 : Fin 8) (7 : Fin 13)
  | 371 => .sqrtTwoAdd9 (12 : Fin 33)
  | 372 => .oneAdd12 (82 : Fin 154)
  | 373 => .sqrtTwoAdd9 (13 : Fin 33)
  | 374 => .oneAdd12 (83 : Fin 154)
  | 375 => .sqrtTwoAdd9 (14 : Fin 33)
  | 376 => .add5_8 (1 : Fin 5) (11 : Fin 20)
  | 377 => .oneAdd12 (84 : Fin 154)
  | 378 => .oneAdd12 (85 : Fin 154)
  | 379 => .sqrtTwoAdd9 (15 : Fin 33)
  | 380 => .oneAdd12 (86 : Fin 154)
  | 381 => .oneAdd12 (87 : Fin 154)
  | 382 => .oneAdd12 (88 : Fin 154)
  | 383 => .oneAdd12 (89 : Fin 154)
  | 384 => .oneAdd12 (90 : Fin 154)
  | 385 => .oneAdd12 (91 : Fin 154)
  | 386 => .oneAdd12 (92 : Fin 154)
  | 387 => .add6_7 (4 : Fin 8) (4 : Fin 13)
  | 388 => .oneAdd12 (93 : Fin 154)
  | 389 => .sqrtTwoAdd9 (16 : Fin 33)
  | 390 => .oneAdd12 (94 : Fin 154)
  | 391 => .oneAdd12 (95 : Fin 154)
  | 392 => .oneAdd12 (96 : Fin 154)
  | 393 => .oneAdd12 (97 : Fin 154)
  | 394 => .oneAdd12 (98 : Fin 154)
  | 395 => .sqrtTwoAdd9 (17 : Fin 33)
  | 396 => .oneAdd12 (99 : Fin 154)
  | 397 => .oneAdd12 (100 : Fin 154)
  | 398 => .oneAdd12 (101 : Fin 154)
  | 399 => .oneAdd12 (102 : Fin 154)
  | 400 => .oneAdd12 (103 : Fin 154)
  | 401 => .oneAdd12 (104 : Fin 154)
  | 402 => .sqrtTwoAdd9 (18 : Fin 33)
  | 403 => .oneAdd12 (105 : Fin 154)
  | 404 => .oneAdd12 (106 : Fin 154)
  | 405 => .add6_7 (4 : Fin 8) (6 : Fin 13)
  | 406 => .oneAdd12 (107 : Fin 154)
  | 407 => .oneAdd12 (108 : Fin 154)
  | 408 => .oneAdd12 (109 : Fin 154)
  | 409 => .oneAdd12 (110 : Fin 154)
  | 410 => .oneAdd12 (111 : Fin 154)
  | 411 => .oneAdd12 (112 : Fin 154)
  | 412 => .oneAdd12 (113 : Fin 154)
  | 413 => .oneAdd12 (114 : Fin 154)
  | 414 => .add6_7 (4 : Fin 8) (7 : Fin 13)
  | 415 => .oneAdd12 (115 : Fin 154)
  | 416 => .oneAdd12 (116 : Fin 154)
  | 417 => .oneAdd12 (117 : Fin 154)
  | 418 => .oneAdd12 (118 : Fin 154)
  | 419 => .oneAdd12 (119 : Fin 154)
  | 420 => .oneAdd12 (120 : Fin 154)
  | 421 => .oneAdd12 (121 : Fin 154)
  | 422 => .oneAdd12 (122 : Fin 154)
  | 423 => .oneAdd12 (123 : Fin 154)
  | 424 => .oneAdd12 (124 : Fin 154)
  | 425 => .oneAdd12 (125 : Fin 154)
  | 426 => .oneAdd12 (126 : Fin 154)
  | 427 => .oneAdd12 (127 : Fin 154)
  | 428 => .oneAdd12 (128 : Fin 154)
  | 429 => .oneAdd12 (129 : Fin 154)
  | 430 => .oneAdd12 (130 : Fin 154)
  | 431 => .oneAdd12 (131 : Fin 154)
  | 432 => .oneAdd12 (132 : Fin 154)
  | 433 => .oneAdd12 (133 : Fin 154)
  | 434 => .oneAdd12 (134 : Fin 154)
  | 435 => .oneAdd12 (135 : Fin 154)
  | 436 => .oneAdd12 (136 : Fin 154)
  | 437 => .oneAdd12 (137 : Fin 154)
  | 438 => .sqrtTwoAdd9 (27 : Fin 33)
  | 439 => .oneAdd12 (138 : Fin 154)
  | 440 => .oneAdd12 (139 : Fin 154)
  | 441 => .oneAdd12 (140 : Fin 154)
  | 442 => .oneAdd12 (141 : Fin 154)
  | 443 => .oneAdd12 (142 : Fin 154)
  | 444 => .oneAdd12 (143 : Fin 154)
  | 445 => .oneAdd12 (144 : Fin 154)
  | 446 => .oneAdd12 (145 : Fin 154)
  | 447 => .oneAdd12 (146 : Fin 154)
  | 448 => .oneAdd12 (147 : Fin 154)
  | 449 => .oneAdd12 (148 : Fin 154)
  | 450 => .oneAdd12 (149 : Fin 154)
  | 451 => .oneAdd12 (150 : Fin 154)
  | 452 => .oneAdd12 (151 : Fin 154)
  | 453 => .oneAdd12 (152 : Fin 154)
  | 454 => .oneAdd12 (153 : Fin 154)
  | _ => .sqrt13 (0 : Fin 264)

noncomputable def values14 (i : Fin 455) : Real :=
  (values14RouteNat i.1).eval

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

/-!
Generated route membership proof for the size-14 table.
Regenerate with:
  wolfram -script Combinatorics/ExpressionEnumeration/RadicalExpressions/A158415/Support/Wolfram/generate-a158415-data.wl 14 numeric-lean-membership
-/

namespace Values14Route

theorem eval_mem_recursiveValueSet_fourteen (route : Values14Route) :
    route.eval ∈ recursiveValueSet 14 := by
  cases route with
  | sqrt13 i => exact sqrt_values13_mem_recursiveValueSet_fourteen i
  | oneAdd12 i => exact one_add_values12_mem_recursiveValueSet_fourteen i
  | sqrtTwoAdd9 i => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen i
  | add5_8 i j => exact values5_add_values8_mem_recursiveValueSet_fourteen i j
  | add6_7 i j => exact values6_add_values7_mem_recursiveValueSet_fourteen i j

end Values14Route

theorem values14_mem_recursiveValueSet (i : Fin 455) :
    values14 i ∈ recursiveValueSet 14 := by
  change (values14RouteNat i.1).eval ∈ recursiveValueSet 14
  exact Values14Route.eval_mem_recursiveValueSet_fourteen (values14RouteNat i.1)

theorem values14_range_subset_recursiveValueSet_fourteen :
    Set.range values14 ⊆ recursiveValueSet 14 := by
  intro x hx
  rcases hx with ⟨i, rfl⟩
  exact values14_mem_recursiveValueSet i

end Expr
end A158415
end LeanProofs
