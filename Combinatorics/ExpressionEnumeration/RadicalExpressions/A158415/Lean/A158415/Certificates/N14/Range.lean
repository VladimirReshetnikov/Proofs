import A158415.Certificates.N14.Table

/-!
# Size-fourteen range certificates for OEIS A158415

This generated module contains the irreducible candidate-index certificates for
the size-14 representative table. Lower one-add and two-add families are derived
in Lean from padding monotonicity rather than duplicated here.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def sqrt_values13_mem_range_values14_indexNat : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 8
  | 9 => 9
  | 10 => 10
  | 11 => 11
  | 12 => 12
  | 13 => 13
  | 14 => 14
  | 15 => 15
  | 16 => 16
  | 17 => 17
  | 18 => 18
  | 19 => 19
  | 20 => 20
  | 21 => 21
  | 22 => 22
  | 23 => 23
  | 24 => 24
  | 25 => 25
  | 26 => 26
  | 27 => 27
  | 28 => 28
  | 29 => 29
  | 30 => 30
  | 31 => 31
  | 32 => 32
  | 33 => 33
  | 34 => 34
  | 35 => 35
  | 36 => 36
  | 37 => 37
  | 38 => 38
  | 39 => 39
  | 40 => 40
  | 41 => 41
  | 42 => 42
  | 43 => 43
  | 44 => 44
  | 45 => 45
  | 46 => 46
  | 47 => 47
  | 48 => 48
  | 49 => 49
  | 50 => 50
  | 51 => 51
  | 52 => 52
  | 53 => 53
  | 54 => 54
  | 55 => 55
  | 56 => 56
  | 57 => 57
  | 58 => 58
  | 59 => 59
  | 60 => 60
  | 61 => 61
  | 62 => 62
  | 63 => 63
  | 64 => 64
  | 65 => 65
  | 66 => 66
  | 67 => 67
  | 68 => 68
  | 69 => 69
  | 70 => 70
  | 71 => 71
  | 72 => 72
  | 73 => 73
  | 74 => 74
  | 75 => 75
  | 76 => 76
  | 77 => 77
  | 78 => 78
  | 79 => 79
  | 80 => 80
  | 81 => 81
  | 82 => 82
  | 83 => 83
  | 84 => 84
  | 85 => 85
  | 86 => 86
  | 87 => 87
  | 88 => 88
  | 89 => 89
  | 90 => 90
  | 91 => 91
  | 92 => 92
  | 93 => 93
  | 94 => 94
  | 95 => 95
  | 96 => 96
  | 97 => 97
  | 98 => 98
  | 99 => 99
  | 100 => 100
  | 101 => 101
  | 102 => 102
  | 103 => 103
  | 104 => 104
  | 105 => 105
  | 106 => 106
  | 107 => 107
  | 108 => 108
  | 109 => 109
  | 110 => 110
  | 111 => 111
  | 112 => 112
  | 113 => 113
  | 114 => 114
  | 115 => 115
  | 116 => 116
  | 117 => 117
  | 118 => 118
  | 119 => 119
  | 120 => 120
  | 121 => 121
  | 122 => 122
  | 123 => 123
  | 124 => 124
  | 125 => 125
  | 126 => 126
  | 127 => 127
  | 128 => 128
  | 129 => 129
  | 130 => 130
  | 131 => 131
  | 132 => 132
  | 133 => 133
  | 134 => 134
  | 135 => 135
  | 136 => 136
  | 137 => 137
  | 138 => 138
  | 139 => 139
  | 140 => 140
  | 141 => 141
  | 142 => 142
  | 143 => 143
  | 144 => 144
  | 145 => 145
  | 146 => 146
  | 147 => 147
  | 148 => 148
  | 149 => 149
  | 150 => 150
  | 151 => 151
  | 152 => 152
  | 153 => 153
  | 154 => 154
  | 155 => 155
  | 156 => 156
  | 157 => 157
  | 158 => 158
  | 159 => 159
  | 160 => 160
  | 161 => 161
  | 162 => 162
  | 163 => 163
  | 164 => 164
  | 165 => 165
  | 166 => 166
  | 167 => 167
  | 168 => 168
  | 169 => 169
  | 170 => 170
  | 171 => 171
  | 172 => 172
  | 173 => 173
  | 174 => 174
  | 175 => 175
  | 176 => 176
  | 177 => 177
  | 178 => 178
  | 179 => 179
  | 180 => 180
  | 181 => 181
  | 182 => 182
  | 183 => 183
  | 184 => 184
  | 185 => 185
  | 186 => 186
  | 187 => 187
  | 188 => 188
  | 189 => 189
  | 190 => 190
  | 191 => 191
  | 192 => 192
  | 193 => 193
  | 194 => 194
  | 195 => 195
  | 196 => 196
  | 197 => 197
  | 198 => 198
  | 199 => 199
  | 200 => 200
  | 201 => 201
  | 202 => 202
  | 203 => 203
  | 204 => 204
  | 205 => 205
  | 206 => 206
  | 207 => 207
  | 208 => 208
  | 209 => 209
  | 210 => 210
  | 211 => 211
  | 212 => 212
  | 213 => 213
  | 214 => 214
  | 215 => 215
  | 216 => 216
  | 217 => 217
  | 218 => 218
  | 219 => 219
  | 220 => 220
  | 221 => 221
  | 222 => 222
  | 223 => 223
  | 224 => 224
  | 225 => 225
  | 226 => 226
  | 227 => 227
  | 228 => 228
  | 229 => 229
  | 230 => 230
  | 231 => 231
  | 232 => 232
  | 233 => 233
  | 234 => 234
  | 235 => 235
  | 236 => 236
  | 237 => 237
  | 238 => 238
  | 239 => 239
  | 240 => 240
  | 241 => 241
  | 242 => 242
  | 243 => 243
  | 244 => 244
  | 245 => 245
  | 246 => 246
  | 247 => 247
  | 248 => 248
  | 249 => 249
  | 250 => 255
  | 251 => 259
  | 252 => 263
  | 253 => 265
  | 254 => 271
  | 255 => 276
  | 256 => 282
  | 257 => 288
  | 258 => 293
  | 259 => 302
  | 260 => 307
  | 261 => 313
  | 262 => 330
  | 263 => 355
  | _ => 0

def sqrt_values13_mem_range_values14_index (i : Fin 264) : Fin 455 :=
  Fin.ofNat 455 (sqrt_values13_mem_range_values14_indexNat i.1)

private theorem sqrt_values13_mem_range_values14_route_spec :
    forall i : Fin 264, values14RouteNat (sqrt_values13_mem_range_values14_index i).1 = Values14Route.sqrt13 i := by
  native_decide

theorem sqrt_values13_mem_range_values14_index_spec (i : Fin 264) :
    values14 (sqrt_values13_mem_range_values14_index i) = Real.sqrt (values13 i) := by
  change (values14RouteNat (sqrt_values13_mem_range_values14_index i).1).eval = Real.sqrt (values13 i)
  rw [sqrt_values13_mem_range_values14_route_spec i]
  rfl

theorem sqrt_values13_mem_range_values14 (i : Fin 264) :
    (Set.range values14) (Real.sqrt (values13 i)) := by
  exact ⟨sqrt_values13_mem_range_values14_index i, sqrt_values13_mem_range_values14_index_spec i⟩

def one_add_values12_mem_range_values14_indexNat : Nat -> Nat
  | 0 => 249
  | 1 => 250
  | 2 => 251
  | 3 => 252
  | 4 => 253
  | 5 => 254
  | 6 => 256
  | 7 => 257
  | 8 => 258
  | 9 => 260
  | 10 => 261
  | 11 => 262
  | 12 => 264
  | 13 => 266
  | 14 => 267
  | 15 => 268
  | 16 => 269
  | 17 => 270
  | 18 => 272
  | 19 => 273
  | 20 => 274
  | 21 => 275
  | 22 => 277
  | 23 => 278
  | 24 => 279
  | 25 => 280
  | 26 => 281
  | 27 => 284
  | 28 => 285
  | 29 => 286
  | 30 => 287
  | 31 => 290
  | 32 => 291
  | 33 => 292
  | 34 => 294
  | 35 => 295
  | 36 => 297
  | 37 => 298
  | 38 => 299
  | 39 => 301
  | 40 => 303
  | 41 => 304
  | 42 => 305
  | 43 => 306
  | 44 => 309
  | 45 => 310
  | 46 => 311
  | 47 => 312
  | 48 => 314
  | 49 => 316
  | 50 => 318
  | 51 => 320
  | 52 => 321
  | 53 => 322
  | 54 => 324
  | 55 => 327
  | 56 => 328
  | 57 => 329
  | 58 => 331
  | 59 => 333
  | 60 => 334
  | 61 => 336
  | 62 => 337
  | 63 => 338
  | 64 => 341
  | 65 => 343
  | 66 => 344
  | 67 => 346
  | 68 => 347
  | 69 => 348
  | 70 => 349
  | 71 => 351
  | 72 => 352
  | 73 => 356
  | 74 => 359
  | 75 => 360
  | 76 => 362
  | 77 => 364
  | 78 => 365
  | 79 => 366
  | 80 => 368
  | 81 => 369
  | 82 => 372
  | 83 => 374
  | 84 => 377
  | 85 => 378
  | 86 => 380
  | 87 => 381
  | 88 => 382
  | 89 => 383
  | 90 => 384
  | 91 => 385
  | 92 => 386
  | 93 => 388
  | 94 => 390
  | 95 => 391
  | 96 => 392
  | 97 => 393
  | 98 => 394
  | 99 => 396
  | 100 => 397
  | 101 => 398
  | 102 => 399
  | 103 => 400
  | 104 => 401
  | 105 => 403
  | 106 => 404
  | 107 => 406
  | 108 => 407
  | 109 => 408
  | 110 => 409
  | 111 => 410
  | 112 => 411
  | 113 => 412
  | 114 => 413
  | 115 => 415
  | 116 => 416
  | 117 => 417
  | 118 => 418
  | 119 => 419
  | 120 => 420
  | 121 => 421
  | 122 => 422
  | 123 => 423
  | 124 => 424
  | 125 => 425
  | 126 => 426
  | 127 => 427
  | 128 => 428
  | 129 => 429
  | 130 => 430
  | 131 => 431
  | 132 => 432
  | 133 => 433
  | 134 => 434
  | 135 => 435
  | 136 => 436
  | 137 => 437
  | 138 => 439
  | 139 => 440
  | 140 => 441
  | 141 => 442
  | 142 => 443
  | 143 => 444
  | 144 => 445
  | 145 => 446
  | 146 => 447
  | 147 => 448
  | 148 => 449
  | 149 => 450
  | 150 => 451
  | 151 => 452
  | 152 => 453
  | 153 => 454
  | _ => 0

def one_add_values12_mem_range_values14_index (i : Fin 154) : Fin 455 :=
  Fin.ofNat 455 (one_add_values12_mem_range_values14_indexNat i.1)

private theorem one_add_values12_mem_range_values14_route_spec :
    forall i : Fin 154, Not (i = (0 : Fin 154)) ->
      values14RouteNat (one_add_values12_mem_range_values14_index i).1 = Values14Route.oneAdd12 i := by
  native_decide

theorem one_add_values12_mem_range_values14_index_spec (i : Fin 154) :
    values14 (one_add_values12_mem_range_values14_index i) = 1 + values12 i := by
  by_cases h : i = (0 : Fin 154)
  · subst i
    change Real.sqrt (values13 (249 : Fin 264)) = 1 + values12 (0 : Fin 154)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  · change (values14RouteNat (one_add_values12_mem_range_values14_index i).1).eval = 1 + values12 i
    rw [one_add_values12_mem_range_values14_route_spec i h]
    rfl

theorem one_add_values12_mem_range_values14 (i : Fin 154) :
    (Set.range values14) (1 + values12 i) := by
  exact ⟨one_add_values12_mem_range_values14_index i, one_add_values12_mem_range_values14_index_spec i⟩

def sqrt_two_add_values9_mem_range_values14_indexNat : Nat -> Nat
  | 0 => 320
  | 1 => 323
  | 2 => 326
  | 3 => 332
  | 4 => 335
  | 5 => 339
  | 6 => 342
  | 7 => 345
  | 8 => 350
  | 9 => 353
  | 10 => 357
  | 11 => 361
  | 12 => 371
  | 13 => 373
  | 14 => 375
  | 15 => 379
  | 16 => 389
  | 17 => 395
  | 18 => 402
  | 19 => 409
  | 20 => 413
  | 21 => 416
  | 22 => 420
  | 23 => 423
  | 24 => 426
  | 25 => 429
  | 26 => 434
  | 27 => 438
  | 28 => 441
  | 29 => 444
  | 30 => 446
  | 31 => 450
  | 32 => 453
  | _ => 0

def sqrt_two_add_values9_mem_range_values14_index (i : Fin 33) : Fin 455 :=
  Fin.ofNat 455 (sqrt_two_add_values9_mem_range_values14_indexNat i.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem sqrt_two_add_values9_mem_range_values14_index_spec (i : Fin 33) :
    values14 (sqrt_two_add_values9_mem_range_values14_index i) = Real.sqrt 2 + values9 i := by
  fin_cases i
  next =>
    change 1 + values12 (51 : Fin 154) = Real.sqrt 2 + values9 (0 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next =>
    change 1 + values12 (110 : Fin 154) = Real.sqrt 2 + values9 (19 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (114 : Fin 154) = Real.sqrt 2 + values9 (20 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (116 : Fin 154) = Real.sqrt 2 + values9 (21 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = Real.sqrt 2 + values9 (22 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (123 : Fin 154) = Real.sqrt 2 + values9 (23 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (126 : Fin 154) = Real.sqrt 2 + values9 (24 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (129 : Fin 154) = Real.sqrt 2 + values9 (25 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (134 : Fin 154) = Real.sqrt 2 + values9 (26 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change 1 + values12 (140 : Fin 154) = Real.sqrt 2 + values9 (28 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (143 : Fin 154) = Real.sqrt 2 + values9 (29 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (145 : Fin 154) = Real.sqrt 2 + values9 (30 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = Real.sqrt 2 + values9 (31 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (152 : Fin 154) = Real.sqrt 2 + values9 (32 : Fin 33)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem sqrt_two_add_values9_mem_range_values14 (i : Fin 33) :
    (Set.range values14) (Real.sqrt 2 + values9 i) := by
  exact ⟨sqrt_two_add_values9_mem_range_values14_index i, sqrt_two_add_values9_mem_range_values14_index_spec i⟩

def values5_add_values8_mem_range_values14_indexNat : Nat -> Nat -> Nat
  | 0, 0 => 249
  | 0, 1 => 258
  | 0, 2 => 264
  | 0, 3 => 273
  | 0, 4 => 285
  | 0, 5 => 290
  | 0, 6 => 303
  | 0, 7 => 311
  | 0, 8 => 320
  | 0, 9 => 334
  | 0, 10 => 344
  | 0, 11 => 362
  | 0, 12 => 380
  | 0, 13 => 391
  | 0, 14 => 397
  | 0, 15 => 409
  | 0, 16 => 424
  | 0, 17 => 430
  | 0, 18 => 441
  | 0, 19 => 447
  | 1, 0 => 290
  | 1, 1 => 296
  | 1, 2 => 300
  | 1, 3 => 308
  | 1, 4 => 315
  | 1, 5 => 317
  | 1, 6 => 325
  | 1, 7 => 340
  | 1, 8 => 350
  | 1, 9 => 358
  | 1, 10 => 363
  | 1, 11 => 376
  | 1, 12 => 397
  | 1, 13 => 403
  | 1, 14 => 408
  | 1, 15 => 420
  | 1, 16 => 428
  | 1, 17 => 436
  | 1, 18 => 444
  | 1, 19 => 449
  | 2, 0 => 320
  | 2, 1 => 326
  | 2, 2 => 332
  | 2, 3 => 339
  | 2, 4 => 345
  | 2, 5 => 350
  | 2, 6 => 357
  | 2, 7 => 361
  | 2, 8 => 371
  | 2, 9 => 375
  | 2, 10 => 379
  | 2, 11 => 395
  | 2, 12 => 409
  | 2, 13 => 416
  | 2, 14 => 420
  | 2, 15 => 426
  | 2, 16 => 434
  | 2, 17 => 441
  | 2, 18 => 446
  | 2, 19 => 450
  | 3, 0 => 380
  | 3, 1 => 383
  | 3, 2 => 385
  | 3, 3 => 391
  | 3, 4 => 396
  | 3, 5 => 397
  | 3, 6 => 401
  | 3, 7 => 406
  | 3, 8 => 409
  | 3, 9 => 415
  | 3, 10 => 418
  | 3, 11 => 424
  | 3, 12 => 430
  | 3, 13 => 433
  | 3, 14 => 436
  | 3, 15 => 441
  | 3, 16 => 445
  | 3, 17 => 447
  | 3, 18 => 450
  | 3, 19 => 452
  | 4, 0 => 430
  | 4, 1 => 431
  | 4, 2 => 432
  | 4, 3 => 433
  | 4, 4 => 435
  | 4, 5 => 436
  | 4, 6 => 439
  | 4, 7 => 440
  | 4, 8 => 441
  | 4, 9 => 442
  | 4, 10 => 443
  | 4, 11 => 445
  | 4, 12 => 447
  | 4, 13 => 448
  | 4, 14 => 449
  | 4, 15 => 450
  | 4, 16 => 451
  | 4, 17 => 452
  | 4, 18 => 453
  | 4, 19 => 454
  | _, _ => 0

def values5_add_values8_mem_range_values14_index (i : Fin 5) (j : Fin 20) : Fin 455 :=
  Fin.ofNat 455 (values5_add_values8_mem_range_values14_indexNat i.1 j.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values5_add_values8_mem_range_values14_index_spec (i : Fin 5) (j : Fin 20) :
    values14 (values5_add_values8_mem_range_values14_index i j) = values5 i + values8 j := by
  fin_cases i <;> fin_cases j
  next =>
    change Real.sqrt (values13 (249 : Fin 264)) = values5 (0 : Fin 5) + values8 (0 : Fin 20)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (8 : Fin 154) = values5 (0 : Fin 5) + values8 (1 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (12 : Fin 154) = values5 (0 : Fin 5) + values8 (2 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (19 : Fin 154) = values5 (0 : Fin 5) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (28 : Fin 154) = values5 (0 : Fin 5) + values8 (4 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (31 : Fin 154) = values5 (0 : Fin 5) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (40 : Fin 154) = values5 (0 : Fin 5) + values8 (6 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (46 : Fin 154) = values5 (0 : Fin 5) + values8 (7 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (51 : Fin 154) = values5 (0 : Fin 5) + values8 (8 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (60 : Fin 154) = values5 (0 : Fin 5) + values8 (9 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (66 : Fin 154) = values5 (0 : Fin 5) + values8 (10 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (76 : Fin 154) = values5 (0 : Fin 5) + values8 (11 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (86 : Fin 154) = values5 (0 : Fin 5) + values8 (12 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (95 : Fin 154) = values5 (0 : Fin 5) + values8 (13 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (100 : Fin 154) = values5 (0 : Fin 5) + values8 (14 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values5 (0 : Fin 5) + values8 (15 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (124 : Fin 154) = values5 (0 : Fin 5) + values8 (16 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values5 (0 : Fin 5) + values8 (17 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values5 (0 : Fin 5) + values8 (18 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values5 (0 : Fin 5) + values8 (19 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (31 : Fin 154) = values5 (1 : Fin 5) + values8 (0 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next =>
    change Real.sqrt 2 + values9 (8 : Fin 33) = values5 (1 : Fin 5) + values8 (8 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next =>
    change 1 + values12 (100 : Fin 154) = values5 (1 : Fin 5) + values8 (12 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (105 : Fin 154) = values5 (1 : Fin 5) + values8 (13 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (109 : Fin 154) = values5 (1 : Fin 5) + values8 (14 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = values5 (1 : Fin 5) + values8 (15 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (128 : Fin 154) = values5 (1 : Fin 5) + values8 (16 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values5 (1 : Fin 5) + values8 (17 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (143 : Fin 154) = values5 (1 : Fin 5) + values8 (18 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (148 : Fin 154) = values5 (1 : Fin 5) + values8 (19 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (51 : Fin 154) = values5 (2 : Fin 5) + values8 (0 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (2 : Fin 33) = values5 (2 : Fin 5) + values8 (1 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (3 : Fin 33) = values5 (2 : Fin 5) + values8 (2 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (5 : Fin 33) = values5 (2 : Fin 5) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (7 : Fin 33) = values5 (2 : Fin 5) + values8 (4 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (8 : Fin 33) = values5 (2 : Fin 5) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (10 : Fin 33) = values5 (2 : Fin 5) + values8 (6 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (11 : Fin 33) = values5 (2 : Fin 5) + values8 (7 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (12 : Fin 33) = values5 (2 : Fin 5) + values8 (8 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (14 : Fin 33) = values5 (2 : Fin 5) + values8 (9 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (15 : Fin 33) = values5 (2 : Fin 5) + values8 (10 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (17 : Fin 33) = values5 (2 : Fin 5) + values8 (11 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values5 (2 : Fin 5) + values8 (12 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (116 : Fin 154) = values5 (2 : Fin 5) + values8 (13 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = values5 (2 : Fin 5) + values8 (14 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (126 : Fin 154) = values5 (2 : Fin 5) + values8 (15 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (134 : Fin 154) = values5 (2 : Fin 5) + values8 (16 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values5 (2 : Fin 5) + values8 (17 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (145 : Fin 154) = values5 (2 : Fin 5) + values8 (18 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values5 (2 : Fin 5) + values8 (19 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (86 : Fin 154) = values5 (3 : Fin 5) + values8 (0 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (89 : Fin 154) = values5 (3 : Fin 5) + values8 (1 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (91 : Fin 154) = values5 (3 : Fin 5) + values8 (2 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (95 : Fin 154) = values5 (3 : Fin 5) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (99 : Fin 154) = values5 (3 : Fin 5) + values8 (4 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (100 : Fin 154) = values5 (3 : Fin 5) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (104 : Fin 154) = values5 (3 : Fin 5) + values8 (6 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (107 : Fin 154) = values5 (3 : Fin 5) + values8 (7 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values5 (3 : Fin 5) + values8 (8 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (115 : Fin 154) = values5 (3 : Fin 5) + values8 (9 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (118 : Fin 154) = values5 (3 : Fin 5) + values8 (10 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (124 : Fin 154) = values5 (3 : Fin 5) + values8 (11 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values5 (3 : Fin 5) + values8 (12 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (133 : Fin 154) = values5 (3 : Fin 5) + values8 (13 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values5 (3 : Fin 5) + values8 (14 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values5 (3 : Fin 5) + values8 (15 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (144 : Fin 154) = values5 (3 : Fin 5) + values8 (16 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values5 (3 : Fin 5) + values8 (17 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values5 (3 : Fin 5) + values8 (18 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (151 : Fin 154) = values5 (3 : Fin 5) + values8 (19 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values5 (4 : Fin 5) + values8 (0 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (131 : Fin 154) = values5 (4 : Fin 5) + values8 (1 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (132 : Fin 154) = values5 (4 : Fin 5) + values8 (2 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (133 : Fin 154) = values5 (4 : Fin 5) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (135 : Fin 154) = values5 (4 : Fin 5) + values8 (4 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values5 (4 : Fin 5) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (138 : Fin 154) = values5 (4 : Fin 5) + values8 (6 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (139 : Fin 154) = values5 (4 : Fin 5) + values8 (7 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values5 (4 : Fin 5) + values8 (8 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (141 : Fin 154) = values5 (4 : Fin 5) + values8 (9 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (142 : Fin 154) = values5 (4 : Fin 5) + values8 (10 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (144 : Fin 154) = values5 (4 : Fin 5) + values8 (11 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values5 (4 : Fin 5) + values8 (12 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (147 : Fin 154) = values5 (4 : Fin 5) + values8 (13 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (148 : Fin 154) = values5 (4 : Fin 5) + values8 (14 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values5 (4 : Fin 5) + values8 (15 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (150 : Fin 154) = values5 (4 : Fin 5) + values8 (16 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (151 : Fin 154) = values5 (4 : Fin 5) + values8 (17 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (152 : Fin 154) = values5 (4 : Fin 5) + values8 (18 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (153 : Fin 154) = values5 (4 : Fin 5) + values8 (19 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem values5_add_values8_mem_range_values14 (i : Fin 5) (j : Fin 20) :
    (Set.range values14) (values5 i + values8 j) := by
  exact ⟨values5_add_values8_mem_range_values14_index i j, values5_add_values8_mem_range_values14_index_spec i j⟩

def values6_add_values7_mem_range_values14_indexNat : Nat -> Nat -> Nat
  | 0, 0 => 249
  | 0, 1 => 264
  | 0, 2 => 273
  | 0, 3 => 290
  | 0, 4 => 311
  | 0, 5 => 320
  | 0, 6 => 344
  | 0, 7 => 362
  | 0, 8 => 380
  | 0, 9 => 397
  | 0, 10 => 409
  | 0, 11 => 430
  | 0, 12 => 447
  | 1, 0 => 273
  | 1, 1 => 283
  | 1, 2 => 289
  | 1, 3 => 308
  | 1, 4 => 319
  | 1, 5 => 339
  | 1, 6 => 354
  | 1, 7 => 370
  | 1, 8 => 391
  | 1, 9 => 403
  | 1, 10 => 416
  | 1, 11 => 433
  | 1, 12 => 448
  | 2, 0 => 290
  | 2, 1 => 300
  | 2, 2 => 308
  | 2, 3 => 317
  | 2, 4 => 340
  | 2, 5 => 350
  | 2, 6 => 363
  | 2, 7 => 376
  | 2, 8 => 397
  | 2, 9 => 408
  | 2, 10 => 420
  | 2, 11 => 436
  | 2, 12 => 449
  | 3, 0 => 320
  | 3, 1 => 332
  | 3, 2 => 339
  | 3, 3 => 350
  | 3, 4 => 361
  | 3, 5 => 371
  | 3, 6 => 379
  | 3, 7 => 395
  | 3, 8 => 409
  | 3, 9 => 420
  | 3, 10 => 426
  | 3, 11 => 441
  | 3, 12 => 450
  | 4, 0 => 362
  | 4, 1 => 367
  | 4, 2 => 370
  | 4, 3 => 376
  | 4, 4 => 387
  | 4, 5 => 395
  | 4, 6 => 405
  | 4, 7 => 414
  | 4, 8 => 424
  | 4, 9 => 428
  | 4, 10 => 434
  | 4, 11 => 445
  | 4, 12 => 451
  | 5, 0 => 380
  | 5, 1 => 385
  | 5, 2 => 391
  | 5, 3 => 397
  | 5, 4 => 406
  | 5, 5 => 409
  | 5, 6 => 418
  | 5, 7 => 424
  | 5, 8 => 430
  | 5, 9 => 436
  | 5, 10 => 441
  | 5, 11 => 447
  | 5, 12 => 452
  | 6, 0 => 409
  | 6, 1 => 413
  | 6, 2 => 416
  | 6, 3 => 420
  | 6, 4 => 423
  | 6, 5 => 426
  | 6, 6 => 429
  | 6, 7 => 434
  | 6, 8 => 441
  | 6, 9 => 444
  | 6, 10 => 446
  | 6, 11 => 450
  | 6, 12 => 453
  | 7, 0 => 430
  | 7, 1 => 432
  | 7, 2 => 433
  | 7, 3 => 436
  | 7, 4 => 440
  | 7, 5 => 441
  | 7, 6 => 443
  | 7, 7 => 445
  | 7, 8 => 447
  | 7, 9 => 449
  | 7, 10 => 450
  | 7, 11 => 452
  | 7, 12 => 454
  | _, _ => 0

def values6_add_values7_mem_range_values14_index (i : Fin 8) (j : Fin 13) : Fin 455 :=
  Fin.ofNat 455 (values6_add_values7_mem_range_values14_indexNat i.1 j.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem values6_add_values7_mem_range_values14_index_spec (i : Fin 8) (j : Fin 13) :
    values14 (values6_add_values7_mem_range_values14_index i j) = values6 i + values7 j := by
  fin_cases i <;> fin_cases j
  next =>
    change Real.sqrt (values13 (249 : Fin 264)) = values6 (0 : Fin 8) + values7 (0 : Fin 13)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (12 : Fin 154) = values6 (0 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (19 : Fin 154) = values6 (0 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (31 : Fin 154) = values6 (0 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (46 : Fin 154) = values6 (0 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (51 : Fin 154) = values6 (0 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (66 : Fin 154) = values6 (0 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (76 : Fin 154) = values6 (0 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (86 : Fin 154) = values6 (0 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (100 : Fin 154) = values6 (0 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values6 (0 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values6 (0 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values6 (0 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (19 : Fin 154) = values6 (1 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change values5 (1 : Fin 5) + values8 (3 : Fin 20) = values6 (1 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change Real.sqrt 2 + values9 (5 : Fin 33) = values6 (1 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change 1 + values12 (95 : Fin 154) = values6 (1 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (105 : Fin 154) = values6 (1 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (116 : Fin 154) = values6 (1 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (133 : Fin 154) = values6 (1 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (147 : Fin 154) = values6 (1 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (31 : Fin 154) = values6 (2 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (2 : Fin 20) = values6 (2 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (3 : Fin 20) = values6 (2 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (5 : Fin 20) = values6 (2 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (7 : Fin 20) = values6 (2 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (8 : Fin 33) = values6 (2 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (10 : Fin 20) = values6 (2 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (11 : Fin 20) = values6 (2 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (100 : Fin 154) = values6 (2 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (109 : Fin 154) = values6 (2 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = values6 (2 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values6 (2 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (148 : Fin 154) = values6 (2 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (51 : Fin 154) = values6 (3 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (3 : Fin 33) = values6 (3 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (5 : Fin 33) = values6 (3 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (8 : Fin 33) = values6 (3 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (11 : Fin 33) = values6 (3 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (12 : Fin 33) = values6 (3 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (15 : Fin 33) = values6 (3 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values9 (17 : Fin 33) = values6 (3 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values6 (3 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = values6 (3 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (126 : Fin 154) = values6 (3 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values6 (3 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values6 (3 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (76 : Fin 154) = values6 (4 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values6 (1 : Fin 8) + values7 (7 : Fin 13) = values6 (4 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values8 (11 : Fin 20) = values6 (4 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change Real.sqrt 2 + values9 (17 : Fin 33) = values6 (4 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change 1 + values12 (124 : Fin 154) = values6 (4 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (128 : Fin 154) = values6 (4 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (134 : Fin 154) = values6 (4 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (144 : Fin 154) = values6 (4 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (150 : Fin 154) = values6 (4 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (86 : Fin 154) = values6 (5 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (91 : Fin 154) = values6 (5 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (95 : Fin 154) = values6 (5 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (100 : Fin 154) = values6 (5 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (107 : Fin 154) = values6 (5 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values6 (5 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (118 : Fin 154) = values6 (5 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (124 : Fin 154) = values6 (5 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values6 (5 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values6 (5 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values6 (5 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values6 (5 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (151 : Fin 154) = values6 (5 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (110 : Fin 154) = values6 (6 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (114 : Fin 154) = values6 (6 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (116 : Fin 154) = values6 (6 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (120 : Fin 154) = values6 (6 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (123 : Fin 154) = values6 (6 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (126 : Fin 154) = values6 (6 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (129 : Fin 154) = values6 (6 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (134 : Fin 154) = values6 (6 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values6 (6 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (143 : Fin 154) = values6 (6 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (145 : Fin 154) = values6 (6 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values6 (6 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (152 : Fin 154) = values6 (6 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (130 : Fin 154) = values6 (7 : Fin 8) + values7 (0 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (132 : Fin 154) = values6 (7 : Fin 8) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (133 : Fin 154) = values6 (7 : Fin 8) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (136 : Fin 154) = values6 (7 : Fin 8) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (139 : Fin 154) = values6 (7 : Fin 8) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (140 : Fin 154) = values6 (7 : Fin 8) + values7 (5 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (142 : Fin 154) = values6 (7 : Fin 8) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (144 : Fin 154) = values6 (7 : Fin 8) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (146 : Fin 154) = values6 (7 : Fin 8) + values7 (8 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (148 : Fin 154) = values6 (7 : Fin 8) + values7 (9 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (149 : Fin 154) = values6 (7 : Fin 8) + values7 (10 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (151 : Fin 154) = values6 (7 : Fin 8) + values7 (11 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values12 (153 : Fin 154) = values6 (7 : Fin 8) + values7 (12 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem values6_add_values7_mem_range_values14 (i : Fin 8) (j : Fin 13) :
    (Set.range values14) (values6 i + values7 j) := by
  exact ⟨values6_add_values7_mem_range_values14_index i j, values6_add_values7_mem_range_values14_index_spec i j⟩

end Expr
end A158415
end LeanProofs
