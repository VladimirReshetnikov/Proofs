import A158415.Certificates.N14.Intervals

/-!
# Size-fourteen ordering proof for OEIS A158415

This module proves that the size-14 representative table is strictly ordered
and therefore has exactly 455 distinct values.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values13_nonneg (i : Fin 264) : (0 : Real) <= values13 i := by
  have h0 : (0 : Real) <= values13 (0 : Fin 264) := by
    change (0 : Real) <= Real.sqrt (values12 (0 : Fin 154))
    exact Real.sqrt_nonneg _
  exact h0.trans (values13_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values13_strictMono :
    StrictMono fun i : Fin 264 => Real.sqrt (values13 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values13_nonneg i) (values13_strictMono hij)

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
    exact add_lt_add_right
      (values12_strictMono (by decide : (1 : Fin 154) < (2 : Fin 154))) 1
  next =>
    change 1 + values12 (2 : Fin 154) < 1 + values12 (3 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (2 : Fin 154) < (3 : Fin 154))) 1
  next =>
    change 1 + values12 (3 : Fin 154) < 1 + values12 (4 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (3 : Fin 154) < (4 : Fin 154))) 1
  next =>
    change 1 + values12 (4 : Fin 154) < 1 + values12 (5 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (4 : Fin 154) < (5 : Fin 154))) 1
  next => exact values14_special_254
  next => exact values14_special_255
  next =>
    change 1 + values12 (6 : Fin 154) < 1 + values12 (7 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (6 : Fin 154) < (7 : Fin 154))) 1
  next =>
    change 1 + values12 (7 : Fin 154) < 1 + values12 (8 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (7 : Fin 154) < (8 : Fin 154))) 1
  next => exact values14_special_258
  next => exact values14_special_259
  next =>
    change 1 + values12 (9 : Fin 154) < 1 + values12 (10 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (9 : Fin 154) < (10 : Fin 154))) 1
  next =>
    change 1 + values12 (10 : Fin 154) < 1 + values12 (11 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (10 : Fin 154) < (11 : Fin 154))) 1
  next => exact values14_special_262
  next => exact values14_special_263
  next => exact values14_special_264
  next => exact values14_special_265
  next =>
    change 1 + values12 (13 : Fin 154) < 1 + values12 (14 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (13 : Fin 154) < (14 : Fin 154))) 1
  next =>
    change 1 + values12 (14 : Fin 154) < 1 + values12 (15 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (14 : Fin 154) < (15 : Fin 154))) 1
  next =>
    change 1 + values12 (15 : Fin 154) < 1 + values12 (16 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (15 : Fin 154) < (16 : Fin 154))) 1
  next =>
    change 1 + values12 (16 : Fin 154) < 1 + values12 (17 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (16 : Fin 154) < (17 : Fin 154))) 1
  next => exact values14_special_270
  next => exact values14_special_271
  next =>
    change 1 + values12 (18 : Fin 154) < 1 + values12 (19 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (18 : Fin 154) < (19 : Fin 154))) 1
  next =>
    change 1 + values12 (19 : Fin 154) < 1 + values12 (20 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (19 : Fin 154) < (20 : Fin 154))) 1
  next =>
    change 1 + values12 (20 : Fin 154) < 1 + values12 (21 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (20 : Fin 154) < (21 : Fin 154))) 1
  next => exact values14_special_275
  next => exact values14_special_276
  next =>
    change 1 + values12 (22 : Fin 154) < 1 + values12 (23 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (22 : Fin 154) < (23 : Fin 154))) 1
  next =>
    change 1 + values12 (23 : Fin 154) < 1 + values12 (24 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (23 : Fin 154) < (24 : Fin 154))) 1
  next =>
    change 1 + values12 (24 : Fin 154) < 1 + values12 (25 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (24 : Fin 154) < (25 : Fin 154))) 1
  next =>
    change 1 + values12 (25 : Fin 154) < 1 + values12 (26 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (25 : Fin 154) < (26 : Fin 154))) 1
  next => exact values14_special_281
  next => exact values14_special_282
  next => exact values14_special_283
  next =>
    change 1 + values12 (27 : Fin 154) < 1 + values12 (28 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (27 : Fin 154) < (28 : Fin 154))) 1
  next =>
    change 1 + values12 (28 : Fin 154) < 1 + values12 (29 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (28 : Fin 154) < (29 : Fin 154))) 1
  next =>
    change 1 + values12 (29 : Fin 154) < 1 + values12 (30 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (29 : Fin 154) < (30 : Fin 154))) 1
  next => exact values14_special_287
  next => exact values14_special_288
  next => exact values14_special_289
  next =>
    change 1 + values12 (31 : Fin 154) < 1 + values12 (32 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (31 : Fin 154) < (32 : Fin 154))) 1
  next =>
    change 1 + values12 (32 : Fin 154) < 1 + values12 (33 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (32 : Fin 154) < (33 : Fin 154))) 1
  next => exact values14_special_292
  next => exact values14_special_293
  next =>
    change 1 + values12 (34 : Fin 154) < 1 + values12 (35 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (34 : Fin 154) < (35 : Fin 154))) 1
  next => exact values14_special_295
  next => exact values14_special_296
  next =>
    change 1 + values12 (36 : Fin 154) < 1 + values12 (37 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (36 : Fin 154) < (37 : Fin 154))) 1
  next =>
    change 1 + values12 (37 : Fin 154) < 1 + values12 (38 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (37 : Fin 154) < (38 : Fin 154))) 1
  next => exact values14_special_299
  next => exact values14_special_300
  next => exact values14_special_301
  next => exact values14_special_302
  next =>
    change 1 + values12 (40 : Fin 154) < 1 + values12 (41 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (40 : Fin 154) < (41 : Fin 154))) 1
  next =>
    change 1 + values12 (41 : Fin 154) < 1 + values12 (42 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (41 : Fin 154) < (42 : Fin 154))) 1
  next =>
    change 1 + values12 (42 : Fin 154) < 1 + values12 (43 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (42 : Fin 154) < (43 : Fin 154))) 1
  next => exact values14_special_306
  next => exact values14_special_307
  next => exact values14_special_308
  next =>
    change 1 + values12 (44 : Fin 154) < 1 + values12 (45 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (44 : Fin 154) < (45 : Fin 154))) 1
  next =>
    change 1 + values12 (45 : Fin 154) < 1 + values12 (46 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (45 : Fin 154) < (46 : Fin 154))) 1
  next =>
    change 1 + values12 (46 : Fin 154) < 1 + values12 (47 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (46 : Fin 154) < (47 : Fin 154))) 1
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
    exact add_lt_add_right
      (values12_strictMono (by decide : (51 : Fin 154) < (52 : Fin 154))) 1
  next =>
    change 1 + values12 (52 : Fin 154) < 1 + values12 (53 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (52 : Fin 154) < (53 : Fin 154))) 1
  next => exact values14_special_322
  next => exact values14_special_323
  next => exact values14_special_324
  next => exact values14_special_325
  next => exact values14_special_326
  next =>
    change 1 + values12 (55 : Fin 154) < 1 + values12 (56 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (55 : Fin 154) < (56 : Fin 154))) 1
  next =>
    change 1 + values12 (56 : Fin 154) < 1 + values12 (57 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (56 : Fin 154) < (57 : Fin 154))) 1
  next => exact values14_special_329
  next => exact values14_special_330
  next => exact values14_special_331
  next => exact values14_special_332
  next =>
    change 1 + values12 (59 : Fin 154) < 1 + values12 (60 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (59 : Fin 154) < (60 : Fin 154))) 1
  next => exact values14_special_334
  next => exact values14_special_335
  next =>
    change 1 + values12 (61 : Fin 154) < 1 + values12 (62 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (61 : Fin 154) < (62 : Fin 154))) 1
  next =>
    change 1 + values12 (62 : Fin 154) < 1 + values12 (63 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (62 : Fin 154) < (63 : Fin 154))) 1
  next => exact values14_special_338
  next => exact values14_special_339
  next => exact values14_special_340
  next => exact values14_special_341
  next => exact values14_special_342
  next =>
    change 1 + values12 (65 : Fin 154) < 1 + values12 (66 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (65 : Fin 154) < (66 : Fin 154))) 1
  next => exact values14_special_344
  next => exact values14_special_345
  next =>
    change 1 + values12 (67 : Fin 154) < 1 + values12 (68 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (67 : Fin 154) < (68 : Fin 154))) 1
  next =>
    change 1 + values12 (68 : Fin 154) < 1 + values12 (69 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (68 : Fin 154) < (69 : Fin 154))) 1
  next =>
    change 1 + values12 (69 : Fin 154) < 1 + values12 (70 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (69 : Fin 154) < (70 : Fin 154))) 1
  next => exact values14_special_349
  next => exact values14_special_350
  next =>
    change 1 + values12 (71 : Fin 154) < 1 + values12 (72 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (71 : Fin 154) < (72 : Fin 154))) 1
  next => exact values14_special_352
  next => exact values14_special_353
  next => exact values14_special_354
  next => exact values14_special_355
  next => exact values14_special_356
  next => exact values14_special_357
  next => exact values14_special_358
  next =>
    change 1 + values12 (74 : Fin 154) < 1 + values12 (75 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (74 : Fin 154) < (75 : Fin 154))) 1
  next => exact values14_special_360
  next => exact values14_special_361
  next => exact values14_special_362
  next => exact values14_special_363
  next =>
    change 1 + values12 (77 : Fin 154) < 1 + values12 (78 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (77 : Fin 154) < (78 : Fin 154))) 1
  next =>
    change 1 + values12 (78 : Fin 154) < 1 + values12 (79 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (78 : Fin 154) < (79 : Fin 154))) 1
  next => exact values14_special_366
  next => exact values14_special_367
  next =>
    change 1 + values12 (80 : Fin 154) < 1 + values12 (81 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (80 : Fin 154) < (81 : Fin 154))) 1
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
    exact add_lt_add_right
      (values12_strictMono (by decide : (84 : Fin 154) < (85 : Fin 154))) 1
  next => exact values14_special_378
  next => exact values14_special_379
  next =>
    change 1 + values12 (86 : Fin 154) < 1 + values12 (87 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (86 : Fin 154) < (87 : Fin 154))) 1
  next =>
    change 1 + values12 (87 : Fin 154) < 1 + values12 (88 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (87 : Fin 154) < (88 : Fin 154))) 1
  next =>
    change 1 + values12 (88 : Fin 154) < 1 + values12 (89 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (88 : Fin 154) < (89 : Fin 154))) 1
  next =>
    change 1 + values12 (89 : Fin 154) < 1 + values12 (90 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (89 : Fin 154) < (90 : Fin 154))) 1
  next =>
    change 1 + values12 (90 : Fin 154) < 1 + values12 (91 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (90 : Fin 154) < (91 : Fin 154))) 1
  next =>
    change 1 + values12 (91 : Fin 154) < 1 + values12 (92 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (91 : Fin 154) < (92 : Fin 154))) 1
  next => exact values14_special_386
  next => exact values14_special_387
  next => exact values14_special_388
  next => exact values14_special_389
  next =>
    change 1 + values12 (94 : Fin 154) < 1 + values12 (95 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (94 : Fin 154) < (95 : Fin 154))) 1
  next =>
    change 1 + values12 (95 : Fin 154) < 1 + values12 (96 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (95 : Fin 154) < (96 : Fin 154))) 1
  next =>
    change 1 + values12 (96 : Fin 154) < 1 + values12 (97 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (96 : Fin 154) < (97 : Fin 154))) 1
  next =>
    change 1 + values12 (97 : Fin 154) < 1 + values12 (98 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (97 : Fin 154) < (98 : Fin 154))) 1
  next => exact values14_special_394
  next => exact values14_special_395
  next =>
    change 1 + values12 (99 : Fin 154) < 1 + values12 (100 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (99 : Fin 154) < (100 : Fin 154))) 1
  next =>
    change 1 + values12 (100 : Fin 154) < 1 + values12 (101 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (100 : Fin 154) < (101 : Fin 154))) 1
  next =>
    change 1 + values12 (101 : Fin 154) < 1 + values12 (102 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (101 : Fin 154) < (102 : Fin 154))) 1
  next =>
    change 1 + values12 (102 : Fin 154) < 1 + values12 (103 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (102 : Fin 154) < (103 : Fin 154))) 1
  next =>
    change 1 + values12 (103 : Fin 154) < 1 + values12 (104 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (103 : Fin 154) < (104 : Fin 154))) 1
  next => exact values14_special_401
  next => exact values14_special_402
  next =>
    change 1 + values12 (105 : Fin 154) < 1 + values12 (106 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (105 : Fin 154) < (106 : Fin 154))) 1
  next => exact values14_special_404
  next => exact values14_special_405
  next =>
    change 1 + values12 (107 : Fin 154) < 1 + values12 (108 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (107 : Fin 154) < (108 : Fin 154))) 1
  next =>
    change 1 + values12 (108 : Fin 154) < 1 + values12 (109 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (108 : Fin 154) < (109 : Fin 154))) 1
  next =>
    change 1 + values12 (109 : Fin 154) < 1 + values12 (110 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (109 : Fin 154) < (110 : Fin 154))) 1
  next =>
    change 1 + values12 (110 : Fin 154) < 1 + values12 (111 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (110 : Fin 154) < (111 : Fin 154))) 1
  next =>
    change 1 + values12 (111 : Fin 154) < 1 + values12 (112 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (111 : Fin 154) < (112 : Fin 154))) 1
  next =>
    change 1 + values12 (112 : Fin 154) < 1 + values12 (113 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (112 : Fin 154) < (113 : Fin 154))) 1
  next =>
    change 1 + values12 (113 : Fin 154) < 1 + values12 (114 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (113 : Fin 154) < (114 : Fin 154))) 1
  next => exact values14_special_413
  next => exact values14_special_414
  next =>
    change 1 + values12 (115 : Fin 154) < 1 + values12 (116 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (115 : Fin 154) < (116 : Fin 154))) 1
  next =>
    change 1 + values12 (116 : Fin 154) < 1 + values12 (117 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (116 : Fin 154) < (117 : Fin 154))) 1
  next =>
    change 1 + values12 (117 : Fin 154) < 1 + values12 (118 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (117 : Fin 154) < (118 : Fin 154))) 1
  next =>
    change 1 + values12 (118 : Fin 154) < 1 + values12 (119 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (118 : Fin 154) < (119 : Fin 154))) 1
  next =>
    change 1 + values12 (119 : Fin 154) < 1 + values12 (120 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (119 : Fin 154) < (120 : Fin 154))) 1
  next =>
    change 1 + values12 (120 : Fin 154) < 1 + values12 (121 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (120 : Fin 154) < (121 : Fin 154))) 1
  next =>
    change 1 + values12 (121 : Fin 154) < 1 + values12 (122 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (121 : Fin 154) < (122 : Fin 154))) 1
  next =>
    change 1 + values12 (122 : Fin 154) < 1 + values12 (123 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (122 : Fin 154) < (123 : Fin 154))) 1
  next =>
    change 1 + values12 (123 : Fin 154) < 1 + values12 (124 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (123 : Fin 154) < (124 : Fin 154))) 1
  next =>
    change 1 + values12 (124 : Fin 154) < 1 + values12 (125 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (124 : Fin 154) < (125 : Fin 154))) 1
  next =>
    change 1 + values12 (125 : Fin 154) < 1 + values12 (126 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (125 : Fin 154) < (126 : Fin 154))) 1
  next =>
    change 1 + values12 (126 : Fin 154) < 1 + values12 (127 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (126 : Fin 154) < (127 : Fin 154))) 1
  next =>
    change 1 + values12 (127 : Fin 154) < 1 + values12 (128 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (127 : Fin 154) < (128 : Fin 154))) 1
  next =>
    change 1 + values12 (128 : Fin 154) < 1 + values12 (129 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (128 : Fin 154) < (129 : Fin 154))) 1
  next =>
    change 1 + values12 (129 : Fin 154) < 1 + values12 (130 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (129 : Fin 154) < (130 : Fin 154))) 1
  next =>
    change 1 + values12 (130 : Fin 154) < 1 + values12 (131 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (130 : Fin 154) < (131 : Fin 154))) 1
  next =>
    change 1 + values12 (131 : Fin 154) < 1 + values12 (132 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (131 : Fin 154) < (132 : Fin 154))) 1
  next =>
    change 1 + values12 (132 : Fin 154) < 1 + values12 (133 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (132 : Fin 154) < (133 : Fin 154))) 1
  next =>
    change 1 + values12 (133 : Fin 154) < 1 + values12 (134 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (133 : Fin 154) < (134 : Fin 154))) 1
  next =>
    change 1 + values12 (134 : Fin 154) < 1 + values12 (135 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (134 : Fin 154) < (135 : Fin 154))) 1
  next =>
    change 1 + values12 (135 : Fin 154) < 1 + values12 (136 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (135 : Fin 154) < (136 : Fin 154))) 1
  next =>
    change 1 + values12 (136 : Fin 154) < 1 + values12 (137 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (136 : Fin 154) < (137 : Fin 154))) 1
  next => exact values14_special_437
  next => exact values14_special_438
  next =>
    change 1 + values12 (138 : Fin 154) < 1 + values12 (139 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (138 : Fin 154) < (139 : Fin 154))) 1
  next =>
    change 1 + values12 (139 : Fin 154) < 1 + values12 (140 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (139 : Fin 154) < (140 : Fin 154))) 1
  next =>
    change 1 + values12 (140 : Fin 154) < 1 + values12 (141 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (140 : Fin 154) < (141 : Fin 154))) 1
  next =>
    change 1 + values12 (141 : Fin 154) < 1 + values12 (142 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (141 : Fin 154) < (142 : Fin 154))) 1
  next =>
    change 1 + values12 (142 : Fin 154) < 1 + values12 (143 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (142 : Fin 154) < (143 : Fin 154))) 1
  next =>
    change 1 + values12 (143 : Fin 154) < 1 + values12 (144 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (143 : Fin 154) < (144 : Fin 154))) 1
  next =>
    change 1 + values12 (144 : Fin 154) < 1 + values12 (145 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (144 : Fin 154) < (145 : Fin 154))) 1
  next =>
    change 1 + values12 (145 : Fin 154) < 1 + values12 (146 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (145 : Fin 154) < (146 : Fin 154))) 1
  next =>
    change 1 + values12 (146 : Fin 154) < 1 + values12 (147 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (146 : Fin 154) < (147 : Fin 154))) 1
  next =>
    change 1 + values12 (147 : Fin 154) < 1 + values12 (148 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (147 : Fin 154) < (148 : Fin 154))) 1
  next =>
    change 1 + values12 (148 : Fin 154) < 1 + values12 (149 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (148 : Fin 154) < (149 : Fin 154))) 1
  next =>
    change 1 + values12 (149 : Fin 154) < 1 + values12 (150 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (149 : Fin 154) < (150 : Fin 154))) 1
  next =>
    change 1 + values12 (150 : Fin 154) < 1 + values12 (151 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (150 : Fin 154) < (151 : Fin 154))) 1
  next =>
    change 1 + values12 (151 : Fin 154) < 1 + values12 (152 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (151 : Fin 154) < (152 : Fin 154))) 1
  next =>
    change 1 + values12 (152 : Fin 154) < 1 + values12 (153 : Fin 154)
    exact add_lt_add_right
      (values12_strictMono (by decide : (152 : Fin 154) < (153 : Fin 154))) 1

theorem values14_range_ncard :
    (Set.range values14).ncard = 455 := by
  rw [Set.ncard_range_of_injective values14_strictMono.injective]
  norm_num

end Expr

end A158415

end LeanProofs
