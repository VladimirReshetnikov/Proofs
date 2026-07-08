import LeanProofs.A158415FifteenTable

/-!
# Unary size-fifteen range lemmas for OEIS A158415

This module contains generated inclusions from recursive candidate families into
the size-15 representative table.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem one_add_values11_mem_range_values15 (i : Fin 91) :
    (Set.range values15) (1 + values11 i) := by
  fin_cases i
  next =>
    exact Exists.intro (430 : Fin 791) (by
      change Real.sqrt (values14 (430 : Fin 455)) = 1 + values11 (0 : Fin 91)
      rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values11 (0 : Fin 91) = Real.sqrt (values10 (0 : Fin 54)) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (433 : Fin 791) (by
      change 1 + values13 (3 : Fin 264) = 1 + values11 (1 : Fin 91)
      rw [show values13 (3 : Fin 264) = Real.sqrt (values12 (3 : Fin 154)) by rfl]
      rw [show values12 (3 : Fin 154) = Real.sqrt (values11 (3 : Fin 91)) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (435 : Fin 791) (by
      change 1 + values13 (5 : Fin 264) = 1 + values11 (2 : Fin 91)
      rw [show values13 (5 : Fin 264) = Real.sqrt (values12 (5 : Fin 154)) by rfl]
      rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (439 : Fin 791) (by
      change 1 + values13 (8 : Fin 264) = 1 + values11 (3 : Fin 91)
      rw [show values13 (8 : Fin 264) = Real.sqrt (values12 (8 : Fin 154)) by rfl]
      rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (443 : Fin 791) (by
      change 1 + values13 (11 : Fin 264) = 1 + values11 (4 : Fin 91)
      rw [show values13 (11 : Fin 264) = Real.sqrt (values12 (11 : Fin 154)) by rfl]
      rw [show values12 (11 : Fin 154) = Real.sqrt (values11 (11 : Fin 91)) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values11 (4 : Fin 91) = Real.sqrt (values10 (4 : Fin 54)) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (444 : Fin 791) (by
      change 1 + values13 (12 : Fin 264) = 1 + values11 (5 : Fin 91)
      rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (448 : Fin 791) (by
      change 1 + values13 (15 : Fin 264) = 1 + values11 (6 : Fin 91)
      rw [show values13 (15 : Fin 264) = Real.sqrt (values12 (15 : Fin 154)) by rfl]
      rw [show values12 (15 : Fin 154) = Real.sqrt (values11 (15 : Fin 91)) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (450 : Fin 791) (by
      change 1 + values13 (17 : Fin 264) = 1 + values11 (7 : Fin 91)
      rw [show values13 (17 : Fin 264) = Real.sqrt (values12 (17 : Fin 154)) by rfl]
      rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (454 : Fin 791) (by
      change 1 + values13 (19 : Fin 264) = 1 + values11 (8 : Fin 91)
      rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
      rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (458 : Fin 791) (by
      change 1 + values13 (22 : Fin 264) = 1 + values11 (9 : Fin 91)
      rw [show values13 (22 : Fin 264) = Real.sqrt (values12 (22 : Fin 154)) by rfl]
      rw [show values12 (22 : Fin 154) = Real.sqrt (values11 (22 : Fin 91)) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (460 : Fin 791) (by
      change 1 + values13 (24 : Fin 264) = 1 + values11 (10 : Fin 91)
      rw [show values13 (24 : Fin 264) = Real.sqrt (values12 (24 : Fin 154)) by rfl]
      rw [show values12 (24 : Fin 154) = Real.sqrt (values11 (24 : Fin 91)) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (467 : Fin 791) (by
      change 1 + values13 (28 : Fin 264) = 1 + values11 (11 : Fin 91)
      rw [show values13 (28 : Fin 264) = Real.sqrt (values12 (28 : Fin 154)) by rfl]
      rw [show values12 (28 : Fin 154) = Real.sqrt (values11 (28 : Fin 91)) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (472 : Fin 791) (by
      change 1 + values13 (31 : Fin 264) = 1 + values11 (12 : Fin 91)
      rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
      rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (475 : Fin 791) (by
      change 1 + values13 (34 : Fin 264) = 1 + values11 (13 : Fin 91)
      rw [show values13 (34 : Fin 264) = Real.sqrt (values12 (34 : Fin 154)) by rfl]
      rw [show values12 (34 : Fin 154) = Real.sqrt (values11 (34 : Fin 91)) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (478 : Fin 791) (by
      change 1 + values13 (36 : Fin 264) = 1 + values11 (14 : Fin 91)
      rw [show values13 (36 : Fin 264) = Real.sqrt (values12 (36 : Fin 154)) by rfl]
      rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (483 : Fin 791) (by
      change 1 + values13 (40 : Fin 264) = 1 + values11 (15 : Fin 91)
      rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
      rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (488 : Fin 791) (by
      change 1 + values13 (44 : Fin 264) = 1 + values11 (16 : Fin 91)
      rw [show values13 (44 : Fin 264) = Real.sqrt (values12 (44 : Fin 154)) by rfl]
      rw [show values12 (44 : Fin 154) = Real.sqrt (values11 (44 : Fin 91)) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values11 (16 : Fin 91) = Real.sqrt (values10 (16 : Fin 54)) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (493 : Fin 791) (by
      change 1 + values13 (46 : Fin 264) = 1 + values11 (17 : Fin 91)
      rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
      rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (496 : Fin 791) (by
      change 1 + values13 (49 : Fin 264) = 1 + values11 (18 : Fin 91)
      rw [show values13 (49 : Fin 264) = Real.sqrt (values12 (49 : Fin 154)) by rfl]
      rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (500 : Fin 791) (by
      change 1 + values13 (51 : Fin 264) = 1 + values11 (19 : Fin 91)
      rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
      rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (503 : Fin 791) (by
      change 1 + values13 (54 : Fin 264) = 1 + values11 (20 : Fin 91)
      rw [show values13 (54 : Fin 264) = Real.sqrt (values12 (54 : Fin 154)) by rfl]
      rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      rw [show values11 (20 : Fin 91) = Real.sqrt (values10 (20 : Fin 54)) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (507 : Fin 791) (by
      change 1 + values13 (56 : Fin 264) = 1 + values11 (21 : Fin 91)
      rw [show values13 (56 : Fin 264) = Real.sqrt (values12 (56 : Fin 154)) by rfl]
      rw [show values12 (56 : Fin 154) = Real.sqrt (values11 (56 : Fin 91)) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (512 : Fin 791) (by
      change 1 + values13 (60 : Fin 264) = 1 + values11 (22 : Fin 91)
      rw [show values13 (60 : Fin 264) = Real.sqrt (values12 (60 : Fin 154)) by rfl]
      rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (517 : Fin 791) (by
      change 1 + values13 (64 : Fin 264) = 1 + values11 (23 : Fin 91)
      rw [show values13 (64 : Fin 264) = Real.sqrt (values12 (64 : Fin 154)) by rfl]
      rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      rw [show values11 (23 : Fin 91) = Real.sqrt (values10 (23 : Fin 54)) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (521 : Fin 791) (by
      change 1 + values13 (66 : Fin 264) = 1 + values11 (24 : Fin 91)
      rw [show values13 (66 : Fin 264) = Real.sqrt (values12 (66 : Fin 154)) by rfl]
      rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (527 : Fin 791) (by
      change 1 + values13 (70 : Fin 264) = 1 + values11 (25 : Fin 91)
      rw [show values13 (70 : Fin 264) = Real.sqrt (values12 (70 : Fin 154)) by rfl]
      rw [show values12 (70 : Fin 154) = Real.sqrt (values11 (70 : Fin 91)) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (532 : Fin 791) (by
      change 1 + values13 (73 : Fin 264) = 1 + values11 (26 : Fin 91)
      rw [show values13 (73 : Fin 264) = Real.sqrt (values12 (73 : Fin 154)) by rfl]
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (533 : Fin 791) (by
      change 1 + values13 (74 : Fin 264) = 1 + values11 (27 : Fin 91)
      rw [show values13 (74 : Fin 264) = Real.sqrt (values12 (74 : Fin 154)) by rfl]
      rw [show values12 (74 : Fin 154) = Real.sqrt (values11 (74 : Fin 91)) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values11 (27 : Fin 91) = Real.sqrt (values10 (27 : Fin 54)) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (536 : Fin 791) (by
      change 1 + values13 (76 : Fin 264) = 1 + values11 (28 : Fin 91)
      rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (541 : Fin 791) (by
      change 1 + values13 (80 : Fin 264) = 1 + values11 (29 : Fin 91)
      rw [show values13 (80 : Fin 264) = Real.sqrt (values12 (80 : Fin 154)) by rfl]
      rw [show values12 (80 : Fin 154) = Real.sqrt (values11 (80 : Fin 91)) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      rw [show values11 (29 : Fin 91) = Real.sqrt (values10 (29 : Fin 54)) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (545 : Fin 791) (by
      change 1 + values13 (82 : Fin 264) = 1 + values11 (30 : Fin 91)
      rw [show values13 (82 : Fin 264) = Real.sqrt (values12 (82 : Fin 154)) by rfl]
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (554 : Fin 791) (by
      change 1 + values13 (86 : Fin 264) = 1 + values11 (31 : Fin 91)
      rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (558 : Fin 791) (by
      change 1 + values13 (89 : Fin 264) = 1 + values11 (32 : Fin 91)
      rw [show values13 (89 : Fin 264) = Real.sqrt (values12 (89 : Fin 154)) by rfl]
      rw [show values12 (89 : Fin 154) = 1 + values10 (3 : Fin 54) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values11 (32 : Fin 91) = Real.sqrt (values10 (32 : Fin 54)) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (561 : Fin 791) (by
      change 1 + values13 (91 : Fin 264) = 1 + values11 (33 : Fin 91)
      rw [show values13 (91 : Fin 264) = Real.sqrt (values12 (91 : Fin 154)) by rfl]
      rw [show values12 (91 : Fin 154) = 1 + values10 (5 : Fin 54) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (567 : Fin 791) (by
      change 1 + values13 (95 : Fin 264) = 1 + values11 (34 : Fin 91)
      rw [show values13 (95 : Fin 264) = Real.sqrt (values12 (95 : Fin 154)) by rfl]
      rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (574 : Fin 791) (by
      change 1 + values13 (99 : Fin 264) = 1 + values11 (35 : Fin 91)
      rw [show values13 (99 : Fin 264) = Real.sqrt (values12 (99 : Fin 154)) by rfl]
      rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (576 : Fin 791) (by
      change 1 + values13 (100 : Fin 264) = 1 + values11 (36 : Fin 91)
      rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
      rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (580 : Fin 791) (by
      change 1 + values13 (103 : Fin 264) = 1 + values11 (37 : Fin 91)
      rw [show values13 (103 : Fin 264) = Real.sqrt (values12 (103 : Fin 154)) by rfl]
      rw [show values12 (103 : Fin 154) = Real.sqrt (values11 (89 : Fin 91)) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      rw [show values11 (37 : Fin 91) = Real.sqrt (values10 (37 : Fin 54)) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (581 : Fin 791) (by
      change 1 + values13 (104 : Fin 264) = 1 + values11 (38 : Fin 91)
      rw [show values13 (104 : Fin 264) = Real.sqrt (values12 (104 : Fin 154)) by rfl]
      rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values11 (38 : Fin 91) = Real.sqrt (values10 (38 : Fin 54)) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (587 : Fin 791) (by
      change 1 + values13 (107 : Fin 264) = 1 + values11 (39 : Fin 91)
      rw [show values13 (107 : Fin 264) = Real.sqrt (values12 (107 : Fin 154)) by rfl]
      rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (592 : Fin 791) (by
      change 1 + values13 (110 : Fin 264) = 1 + values11 (40 : Fin 91)
      rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
      rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (599 : Fin 791) (by
      change 1 + values13 (115 : Fin 264) = 1 + values11 (41 : Fin 91)
      rw [show values13 (115 : Fin 264) = Real.sqrt (values12 (115 : Fin 154)) by rfl]
      rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values11 (41 : Fin 91) = Real.sqrt (values10 (41 : Fin 54)) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (603 : Fin 791) (by
      change 1 + values13 (118 : Fin 264) = 1 + values11 (42 : Fin 91)
      rw [show values13 (118 : Fin 264) = Real.sqrt (values12 (118 : Fin 154)) by rfl]
      rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (606 : Fin 791) (by
      change 1 + values13 (120 : Fin 264) = 1 + values11 (43 : Fin 91)
      rw [show values13 (120 : Fin 264) = Real.sqrt (values12 (120 : Fin 154)) by rfl]
      rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by rfl]
      rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (616 : Fin 791) (by
      change 1 + values13 (124 : Fin 264) = 1 + values11 (44 : Fin 91)
      rw [show values13 (124 : Fin 264) = Real.sqrt (values12 (124 : Fin 154)) by rfl]
      rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (620 : Fin 791) (by
      change 1 + values13 (126 : Fin 264) = 1 + values11 (45 : Fin 91)
      rw [show values13 (126 : Fin 264) = Real.sqrt (values12 (126 : Fin 154)) by rfl]
      rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (626 : Fin 791) (by
      change 1 + values13 (130 : Fin 264) = 1 + values11 (46 : Fin 91)
      rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (631 : Fin 791) (by
      change 1 + values13 (133 : Fin 264) = 1 + values11 (47 : Fin 91)
      rw [show values13 (133 : Fin 264) = Real.sqrt (values12 (133 : Fin 154)) by rfl]
      rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values11 (47 : Fin 91) = Real.sqrt (values10 (47 : Fin 54)) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (636 : Fin 791) (by
      change 1 + values13 (136 : Fin 264) = 1 + values11 (48 : Fin 91)
      rw [show values13 (136 : Fin 264) = Real.sqrt (values12 (136 : Fin 154)) by rfl]
      rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (644 : Fin 791) (by
      change 1 + values13 (140 : Fin 264) = 1 + values11 (49 : Fin 91)
      rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
      rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (653 : Fin 791) (by
      change 1 + values13 (144 : Fin 264) = 1 + values11 (50 : Fin 91)
      rw [show values13 (144 : Fin 264) = Real.sqrt (values12 (144 : Fin 154)) by rfl]
      rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 1 + values11 (51 : Fin 91)
      rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (661 : Fin 791) (by
      change 1 + values13 (149 : Fin 264) = 1 + values11 (52 : Fin 91)
      rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values11 (52 : Fin 91) = 1 + values9 (1 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 1 + values11 (53 : Fin 91)
      rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 1 + values11 (54 : Fin 91)
      rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (675 : Fin 791) (by
      change 1 + values13 (159 : Fin 264) = 1 + values11 (55 : Fin 91)
      rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 1 + values11 (56 : Fin 91)
      rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (679 : Fin 791) (by
      change 1 + values13 (162 : Fin 264) = 1 + values11 (57 : Fin 91)
      rw [show values13 (162 : Fin 264) = Real.sqrt (values12 (149 : Fin 154)) by rfl]
      rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values11 (57 : Fin 91) = Real.sqrt (values10 (52 : Fin 54)) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (682 : Fin 791) (by
      change 1 + values13 (164 : Fin 264) = 1 + values11 (58 : Fin 91)
      rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 1 + values11 (59 : Fin 91)
      rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 1 + values11 (60 : Fin 91)
      rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (694 : Fin 791) (by
      change 1 + values13 (173 : Fin 264) = 1 + values11 (61 : Fin 91)
      rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values11 (61 : Fin 91) = 1 + values9 (9 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (697 : Fin 791) (by
      change 1 + values13 (176 : Fin 264) = 1 + values11 (62 : Fin 91)
      rw [show values13 (176 : Fin 264) = Real.sqrt (values12 (151 : Fin 154)) by rfl]
      rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 1 + values11 (63 : Fin 91)
      rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 1 + values11 (64 : Fin 91)
      rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (709 : Fin 791) (by
      change 1 + values13 (186 : Fin 264) = 1 + values11 (65 : Fin 91)
      rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
      rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 1 + values11 (66 : Fin 91)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (714 : Fin 791) (by
      change 1 + values13 (191 : Fin 264) = 1 + values11 (67 : Fin 91)
      rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 1 + values11 (68 : Fin 91)
      rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (722 : Fin 791) (by
      change 1 + values13 (198 : Fin 264) = 1 + values11 (69 : Fin 91)
      rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
      rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 1 + values11 (70 : Fin 91)
      rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (729 : Fin 791) (by
      change 1 + values13 (205 : Fin 264) = 1 + values11 (71 : Fin 91)
      rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (732 : Fin 791) (by
      change 1 + values13 (207 : Fin 264) = 1 + values11 (72 : Fin 91)
      rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 1 + values11 (73 : Fin 91)
      rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (741 : Fin 791) (by
      change 1 + values13 (216 : Fin 264) = 1 + values11 (74 : Fin 91)
      rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (742 : Fin 791) (by
      change 1 + values13 (217 : Fin 264) = 1 + values11 (75 : Fin 91)
      rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 1 + values11 (76 : Fin 91)
      rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (751 : Fin 791) (by
      change 1 + values13 (225 : Fin 264) = 1 + values11 (77 : Fin 91)
      rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 1 + values11 (78 : Fin 91)
      rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (756 : Fin 791) (by
      change 1 + values13 (230 : Fin 264) = 1 + values11 (79 : Fin 91)
      rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 1 + values11 (80 : Fin 91)
      rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (763 : Fin 791) (by
      change 1 + values13 (236 : Fin 264) = 1 + values11 (81 : Fin 91)
      rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 1 + values11 (82 : Fin 91)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (770 : Fin 791) (by
      change 1 + values13 (243 : Fin 264) = 1 + values11 (83 : Fin 91)
      rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 1 + values11 (84 : Fin 91)
      rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = 1 + values11 (85 : Fin 91)
      rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 1 + values11 (86 : Fin 91)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (780 : Fin 791) (by
      change 1 + values13 (253 : Fin 264) = 1 + values11 (87 : Fin 91)
      rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 1 + values11 (88 : Fin 91)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 1 + values11 (89 : Fin 91)
      rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (789 : Fin 791) (by
      change 1 + values13 (262 : Fin 264) = 1 + values11 (90 : Fin 91)
      rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem two_add_values11_mem_range_values15 (i : Fin 91) :
    (Set.range values15) (2 + values11 i) := by
  fin_cases i
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 2 + values11 (0 : Fin 91)
      rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values11 (0 : Fin 91) = Real.sqrt (values10 (0 : Fin 54)) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (659 : Fin 791) (by
      change 1 + values13 (147 : Fin 264) = 2 + values11 (1 : Fin 91)
      rw [show values13 (147 : Fin 264) = 1 + values11 (1 : Fin 91) by rfl]
      rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (660 : Fin 791) (by
      change 1 + values13 (148 : Fin 264) = 2 + values11 (2 : Fin 91)
      rw [show values13 (148 : Fin 264) = 1 + values11 (2 : Fin 91) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (661 : Fin 791) (by
      change 1 + values13 (149 : Fin 264) = 2 + values11 (3 : Fin 91)
      rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (663 : Fin 791) (by
      change 1 + values13 (150 : Fin 264) = 2 + values11 (4 : Fin 91)
      rw [show values13 (150 : Fin 264) = 1 + values11 (4 : Fin 91) by rfl]
      rw [show values11 (4 : Fin 91) = Real.sqrt (values10 (4 : Fin 54)) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 2 + values11 (5 : Fin 91)
      rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (666 : Fin 791) (by
      change 1 + values13 (153 : Fin 264) = 2 + values11 (6 : Fin 91)
      rw [show values13 (153 : Fin 264) = 1 + values11 (6 : Fin 91) by rfl]
      rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (667 : Fin 791) (by
      change 1 + values13 (154 : Fin 264) = 2 + values11 (7 : Fin 91)
      rw [show values13 (154 : Fin 264) = 1 + values11 (7 : Fin 91) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 2 + values11 (8 : Fin 91)
      rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (672 : Fin 791) (by
      change 1 + values13 (157 : Fin 264) = 2 + values11 (9 : Fin 91)
      rw [show values13 (157 : Fin 264) = 1 + values11 (9 : Fin 91) by rfl]
      rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (673 : Fin 791) (by
      change 1 + values13 (158 : Fin 264) = 2 + values11 (10 : Fin 91)
      rw [show values13 (158 : Fin 264) = 1 + values11 (10 : Fin 91) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (675 : Fin 791) (by
      change 1 + values13 (159 : Fin 264) = 2 + values11 (11 : Fin 91)
      rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 2 + values11 (12 : Fin 91)
      rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (678 : Fin 791) (by
      change 1 + values13 (161 : Fin 264) = 2 + values11 (13 : Fin 91)
      rw [show values13 (161 : Fin 264) = 1 + values11 (13 : Fin 91) by rfl]
      rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (680 : Fin 791) (by
      change 1 + values13 (163 : Fin 264) = 2 + values11 (14 : Fin 91)
      rw [show values13 (163 : Fin 264) = 1 + values11 (14 : Fin 91) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (682 : Fin 791) (by
      change 1 + values13 (164 : Fin 264) = 2 + values11 (15 : Fin 91)
      rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (683 : Fin 791) (by
      change 1 + values13 (165 : Fin 264) = 2 + values11 (16 : Fin 91)
      rw [show values13 (165 : Fin 264) = 1 + values11 (16 : Fin 91) by rfl]
      rw [show values11 (16 : Fin 91) = Real.sqrt (values10 (16 : Fin 54)) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 2 + values11 (17 : Fin 91)
      rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (686 : Fin 791) (by
      change 1 + values13 (167 : Fin 264) = 2 + values11 (18 : Fin 91)
      rw [show values13 (167 : Fin 264) = 1 + values11 (18 : Fin 91) by rfl]
      rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 2 + values11 (19 : Fin 91)
      rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (690 : Fin 791) (by
      change 1 + values13 (171 : Fin 264) = 2 + values11 (20 : Fin 91)
      rw [show values13 (171 : Fin 264) = 1 + values11 (20 : Fin 91) by rfl]
      rw [show values11 (20 : Fin 91) = Real.sqrt (values10 (20 : Fin 54)) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (692 : Fin 791) (by
      change 1 + values13 (172 : Fin 264) = 2 + values11 (21 : Fin 91)
      rw [show values13 (172 : Fin 264) = 1 + values11 (21 : Fin 91) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (694 : Fin 791) (by
      change 1 + values13 (173 : Fin 264) = 2 + values11 (22 : Fin 91)
      rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (696 : Fin 791) (by
      change 1 + values13 (175 : Fin 264) = 2 + values11 (23 : Fin 91)
      rw [show values13 (175 : Fin 264) = 1 + values11 (23 : Fin 91) by rfl]
      rw [show values11 (23 : Fin 91) = Real.sqrt (values10 (23 : Fin 54)) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 2 + values11 (24 : Fin 91)
      rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (700 : Fin 791) (by
      change 1 + values13 (178 : Fin 264) = 2 + values11 (25 : Fin 91)
      rw [show values13 (178 : Fin 264) = 1 + values11 (25 : Fin 91) by rfl]
      rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (702 : Fin 791) (by
      change 1 + values13 (180 : Fin 264) = 2 + values11 (26 : Fin 91)
      rw [show values13 (180 : Fin 264) = 1 + values11 (26 : Fin 91) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (704 : Fin 791) (by
      change 1 + values13 (181 : Fin 264) = 2 + values11 (27 : Fin 91)
      rw [show values13 (181 : Fin 264) = 1 + values11 (27 : Fin 91) by rfl]
      rw [show values11 (27 : Fin 91) = Real.sqrt (values10 (27 : Fin 54)) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 2 + values11 (28 : Fin 91)
      rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (707 : Fin 791) (by
      change 1 + values13 (184 : Fin 264) = 2 + values11 (29 : Fin 91)
      rw [show values13 (184 : Fin 264) = 1 + values11 (29 : Fin 91) by rfl]
      rw [show values11 (29 : Fin 91) = Real.sqrt (values10 (29 : Fin 54)) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (708 : Fin 791) (by
      change 1 + values13 (185 : Fin 264) = 2 + values11 (30 : Fin 91)
      rw [show values13 (185 : Fin 264) = 1 + values11 (30 : Fin 91) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 2 + values11 (31 : Fin 91)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (711 : Fin 791) (by
      change 1 + values13 (188 : Fin 264) = 2 + values11 (32 : Fin 91)
      rw [show values13 (188 : Fin 264) = 1 + values11 (32 : Fin 91) by rfl]
      rw [show values11 (32 : Fin 91) = Real.sqrt (values10 (32 : Fin 54)) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (712 : Fin 791) (by
      change 1 + values13 (189 : Fin 264) = 2 + values11 (33 : Fin 91)
      rw [show values13 (189 : Fin 264) = 1 + values11 (33 : Fin 91) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (714 : Fin 791) (by
      change 1 + values13 (191 : Fin 264) = 2 + values11 (34 : Fin 91)
      rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (718 : Fin 791) (by
      change 1 + values13 (194 : Fin 264) = 2 + values11 (35 : Fin 91)
      rw [show values13 (194 : Fin 264) = 1 + values11 (35 : Fin 91) by rfl]
      rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 2 + values11 (36 : Fin 91)
      rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (720 : Fin 791) (by
      change 1 + values13 (196 : Fin 264) = 2 + values11 (37 : Fin 91)
      rw [show values13 (196 : Fin 264) = 1 + values11 (37 : Fin 91) by rfl]
      rw [show values11 (37 : Fin 91) = Real.sqrt (values10 (37 : Fin 54)) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (721 : Fin 791) (by
      change 1 + values13 (197 : Fin 264) = 2 + values11 (38 : Fin 91)
      rw [show values13 (197 : Fin 264) = 1 + values11 (38 : Fin 91) by rfl]
      rw [show values11 (38 : Fin 91) = Real.sqrt (values10 (38 : Fin 54)) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (724 : Fin 791) (by
      change 1 + values13 (200 : Fin 264) = 2 + values11 (39 : Fin 91)
      rw [show values13 (200 : Fin 264) = 1 + values11 (39 : Fin 91) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 2 + values11 (40 : Fin 91)
      rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (727 : Fin 791) (by
      change 1 + values13 (203 : Fin 264) = 2 + values11 (41 : Fin 91)
      rw [show values13 (203 : Fin 264) = 1 + values11 (41 : Fin 91) by rfl]
      rw [show values11 (41 : Fin 91) = Real.sqrt (values10 (41 : Fin 54)) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (728 : Fin 791) (by
      change 1 + values13 (204 : Fin 264) = 2 + values11 (42 : Fin 91)
      rw [show values13 (204 : Fin 264) = 1 + values11 (42 : Fin 91) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (730 : Fin 791) (by
      change 1 + values13 (206 : Fin 264) = 2 + values11 (43 : Fin 91)
      rw [show values13 (206 : Fin 264) = 1 + values11 (43 : Fin 91) by rfl]
      rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (732 : Fin 791) (by
      change 1 + values13 (207 : Fin 264) = 2 + values11 (44 : Fin 91)
      rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (734 : Fin 791) (by
      change 1 + values13 (209 : Fin 264) = 2 + values11 (45 : Fin 91)
      rw [show values13 (209 : Fin 264) = 1 + values11 (45 : Fin 91) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 2 + values11 (46 : Fin 91)
      rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (738 : Fin 791) (by
      change 1 + values13 (213 : Fin 264) = 2 + values11 (47 : Fin 91)
      rw [show values13 (213 : Fin 264) = 1 + values11 (47 : Fin 91) by rfl]
      rw [show values11 (47 : Fin 91) = Real.sqrt (values10 (47 : Fin 54)) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (739 : Fin 791) (by
      change 1 + values13 (214 : Fin 264) = 2 + values11 (48 : Fin 91)
      rw [show values13 (214 : Fin 264) = 1 + values11 (48 : Fin 91) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (742 : Fin 791) (by
      change 1 + values13 (217 : Fin 264) = 2 + values11 (49 : Fin 91)
      rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (745 : Fin 791) (by
      change 1 + values13 (220 : Fin 264) = 2 + values11 (50 : Fin 91)
      rw [show values13 (220 : Fin 264) = 1 + values11 (50 : Fin 91) by rfl]
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 2 + values11 (51 : Fin 91)
      rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (748 : Fin 791) (by
      change 1 + values13 (223 : Fin 264) = 2 + values11 (52 : Fin 91)
      rw [show values13 (223 : Fin 264) = 1 + values11 (52 : Fin 91) by rfl]
      rw [show values11 (52 : Fin 91) = 1 + values9 (1 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (750 : Fin 791) (by
      change 1 + values13 (224 : Fin 264) = 2 + values11 (53 : Fin 91)
      rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (751 : Fin 791) (by
      change 1 + values13 (225 : Fin 264) = 2 + values11 (54 : Fin 91)
      rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (752 : Fin 791) (by
      change 1 + values13 (226 : Fin 264) = 2 + values11 (55 : Fin 91)
      rw [show values13 (226 : Fin 264) = 1 + values11 (55 : Fin 91) by rfl]
      rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 2 + values11 (56 : Fin 91)
      rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (754 : Fin 791) (by
      change 1 + values13 (228 : Fin 264) = 2 + values11 (57 : Fin 91)
      rw [show values13 (228 : Fin 264) = 1 + values11 (57 : Fin 91) by rfl]
      rw [show values11 (57 : Fin 91) = Real.sqrt (values10 (52 : Fin 54)) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (755 : Fin 791) (by
      change 1 + values13 (229 : Fin 264) = 2 + values11 (58 : Fin 91)
      rw [show values13 (229 : Fin 264) = 1 + values11 (58 : Fin 91) by rfl]
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (757 : Fin 791) (by
      change 1 + values13 (231 : Fin 264) = 2 + values11 (59 : Fin 91)
      rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 2 + values11 (60 : Fin 91)
      rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (759 : Fin 791) (by
      change 1 + values13 (233 : Fin 264) = 2 + values11 (61 : Fin 91)
      rw [show values13 (233 : Fin 264) = 1 + values11 (61 : Fin 91) by rfl]
      rw [show values11 (61 : Fin 91) = 1 + values9 (9 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (760 : Fin 791) (by
      change 1 + values13 (234 : Fin 264) = 2 + values11 (62 : Fin 91)
      rw [show values13 (234 : Fin 264) = 1 + values11 (62 : Fin 91) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (762 : Fin 791) (by
      change 1 + values13 (235 : Fin 264) = 2 + values11 (63 : Fin 91)
      rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (763 : Fin 791) (by
      change 1 + values13 (236 : Fin 264) = 2 + values11 (64 : Fin 91)
      rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (764 : Fin 791) (by
      change 1 + values13 (237 : Fin 264) = 2 + values11 (65 : Fin 91)
      rw [show values13 (237 : Fin 264) = 1 + values11 (65 : Fin 91) by rfl]
      rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 2 + values11 (66 : Fin 91)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (766 : Fin 791) (by
      change 1 + values13 (239 : Fin 264) = 2 + values11 (67 : Fin 91)
      rw [show values13 (239 : Fin 264) = 1 + values11 (67 : Fin 91) by rfl]
      rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (768 : Fin 791) (by
      change 1 + values13 (241 : Fin 264) = 2 + values11 (68 : Fin 91)
      rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (769 : Fin 791) (by
      change 1 + values13 (242 : Fin 264) = 2 + values11 (69 : Fin 91)
      rw [show values13 (242 : Fin 264) = 1 + values11 (69 : Fin 91) by rfl]
      rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (770 : Fin 791) (by
      change 1 + values13 (243 : Fin 264) = 2 + values11 (70 : Fin 91)
      rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (771 : Fin 791) (by
      change 1 + values13 (244 : Fin 264) = 2 + values11 (71 : Fin 91)
      rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (772 : Fin 791) (by
      change 1 + values13 (245 : Fin 264) = 2 + values11 (72 : Fin 91)
      rw [show values13 (245 : Fin 264) = 1 + values11 (72 : Fin 91) by rfl]
      rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 2 + values11 (73 : Fin 91)
      rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = 2 + values11 (74 : Fin 91)
      rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (775 : Fin 791) (by
      change 1 + values13 (248 : Fin 264) = 2 + values11 (75 : Fin 91)
      rw [show values13 (248 : Fin 264) = 1 + values11 (75 : Fin 91) by rfl]
      rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 2 + values11 (76 : Fin 91)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (777 : Fin 791) (by
      change 1 + values13 (250 : Fin 264) = 2 + values11 (77 : Fin 91)
      rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (778 : Fin 791) (by
      change 1 + values13 (251 : Fin 264) = 2 + values11 (78 : Fin 91)
      rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (779 : Fin 791) (by
      change 1 + values13 (252 : Fin 264) = 2 + values11 (79 : Fin 91)
      rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (780 : Fin 791) (by
      change 1 + values13 (253 : Fin 264) = 2 + values11 (80 : Fin 91)
      rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (781 : Fin 791) (by
      change 1 + values13 (254 : Fin 264) = 2 + values11 (81 : Fin 91)
      rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 2 + values11 (82 : Fin 91)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (783 : Fin 791) (by
      change 1 + values13 (256 : Fin 264) = 2 + values11 (83 : Fin 91)
      rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (784 : Fin 791) (by
      change 1 + values13 (257 : Fin 264) = 2 + values11 (84 : Fin 91)
      rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (785 : Fin 791) (by
      change 1 + values13 (258 : Fin 264) = 2 + values11 (85 : Fin 91)
      rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 2 + values11 (86 : Fin 91)
      rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (787 : Fin 791) (by
      change 1 + values13 (260 : Fin 264) = 2 + values11 (87 : Fin 91)
      rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (788 : Fin 791) (by
      change 1 + values13 (261 : Fin 264) = 2 + values11 (88 : Fin 91)
      rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (789 : Fin 791) (by
      change 1 + values13 (262 : Fin 264) = 2 + values11 (89 : Fin 91)
      rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (790 : Fin 791) (by
      change 1 + values13 (263 : Fin 264) = 2 + values11 (90 : Fin 91)
      rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
      rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem one_add_values10_mem_range_values15 (i : Fin 54) :
    (Set.range values15) (1 + values10 i) := by
  fin_cases i
  next =>
    exact Exists.intro (430 : Fin 791) (by
      change Real.sqrt (values14 (430 : Fin 455)) = 1 + values10 (0 : Fin 54)
      rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (435 : Fin 791) (by
      change 1 + values13 (5 : Fin 264) = 1 + values10 (1 : Fin 54)
      rw [show values13 (5 : Fin 264) = Real.sqrt (values12 (5 : Fin 154)) by rfl]
      rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (439 : Fin 791) (by
      change 1 + values13 (8 : Fin 264) = 1 + values10 (2 : Fin 54)
      rw [show values13 (8 : Fin 264) = Real.sqrt (values12 (8 : Fin 154)) by rfl]
      rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (444 : Fin 791) (by
      change 1 + values13 (12 : Fin 264) = 1 + values10 (3 : Fin 54)
      rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (450 : Fin 791) (by
      change 1 + values13 (17 : Fin 264) = 1 + values10 (4 : Fin 54)
      rw [show values13 (17 : Fin 264) = Real.sqrt (values12 (17 : Fin 154)) by rfl]
      rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (454 : Fin 791) (by
      change 1 + values13 (19 : Fin 264) = 1 + values10 (5 : Fin 54)
      rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
      rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (460 : Fin 791) (by
      change 1 + values13 (24 : Fin 264) = 1 + values10 (6 : Fin 54)
      rw [show values13 (24 : Fin 264) = Real.sqrt (values12 (24 : Fin 154)) by rfl]
      rw [show values12 (24 : Fin 154) = Real.sqrt (values11 (24 : Fin 91)) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (467 : Fin 791) (by
      change 1 + values13 (28 : Fin 264) = 1 + values10 (7 : Fin 54)
      rw [show values13 (28 : Fin 264) = Real.sqrt (values12 (28 : Fin 154)) by rfl]
      rw [show values12 (28 : Fin 154) = Real.sqrt (values11 (28 : Fin 91)) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (472 : Fin 791) (by
      change 1 + values13 (31 : Fin 264) = 1 + values10 (8 : Fin 54)
      rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
      rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (478 : Fin 791) (by
      change 1 + values13 (36 : Fin 264) = 1 + values10 (9 : Fin 54)
      rw [show values13 (36 : Fin 264) = Real.sqrt (values12 (36 : Fin 154)) by rfl]
      rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (483 : Fin 791) (by
      change 1 + values13 (40 : Fin 264) = 1 + values10 (10 : Fin 54)
      rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
      rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (493 : Fin 791) (by
      change 1 + values13 (46 : Fin 264) = 1 + values10 (11 : Fin 54)
      rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
      rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (500 : Fin 791) (by
      change 1 + values13 (51 : Fin 264) = 1 + values10 (12 : Fin 54)
      rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
      rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (507 : Fin 791) (by
      change 1 + values13 (56 : Fin 264) = 1 + values10 (13 : Fin 54)
      rw [show values13 (56 : Fin 264) = Real.sqrt (values12 (56 : Fin 154)) by rfl]
      rw [show values12 (56 : Fin 154) = Real.sqrt (values11 (56 : Fin 91)) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (512 : Fin 791) (by
      change 1 + values13 (60 : Fin 264) = 1 + values10 (14 : Fin 54)
      rw [show values13 (60 : Fin 264) = Real.sqrt (values12 (60 : Fin 154)) by rfl]
      rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (521 : Fin 791) (by
      change 1 + values13 (66 : Fin 264) = 1 + values10 (15 : Fin 54)
      rw [show values13 (66 : Fin 264) = Real.sqrt (values12 (66 : Fin 154)) by rfl]
      rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (532 : Fin 791) (by
      change 1 + values13 (73 : Fin 264) = 1 + values10 (16 : Fin 54)
      rw [show values13 (73 : Fin 264) = Real.sqrt (values12 (73 : Fin 154)) by rfl]
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (536 : Fin 791) (by
      change 1 + values13 (76 : Fin 264) = 1 + values10 (17 : Fin 54)
      rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (545 : Fin 791) (by
      change 1 + values13 (82 : Fin 264) = 1 + values10 (18 : Fin 54)
      rw [show values13 (82 : Fin 264) = Real.sqrt (values12 (82 : Fin 154)) by rfl]
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (554 : Fin 791) (by
      change 1 + values13 (86 : Fin 264) = 1 + values10 (19 : Fin 54)
      rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (561 : Fin 791) (by
      change 1 + values13 (91 : Fin 264) = 1 + values10 (20 : Fin 54)
      rw [show values13 (91 : Fin 264) = Real.sqrt (values12 (91 : Fin 154)) by rfl]
      rw [show values12 (91 : Fin 154) = 1 + values10 (5 : Fin 54) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (567 : Fin 791) (by
      change 1 + values13 (95 : Fin 264) = 1 + values10 (21 : Fin 54)
      rw [show values13 (95 : Fin 264) = Real.sqrt (values12 (95 : Fin 154)) by rfl]
      rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (576 : Fin 791) (by
      change 1 + values13 (100 : Fin 264) = 1 + values10 (22 : Fin 54)
      rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
      rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (587 : Fin 791) (by
      change 1 + values13 (107 : Fin 264) = 1 + values10 (23 : Fin 54)
      rw [show values13 (107 : Fin 264) = Real.sqrt (values12 (107 : Fin 154)) by rfl]
      rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (592 : Fin 791) (by
      change 1 + values13 (110 : Fin 264) = 1 + values10 (24 : Fin 54)
      rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
      rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (603 : Fin 791) (by
      change 1 + values13 (118 : Fin 264) = 1 + values10 (25 : Fin 54)
      rw [show values13 (118 : Fin 264) = Real.sqrt (values12 (118 : Fin 154)) by rfl]
      rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (616 : Fin 791) (by
      change 1 + values13 (124 : Fin 264) = 1 + values10 (26 : Fin 54)
      rw [show values13 (124 : Fin 264) = Real.sqrt (values12 (124 : Fin 154)) by rfl]
      rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (620 : Fin 791) (by
      change 1 + values13 (126 : Fin 264) = 1 + values10 (27 : Fin 54)
      rw [show values13 (126 : Fin 264) = Real.sqrt (values12 (126 : Fin 154)) by rfl]
      rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (626 : Fin 791) (by
      change 1 + values13 (130 : Fin 264) = 1 + values10 (28 : Fin 54)
      rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (636 : Fin 791) (by
      change 1 + values13 (136 : Fin 264) = 1 + values10 (29 : Fin 54)
      rw [show values13 (136 : Fin 264) = Real.sqrt (values12 (136 : Fin 154)) by rfl]
      rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (644 : Fin 791) (by
      change 1 + values13 (140 : Fin 264) = 1 + values10 (30 : Fin 54)
      rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
      rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 1 + values10 (31 : Fin 54)
      rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 1 + values10 (32 : Fin 54)
      rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 1 + values10 (33 : Fin 54)
      rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 1 + values10 (34 : Fin 54)
      rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 1 + values10 (35 : Fin 54)
      rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 1 + values10 (36 : Fin 54)
      rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (697 : Fin 791) (by
      change 1 + values13 (176 : Fin 264) = 1 + values10 (37 : Fin 54)
      rw [show values13 (176 : Fin 264) = Real.sqrt (values12 (151 : Fin 154)) by rfl]
      rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 1 + values10 (38 : Fin 54)
      rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 1 + values10 (39 : Fin 54)
      rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 1 + values10 (40 : Fin 54)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 1 + values10 (41 : Fin 54)
      rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 1 + values10 (42 : Fin 54)
      rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (729 : Fin 791) (by
      change 1 + values13 (205 : Fin 264) = 1 + values10 (43 : Fin 54)
      rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 1 + values10 (44 : Fin 54)
      rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (741 : Fin 791) (by
      change 1 + values13 (216 : Fin 264) = 1 + values10 (45 : Fin 54)
      rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 1 + values10 (46 : Fin 54)
      rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 1 + values10 (47 : Fin 54)
      rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 1 + values10 (48 : Fin 54)
      rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 1 + values10 (49 : Fin 54)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 1 + values10 (50 : Fin 54)
      rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 1 + values10 (51 : Fin 54)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 1 + values10 (52 : Fin 54)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 1 + values10 (53 : Fin 54)
      rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem sqrt_two_add_values10_mem_range_values15 (i : Fin 54) :
    (Set.range values15) (Real.sqrt 2 + values10 i) := by
  fin_cases i
  next =>
    exact Exists.intro (554 : Fin 791) (by
      change 1 + values13 (86 : Fin 264) = Real.sqrt 2 + values10 (0 : Fin 54)
      rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (557 : Fin 791) (by
      change Real.sqrt 2 + values10 (1 : Fin 54) = Real.sqrt 2 + values10 (1 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (559 : Fin 791) (by
      change Real.sqrt 2 + values10 (2 : Fin 54) = Real.sqrt 2 + values10 (2 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (565 : Fin 791) (by
      change Real.sqrt 2 + values10 (3 : Fin 54) = Real.sqrt 2 + values10 (3 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (568 : Fin 791) (by
      change Real.sqrt 2 + values10 (4 : Fin 54) = Real.sqrt 2 + values10 (4 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (573 : Fin 791) (by
      change Real.sqrt 2 + values10 (5 : Fin 54) = Real.sqrt 2 + values10 (5 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (575 : Fin 791) (by
      change Real.sqrt 2 + values10 (6 : Fin 54) = Real.sqrt 2 + values10 (6 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (578 : Fin 791) (by
      change Real.sqrt 2 + values10 (7 : Fin 54) = Real.sqrt 2 + values10 (7 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (582 : Fin 791) (by
      change Real.sqrt 2 + values10 (8 : Fin 54) = Real.sqrt 2 + values10 (8 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (586 : Fin 791) (by
      change Real.sqrt 2 + values10 (9 : Fin 54) = Real.sqrt 2 + values10 (9 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (588 : Fin 791) (by
      change Real.sqrt 2 + values10 (10 : Fin 54) = Real.sqrt 2 + values10 (10 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (594 : Fin 791) (by
      change Real.sqrt 2 + values10 (11 : Fin 54) = Real.sqrt 2 + values10 (11 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (604 : Fin 791) (by
      change Real.sqrt 2 + values10 (12 : Fin 54) = Real.sqrt 2 + values10 (12 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (607 : Fin 791) (by
      change Real.sqrt 2 + values10 (13 : Fin 54) = Real.sqrt 2 + values10 (13 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (609 : Fin 791) (by
      change Real.sqrt 2 + values10 (14 : Fin 54) = Real.sqrt 2 + values10 (14 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (617 : Fin 791) (by
      change Real.sqrt 2 + values10 (15 : Fin 54) = Real.sqrt 2 + values10 (15 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (622 : Fin 791) (by
      change Real.sqrt 2 + values10 (16 : Fin 54) = Real.sqrt 2 + values10 (16 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (625 : Fin 791) (by
      change Real.sqrt 2 + values10 (17 : Fin 54) = Real.sqrt 2 + values10 (17 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (632 : Fin 791) (by
      change Real.sqrt 2 + values10 (18 : Fin 54) = Real.sqrt 2 + values10 (18 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (641 : Fin 791) (by
      change Real.sqrt 2 + values10 (19 : Fin 54) = Real.sqrt 2 + values10 (19 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (643 : Fin 791) (by
      change Real.sqrt 2 + values10 (20 : Fin 54) = Real.sqrt 2 + values10 (20 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (645 : Fin 791) (by
      change Real.sqrt 2 + values10 (21 : Fin 54) = Real.sqrt 2 + values10 (21 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (650 : Fin 791) (by
      change Real.sqrt 2 + values10 (22 : Fin 54) = Real.sqrt 2 + values10 (22 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (654 : Fin 791) (by
      change Real.sqrt 2 + values10 (23 : Fin 54) = Real.sqrt 2 + values10 (23 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (656 : Fin 791) (by
      change Real.sqrt 2 + values10 (24 : Fin 54) = Real.sqrt 2 + values10 (24 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (662 : Fin 791) (by
      change Real.sqrt 2 + values10 (25 : Fin 54) = Real.sqrt 2 + values10 (25 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (674 : Fin 791) (by
      change Real.sqrt 2 + values10 (26 : Fin 54) = Real.sqrt 2 + values10 (26 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (677 : Fin 791) (by
      change Real.sqrt 2 + values10 (27 : Fin 54) = Real.sqrt 2 + values10 (27 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (684 : Fin 791) (by
      change Real.sqrt 2 + values10 (28 : Fin 54) = Real.sqrt 2 + values10 (28 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (691 : Fin 791) (by
      change Real.sqrt 2 + values10 (29 : Fin 54) = Real.sqrt 2 + values10 (29 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (699 : Fin 791) (by
      change Real.sqrt 2 + values10 (30 : Fin 54) = Real.sqrt 2 + values10 (30 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = Real.sqrt 2 + values10 (31 : Fin 54)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (713 : Fin 791) (by
      change 1 + values13 (190 : Fin 264) = Real.sqrt 2 + values10 (32 : Fin 54)
      rw [show values13 (190 : Fin 264) = Real.sqrt 2 + values8 (1 : Fin 20) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (716 : Fin 791) (by
      change 1 + values13 (193 : Fin 264) = Real.sqrt 2 + values10 (33 : Fin 54)
      rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (722 : Fin 791) (by
      change 1 + values13 (198 : Fin 264) = Real.sqrt 2 + values10 (34 : Fin 54)
      rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (726 : Fin 791) (by
      change 1 + values13 (202 : Fin 264) = Real.sqrt 2 + values10 (35 : Fin 54)
      rw [show values13 (202 : Fin 264) = Real.sqrt 2 + values8 (4 : Fin 20) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (729 : Fin 791) (by
      change 1 + values13 (205 : Fin 264) = Real.sqrt 2 + values10 (36 : Fin 54)
      rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (731 : Fin 791) (by
      change Real.sqrt 2 + values10 (37 : Fin 54) = Real.sqrt 2 + values10 (37 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (733 : Fin 791) (by
      change 1 + values13 (208 : Fin 264) = Real.sqrt 2 + values10 (38 : Fin 54)
      rw [show values13 (208 : Fin 264) = Real.sqrt 2 + values8 (6 : Fin 20) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (735 : Fin 791) (by
      change 1 + values13 (210 : Fin 264) = Real.sqrt 2 + values10 (39 : Fin 54)
      rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (741 : Fin 791) (by
      change 1 + values13 (216 : Fin 264) = Real.sqrt 2 + values10 (40 : Fin 54)
      rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (743 : Fin 791) (by
      change 1 + values13 (218 : Fin 264) = Real.sqrt 2 + values10 (41 : Fin 54)
      rw [show values13 (218 : Fin 264) = Real.sqrt 2 + values8 (9 : Fin 20) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (746 : Fin 791) (by
      change 1 + values13 (221 : Fin 264) = Real.sqrt 2 + values10 (42 : Fin 54)
      rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (749 : Fin 791) (by
      change Real.sqrt 2 + values10 (43 : Fin 54) = Real.sqrt 2 + values10 (43 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (756 : Fin 791) (by
      change 1 + values13 (230 : Fin 264) = Real.sqrt 2 + values10 (44 : Fin 54)
      rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (761 : Fin 791) (by
      change Real.sqrt 2 + values10 (45 : Fin 54) = Real.sqrt 2 + values10 (45 : Fin 54)
      rfl
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = Real.sqrt 2 + values10 (46 : Fin 54)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (769 : Fin 791) (by
      change 1 + values13 (242 : Fin 264) = Real.sqrt 2 + values10 (47 : Fin 54)
      rw [show values13 (242 : Fin 264) = 1 + values11 (69 : Fin 91) by rfl]
      rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (771 : Fin 791) (by
      change 1 + values13 (244 : Fin 264) = Real.sqrt 2 + values10 (48 : Fin 54)
      rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = Real.sqrt 2 + values10 (49 : Fin 54)
      rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (779 : Fin 791) (by
      change 1 + values13 (252 : Fin 264) = Real.sqrt 2 + values10 (50 : Fin 54)
      rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = Real.sqrt 2 + values10 (51 : Fin 54)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (785 : Fin 791) (by
      change 1 + values13 (258 : Fin 264) = Real.sqrt 2 + values10 (52 : Fin 54)
      rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (788 : Fin 791) (by
      change 1 + values13 (261 : Fin 264) = Real.sqrt 2 + values10 (53 : Fin 54)
      rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem two_add_values10_mem_range_values15 (i : Fin 54) :
    (Set.range values15) (2 + values10 i) := by
  fin_cases i
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 2 + values10 (0 : Fin 54)
      rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (660 : Fin 791) (by
      change 1 + values13 (148 : Fin 264) = 2 + values10 (1 : Fin 54)
      rw [show values13 (148 : Fin 264) = 1 + values11 (2 : Fin 91) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (661 : Fin 791) (by
      change 1 + values13 (149 : Fin 264) = 2 + values10 (2 : Fin 54)
      rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 2 + values10 (3 : Fin 54)
      rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (667 : Fin 791) (by
      change 1 + values13 (154 : Fin 264) = 2 + values10 (4 : Fin 54)
      rw [show values13 (154 : Fin 264) = 1 + values11 (7 : Fin 91) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 2 + values10 (5 : Fin 54)
      rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (673 : Fin 791) (by
      change 1 + values13 (158 : Fin 264) = 2 + values10 (6 : Fin 54)
      rw [show values13 (158 : Fin 264) = 1 + values11 (10 : Fin 91) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (675 : Fin 791) (by
      change 1 + values13 (159 : Fin 264) = 2 + values10 (7 : Fin 54)
      rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 2 + values10 (8 : Fin 54)
      rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (680 : Fin 791) (by
      change 1 + values13 (163 : Fin 264) = 2 + values10 (9 : Fin 54)
      rw [show values13 (163 : Fin 264) = 1 + values11 (14 : Fin 91) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (682 : Fin 791) (by
      change 1 + values13 (164 : Fin 264) = 2 + values10 (10 : Fin 54)
      rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 2 + values10 (11 : Fin 54)
      rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 2 + values10 (12 : Fin 54)
      rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (692 : Fin 791) (by
      change 1 + values13 (172 : Fin 264) = 2 + values10 (13 : Fin 54)
      rw [show values13 (172 : Fin 264) = 1 + values11 (21 : Fin 91) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (694 : Fin 791) (by
      change 1 + values13 (173 : Fin 264) = 2 + values10 (14 : Fin 54)
      rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 2 + values10 (15 : Fin 54)
      rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (702 : Fin 791) (by
      change 1 + values13 (180 : Fin 264) = 2 + values10 (16 : Fin 54)
      rw [show values13 (180 : Fin 264) = 1 + values11 (26 : Fin 91) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 2 + values10 (17 : Fin 54)
      rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (708 : Fin 791) (by
      change 1 + values13 (185 : Fin 264) = 2 + values10 (18 : Fin 54)
      rw [show values13 (185 : Fin 264) = 1 + values11 (30 : Fin 91) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 2 + values10 (19 : Fin 54)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (712 : Fin 791) (by
      change 1 + values13 (189 : Fin 264) = 2 + values10 (20 : Fin 54)
      rw [show values13 (189 : Fin 264) = 1 + values11 (33 : Fin 91) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (714 : Fin 791) (by
      change 1 + values13 (191 : Fin 264) = 2 + values10 (21 : Fin 54)
      rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 2 + values10 (22 : Fin 54)
      rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (724 : Fin 791) (by
      change 1 + values13 (200 : Fin 264) = 2 + values10 (23 : Fin 54)
      rw [show values13 (200 : Fin 264) = 1 + values11 (39 : Fin 91) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 2 + values10 (24 : Fin 54)
      rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (728 : Fin 791) (by
      change 1 + values13 (204 : Fin 264) = 2 + values10 (25 : Fin 54)
      rw [show values13 (204 : Fin 264) = 1 + values11 (42 : Fin 91) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (732 : Fin 791) (by
      change 1 + values13 (207 : Fin 264) = 2 + values10 (26 : Fin 54)
      rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (734 : Fin 791) (by
      change 1 + values13 (209 : Fin 264) = 2 + values10 (27 : Fin 54)
      rw [show values13 (209 : Fin 264) = 1 + values11 (45 : Fin 91) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 2 + values10 (28 : Fin 54)
      rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (739 : Fin 791) (by
      change 1 + values13 (214 : Fin 264) = 2 + values10 (29 : Fin 54)
      rw [show values13 (214 : Fin 264) = 1 + values11 (48 : Fin 91) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (742 : Fin 791) (by
      change 1 + values13 (217 : Fin 264) = 2 + values10 (30 : Fin 54)
      rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 2 + values10 (31 : Fin 54)
      rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (750 : Fin 791) (by
      change 1 + values13 (224 : Fin 264) = 2 + values10 (32 : Fin 54)
      rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (751 : Fin 791) (by
      change 1 + values13 (225 : Fin 264) = 2 + values10 (33 : Fin 54)
      rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 2 + values10 (34 : Fin 54)
      rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (757 : Fin 791) (by
      change 1 + values13 (231 : Fin 264) = 2 + values10 (35 : Fin 54)
      rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 2 + values10 (36 : Fin 54)
      rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (760 : Fin 791) (by
      change 1 + values13 (234 : Fin 264) = 2 + values10 (37 : Fin 54)
      rw [show values13 (234 : Fin 264) = 1 + values11 (62 : Fin 91) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (762 : Fin 791) (by
      change 1 + values13 (235 : Fin 264) = 2 + values10 (38 : Fin 54)
      rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (763 : Fin 791) (by
      change 1 + values13 (236 : Fin 264) = 2 + values10 (39 : Fin 54)
      rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 2 + values10 (40 : Fin 54)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (768 : Fin 791) (by
      change 1 + values13 (241 : Fin 264) = 2 + values10 (41 : Fin 54)
      rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (770 : Fin 791) (by
      change 1 + values13 (243 : Fin 264) = 2 + values10 (42 : Fin 54)
      rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (771 : Fin 791) (by
      change 1 + values13 (244 : Fin 264) = 2 + values10 (43 : Fin 54)
      rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 2 + values10 (44 : Fin 54)
      rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = 2 + values10 (45 : Fin 54)
      rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 2 + values10 (46 : Fin 54)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (778 : Fin 791) (by
      change 1 + values13 (251 : Fin 264) = 2 + values10 (47 : Fin 54)
      rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (780 : Fin 791) (by
      change 1 + values13 (253 : Fin 264) = 2 + values10 (48 : Fin 54)
      rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 2 + values10 (49 : Fin 54)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (784 : Fin 791) (by
      change 1 + values13 (257 : Fin 264) = 2 + values10 (50 : Fin 54)
      rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 2 + values10 (51 : Fin 54)
      rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (788 : Fin 791) (by
      change 1 + values13 (261 : Fin 264) = 2 + values10 (52 : Fin 54)
      rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (789 : Fin 791) (by
      change 1 + values13 (262 : Fin 264) = 2 + values10 (53 : Fin 54)
      rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )



end Expr
end A158415
end LeanProofs
