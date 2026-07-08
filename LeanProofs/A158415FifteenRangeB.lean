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

end Expr
end A158415
end LeanProofs
