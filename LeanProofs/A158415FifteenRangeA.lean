import LeanProofs.A158415FifteenTable

/-!
# First size-fifteen range lemmas for OEIS A158415

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
theorem sqrt_values14_mem_range_values15 (i : Fin 455) :
    (Set.range values15) (Real.sqrt (values14 i)) := by
  fin_cases i
  next =>
    exact Exists.intro (0 : Fin 791) (by
      change Real.sqrt (values14 (0 : Fin 455)) = Real.sqrt (values14 (0 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (1 : Fin 791) (by
      change Real.sqrt (values14 (1 : Fin 455)) = Real.sqrt (values14 (1 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (2 : Fin 791) (by
      change Real.sqrt (values14 (2 : Fin 455)) = Real.sqrt (values14 (2 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (3 : Fin 791) (by
      change Real.sqrt (values14 (3 : Fin 455)) = Real.sqrt (values14 (3 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (4 : Fin 791) (by
      change Real.sqrt (values14 (4 : Fin 455)) = Real.sqrt (values14 (4 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (5 : Fin 791) (by
      change Real.sqrt (values14 (5 : Fin 455)) = Real.sqrt (values14 (5 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (6 : Fin 791) (by
      change Real.sqrt (values14 (6 : Fin 455)) = Real.sqrt (values14 (6 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (7 : Fin 791) (by
      change Real.sqrt (values14 (7 : Fin 455)) = Real.sqrt (values14 (7 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (8 : Fin 791) (by
      change Real.sqrt (values14 (8 : Fin 455)) = Real.sqrt (values14 (8 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (9 : Fin 791) (by
      change Real.sqrt (values14 (9 : Fin 455)) = Real.sqrt (values14 (9 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (10 : Fin 791) (by
      change Real.sqrt (values14 (10 : Fin 455)) = Real.sqrt (values14 (10 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (11 : Fin 791) (by
      change Real.sqrt (values14 (11 : Fin 455)) = Real.sqrt (values14 (11 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (12 : Fin 791) (by
      change Real.sqrt (values14 (12 : Fin 455)) = Real.sqrt (values14 (12 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (13 : Fin 791) (by
      change Real.sqrt (values14 (13 : Fin 455)) = Real.sqrt (values14 (13 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (14 : Fin 791) (by
      change Real.sqrt (values14 (14 : Fin 455)) = Real.sqrt (values14 (14 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (15 : Fin 791) (by
      change Real.sqrt (values14 (15 : Fin 455)) = Real.sqrt (values14 (15 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (16 : Fin 791) (by
      change Real.sqrt (values14 (16 : Fin 455)) = Real.sqrt (values14 (16 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (17 : Fin 791) (by
      change Real.sqrt (values14 (17 : Fin 455)) = Real.sqrt (values14 (17 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (18 : Fin 791) (by
      change Real.sqrt (values14 (18 : Fin 455)) = Real.sqrt (values14 (18 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (19 : Fin 791) (by
      change Real.sqrt (values14 (19 : Fin 455)) = Real.sqrt (values14 (19 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (20 : Fin 791) (by
      change Real.sqrt (values14 (20 : Fin 455)) = Real.sqrt (values14 (20 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (21 : Fin 791) (by
      change Real.sqrt (values14 (21 : Fin 455)) = Real.sqrt (values14 (21 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (22 : Fin 791) (by
      change Real.sqrt (values14 (22 : Fin 455)) = Real.sqrt (values14 (22 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (23 : Fin 791) (by
      change Real.sqrt (values14 (23 : Fin 455)) = Real.sqrt (values14 (23 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (24 : Fin 791) (by
      change Real.sqrt (values14 (24 : Fin 455)) = Real.sqrt (values14 (24 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (25 : Fin 791) (by
      change Real.sqrt (values14 (25 : Fin 455)) = Real.sqrt (values14 (25 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (26 : Fin 791) (by
      change Real.sqrt (values14 (26 : Fin 455)) = Real.sqrt (values14 (26 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (27 : Fin 791) (by
      change Real.sqrt (values14 (27 : Fin 455)) = Real.sqrt (values14 (27 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (28 : Fin 791) (by
      change Real.sqrt (values14 (28 : Fin 455)) = Real.sqrt (values14 (28 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (29 : Fin 791) (by
      change Real.sqrt (values14 (29 : Fin 455)) = Real.sqrt (values14 (29 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (30 : Fin 791) (by
      change Real.sqrt (values14 (30 : Fin 455)) = Real.sqrt (values14 (30 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (31 : Fin 791) (by
      change Real.sqrt (values14 (31 : Fin 455)) = Real.sqrt (values14 (31 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (32 : Fin 791) (by
      change Real.sqrt (values14 (32 : Fin 455)) = Real.sqrt (values14 (32 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (33 : Fin 791) (by
      change Real.sqrt (values14 (33 : Fin 455)) = Real.sqrt (values14 (33 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (34 : Fin 791) (by
      change Real.sqrt (values14 (34 : Fin 455)) = Real.sqrt (values14 (34 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (35 : Fin 791) (by
      change Real.sqrt (values14 (35 : Fin 455)) = Real.sqrt (values14 (35 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (36 : Fin 791) (by
      change Real.sqrt (values14 (36 : Fin 455)) = Real.sqrt (values14 (36 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (37 : Fin 791) (by
      change Real.sqrt (values14 (37 : Fin 455)) = Real.sqrt (values14 (37 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (38 : Fin 791) (by
      change Real.sqrt (values14 (38 : Fin 455)) = Real.sqrt (values14 (38 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (39 : Fin 791) (by
      change Real.sqrt (values14 (39 : Fin 455)) = Real.sqrt (values14 (39 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (40 : Fin 791) (by
      change Real.sqrt (values14 (40 : Fin 455)) = Real.sqrt (values14 (40 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (41 : Fin 791) (by
      change Real.sqrt (values14 (41 : Fin 455)) = Real.sqrt (values14 (41 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (42 : Fin 791) (by
      change Real.sqrt (values14 (42 : Fin 455)) = Real.sqrt (values14 (42 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (43 : Fin 791) (by
      change Real.sqrt (values14 (43 : Fin 455)) = Real.sqrt (values14 (43 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (44 : Fin 791) (by
      change Real.sqrt (values14 (44 : Fin 455)) = Real.sqrt (values14 (44 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (45 : Fin 791) (by
      change Real.sqrt (values14 (45 : Fin 455)) = Real.sqrt (values14 (45 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (46 : Fin 791) (by
      change Real.sqrt (values14 (46 : Fin 455)) = Real.sqrt (values14 (46 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (47 : Fin 791) (by
      change Real.sqrt (values14 (47 : Fin 455)) = Real.sqrt (values14 (47 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (48 : Fin 791) (by
      change Real.sqrt (values14 (48 : Fin 455)) = Real.sqrt (values14 (48 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (49 : Fin 791) (by
      change Real.sqrt (values14 (49 : Fin 455)) = Real.sqrt (values14 (49 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (50 : Fin 791) (by
      change Real.sqrt (values14 (50 : Fin 455)) = Real.sqrt (values14 (50 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (51 : Fin 791) (by
      change Real.sqrt (values14 (51 : Fin 455)) = Real.sqrt (values14 (51 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (52 : Fin 791) (by
      change Real.sqrt (values14 (52 : Fin 455)) = Real.sqrt (values14 (52 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (53 : Fin 791) (by
      change Real.sqrt (values14 (53 : Fin 455)) = Real.sqrt (values14 (53 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (54 : Fin 791) (by
      change Real.sqrt (values14 (54 : Fin 455)) = Real.sqrt (values14 (54 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (55 : Fin 791) (by
      change Real.sqrt (values14 (55 : Fin 455)) = Real.sqrt (values14 (55 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (56 : Fin 791) (by
      change Real.sqrt (values14 (56 : Fin 455)) = Real.sqrt (values14 (56 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (57 : Fin 791) (by
      change Real.sqrt (values14 (57 : Fin 455)) = Real.sqrt (values14 (57 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (58 : Fin 791) (by
      change Real.sqrt (values14 (58 : Fin 455)) = Real.sqrt (values14 (58 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (59 : Fin 791) (by
      change Real.sqrt (values14 (59 : Fin 455)) = Real.sqrt (values14 (59 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (60 : Fin 791) (by
      change Real.sqrt (values14 (60 : Fin 455)) = Real.sqrt (values14 (60 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (61 : Fin 791) (by
      change Real.sqrt (values14 (61 : Fin 455)) = Real.sqrt (values14 (61 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (62 : Fin 791) (by
      change Real.sqrt (values14 (62 : Fin 455)) = Real.sqrt (values14 (62 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (63 : Fin 791) (by
      change Real.sqrt (values14 (63 : Fin 455)) = Real.sqrt (values14 (63 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (64 : Fin 791) (by
      change Real.sqrt (values14 (64 : Fin 455)) = Real.sqrt (values14 (64 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (65 : Fin 791) (by
      change Real.sqrt (values14 (65 : Fin 455)) = Real.sqrt (values14 (65 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (66 : Fin 791) (by
      change Real.sqrt (values14 (66 : Fin 455)) = Real.sqrt (values14 (66 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (67 : Fin 791) (by
      change Real.sqrt (values14 (67 : Fin 455)) = Real.sqrt (values14 (67 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (68 : Fin 791) (by
      change Real.sqrt (values14 (68 : Fin 455)) = Real.sqrt (values14 (68 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (69 : Fin 791) (by
      change Real.sqrt (values14 (69 : Fin 455)) = Real.sqrt (values14 (69 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (70 : Fin 791) (by
      change Real.sqrt (values14 (70 : Fin 455)) = Real.sqrt (values14 (70 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (71 : Fin 791) (by
      change Real.sqrt (values14 (71 : Fin 455)) = Real.sqrt (values14 (71 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (72 : Fin 791) (by
      change Real.sqrt (values14 (72 : Fin 455)) = Real.sqrt (values14 (72 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (73 : Fin 791) (by
      change Real.sqrt (values14 (73 : Fin 455)) = Real.sqrt (values14 (73 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (74 : Fin 791) (by
      change Real.sqrt (values14 (74 : Fin 455)) = Real.sqrt (values14 (74 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (75 : Fin 791) (by
      change Real.sqrt (values14 (75 : Fin 455)) = Real.sqrt (values14 (75 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (76 : Fin 791) (by
      change Real.sqrt (values14 (76 : Fin 455)) = Real.sqrt (values14 (76 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (77 : Fin 791) (by
      change Real.sqrt (values14 (77 : Fin 455)) = Real.sqrt (values14 (77 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (78 : Fin 791) (by
      change Real.sqrt (values14 (78 : Fin 455)) = Real.sqrt (values14 (78 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (79 : Fin 791) (by
      change Real.sqrt (values14 (79 : Fin 455)) = Real.sqrt (values14 (79 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (80 : Fin 791) (by
      change Real.sqrt (values14 (80 : Fin 455)) = Real.sqrt (values14 (80 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (81 : Fin 791) (by
      change Real.sqrt (values14 (81 : Fin 455)) = Real.sqrt (values14 (81 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (82 : Fin 791) (by
      change Real.sqrt (values14 (82 : Fin 455)) = Real.sqrt (values14 (82 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (83 : Fin 791) (by
      change Real.sqrt (values14 (83 : Fin 455)) = Real.sqrt (values14 (83 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (84 : Fin 791) (by
      change Real.sqrt (values14 (84 : Fin 455)) = Real.sqrt (values14 (84 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (85 : Fin 791) (by
      change Real.sqrt (values14 (85 : Fin 455)) = Real.sqrt (values14 (85 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (86 : Fin 791) (by
      change Real.sqrt (values14 (86 : Fin 455)) = Real.sqrt (values14 (86 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (87 : Fin 791) (by
      change Real.sqrt (values14 (87 : Fin 455)) = Real.sqrt (values14 (87 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (88 : Fin 791) (by
      change Real.sqrt (values14 (88 : Fin 455)) = Real.sqrt (values14 (88 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (89 : Fin 791) (by
      change Real.sqrt (values14 (89 : Fin 455)) = Real.sqrt (values14 (89 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (90 : Fin 791) (by
      change Real.sqrt (values14 (90 : Fin 455)) = Real.sqrt (values14 (90 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (91 : Fin 791) (by
      change Real.sqrt (values14 (91 : Fin 455)) = Real.sqrt (values14 (91 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (92 : Fin 791) (by
      change Real.sqrt (values14 (92 : Fin 455)) = Real.sqrt (values14 (92 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (93 : Fin 791) (by
      change Real.sqrt (values14 (93 : Fin 455)) = Real.sqrt (values14 (93 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (94 : Fin 791) (by
      change Real.sqrt (values14 (94 : Fin 455)) = Real.sqrt (values14 (94 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (95 : Fin 791) (by
      change Real.sqrt (values14 (95 : Fin 455)) = Real.sqrt (values14 (95 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (96 : Fin 791) (by
      change Real.sqrt (values14 (96 : Fin 455)) = Real.sqrt (values14 (96 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (97 : Fin 791) (by
      change Real.sqrt (values14 (97 : Fin 455)) = Real.sqrt (values14 (97 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (98 : Fin 791) (by
      change Real.sqrt (values14 (98 : Fin 455)) = Real.sqrt (values14 (98 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (99 : Fin 791) (by
      change Real.sqrt (values14 (99 : Fin 455)) = Real.sqrt (values14 (99 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (100 : Fin 791) (by
      change Real.sqrt (values14 (100 : Fin 455)) = Real.sqrt (values14 (100 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (101 : Fin 791) (by
      change Real.sqrt (values14 (101 : Fin 455)) = Real.sqrt (values14 (101 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (102 : Fin 791) (by
      change Real.sqrt (values14 (102 : Fin 455)) = Real.sqrt (values14 (102 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (103 : Fin 791) (by
      change Real.sqrt (values14 (103 : Fin 455)) = Real.sqrt (values14 (103 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (104 : Fin 791) (by
      change Real.sqrt (values14 (104 : Fin 455)) = Real.sqrt (values14 (104 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (105 : Fin 791) (by
      change Real.sqrt (values14 (105 : Fin 455)) = Real.sqrt (values14 (105 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (106 : Fin 791) (by
      change Real.sqrt (values14 (106 : Fin 455)) = Real.sqrt (values14 (106 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (107 : Fin 791) (by
      change Real.sqrt (values14 (107 : Fin 455)) = Real.sqrt (values14 (107 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (108 : Fin 791) (by
      change Real.sqrt (values14 (108 : Fin 455)) = Real.sqrt (values14 (108 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (109 : Fin 791) (by
      change Real.sqrt (values14 (109 : Fin 455)) = Real.sqrt (values14 (109 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (110 : Fin 791) (by
      change Real.sqrt (values14 (110 : Fin 455)) = Real.sqrt (values14 (110 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (111 : Fin 791) (by
      change Real.sqrt (values14 (111 : Fin 455)) = Real.sqrt (values14 (111 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (112 : Fin 791) (by
      change Real.sqrt (values14 (112 : Fin 455)) = Real.sqrt (values14 (112 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (113 : Fin 791) (by
      change Real.sqrt (values14 (113 : Fin 455)) = Real.sqrt (values14 (113 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (114 : Fin 791) (by
      change Real.sqrt (values14 (114 : Fin 455)) = Real.sqrt (values14 (114 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (115 : Fin 791) (by
      change Real.sqrt (values14 (115 : Fin 455)) = Real.sqrt (values14 (115 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (116 : Fin 791) (by
      change Real.sqrt (values14 (116 : Fin 455)) = Real.sqrt (values14 (116 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (117 : Fin 791) (by
      change Real.sqrt (values14 (117 : Fin 455)) = Real.sqrt (values14 (117 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (118 : Fin 791) (by
      change Real.sqrt (values14 (118 : Fin 455)) = Real.sqrt (values14 (118 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (119 : Fin 791) (by
      change Real.sqrt (values14 (119 : Fin 455)) = Real.sqrt (values14 (119 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (120 : Fin 791) (by
      change Real.sqrt (values14 (120 : Fin 455)) = Real.sqrt (values14 (120 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (121 : Fin 791) (by
      change Real.sqrt (values14 (121 : Fin 455)) = Real.sqrt (values14 (121 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (122 : Fin 791) (by
      change Real.sqrt (values14 (122 : Fin 455)) = Real.sqrt (values14 (122 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (123 : Fin 791) (by
      change Real.sqrt (values14 (123 : Fin 455)) = Real.sqrt (values14 (123 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (124 : Fin 791) (by
      change Real.sqrt (values14 (124 : Fin 455)) = Real.sqrt (values14 (124 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (125 : Fin 791) (by
      change Real.sqrt (values14 (125 : Fin 455)) = Real.sqrt (values14 (125 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (126 : Fin 791) (by
      change Real.sqrt (values14 (126 : Fin 455)) = Real.sqrt (values14 (126 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (127 : Fin 791) (by
      change Real.sqrt (values14 (127 : Fin 455)) = Real.sqrt (values14 (127 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (128 : Fin 791) (by
      change Real.sqrt (values14 (128 : Fin 455)) = Real.sqrt (values14 (128 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (129 : Fin 791) (by
      change Real.sqrt (values14 (129 : Fin 455)) = Real.sqrt (values14 (129 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (130 : Fin 791) (by
      change Real.sqrt (values14 (130 : Fin 455)) = Real.sqrt (values14 (130 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (131 : Fin 791) (by
      change Real.sqrt (values14 (131 : Fin 455)) = Real.sqrt (values14 (131 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (132 : Fin 791) (by
      change Real.sqrt (values14 (132 : Fin 455)) = Real.sqrt (values14 (132 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (133 : Fin 791) (by
      change Real.sqrt (values14 (133 : Fin 455)) = Real.sqrt (values14 (133 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (134 : Fin 791) (by
      change Real.sqrt (values14 (134 : Fin 455)) = Real.sqrt (values14 (134 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (135 : Fin 791) (by
      change Real.sqrt (values14 (135 : Fin 455)) = Real.sqrt (values14 (135 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (136 : Fin 791) (by
      change Real.sqrt (values14 (136 : Fin 455)) = Real.sqrt (values14 (136 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (137 : Fin 791) (by
      change Real.sqrt (values14 (137 : Fin 455)) = Real.sqrt (values14 (137 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (138 : Fin 791) (by
      change Real.sqrt (values14 (138 : Fin 455)) = Real.sqrt (values14 (138 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (139 : Fin 791) (by
      change Real.sqrt (values14 (139 : Fin 455)) = Real.sqrt (values14 (139 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (140 : Fin 791) (by
      change Real.sqrt (values14 (140 : Fin 455)) = Real.sqrt (values14 (140 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (141 : Fin 791) (by
      change Real.sqrt (values14 (141 : Fin 455)) = Real.sqrt (values14 (141 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (142 : Fin 791) (by
      change Real.sqrt (values14 (142 : Fin 455)) = Real.sqrt (values14 (142 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (143 : Fin 791) (by
      change Real.sqrt (values14 (143 : Fin 455)) = Real.sqrt (values14 (143 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (144 : Fin 791) (by
      change Real.sqrt (values14 (144 : Fin 455)) = Real.sqrt (values14 (144 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (145 : Fin 791) (by
      change Real.sqrt (values14 (145 : Fin 455)) = Real.sqrt (values14 (145 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (146 : Fin 791) (by
      change Real.sqrt (values14 (146 : Fin 455)) = Real.sqrt (values14 (146 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (147 : Fin 791) (by
      change Real.sqrt (values14 (147 : Fin 455)) = Real.sqrt (values14 (147 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (148 : Fin 791) (by
      change Real.sqrt (values14 (148 : Fin 455)) = Real.sqrt (values14 (148 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (149 : Fin 791) (by
      change Real.sqrt (values14 (149 : Fin 455)) = Real.sqrt (values14 (149 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (150 : Fin 791) (by
      change Real.sqrt (values14 (150 : Fin 455)) = Real.sqrt (values14 (150 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (151 : Fin 791) (by
      change Real.sqrt (values14 (151 : Fin 455)) = Real.sqrt (values14 (151 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (152 : Fin 791) (by
      change Real.sqrt (values14 (152 : Fin 455)) = Real.sqrt (values14 (152 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (153 : Fin 791) (by
      change Real.sqrt (values14 (153 : Fin 455)) = Real.sqrt (values14 (153 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (154 : Fin 791) (by
      change Real.sqrt (values14 (154 : Fin 455)) = Real.sqrt (values14 (154 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (155 : Fin 791) (by
      change Real.sqrt (values14 (155 : Fin 455)) = Real.sqrt (values14 (155 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (156 : Fin 791) (by
      change Real.sqrt (values14 (156 : Fin 455)) = Real.sqrt (values14 (156 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (157 : Fin 791) (by
      change Real.sqrt (values14 (157 : Fin 455)) = Real.sqrt (values14 (157 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (158 : Fin 791) (by
      change Real.sqrt (values14 (158 : Fin 455)) = Real.sqrt (values14 (158 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (159 : Fin 791) (by
      change Real.sqrt (values14 (159 : Fin 455)) = Real.sqrt (values14 (159 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (160 : Fin 791) (by
      change Real.sqrt (values14 (160 : Fin 455)) = Real.sqrt (values14 (160 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (161 : Fin 791) (by
      change Real.sqrt (values14 (161 : Fin 455)) = Real.sqrt (values14 (161 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (162 : Fin 791) (by
      change Real.sqrt (values14 (162 : Fin 455)) = Real.sqrt (values14 (162 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (163 : Fin 791) (by
      change Real.sqrt (values14 (163 : Fin 455)) = Real.sqrt (values14 (163 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (164 : Fin 791) (by
      change Real.sqrt (values14 (164 : Fin 455)) = Real.sqrt (values14 (164 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (165 : Fin 791) (by
      change Real.sqrt (values14 (165 : Fin 455)) = Real.sqrt (values14 (165 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (166 : Fin 791) (by
      change Real.sqrt (values14 (166 : Fin 455)) = Real.sqrt (values14 (166 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (167 : Fin 791) (by
      change Real.sqrt (values14 (167 : Fin 455)) = Real.sqrt (values14 (167 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (168 : Fin 791) (by
      change Real.sqrt (values14 (168 : Fin 455)) = Real.sqrt (values14 (168 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (169 : Fin 791) (by
      change Real.sqrt (values14 (169 : Fin 455)) = Real.sqrt (values14 (169 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (170 : Fin 791) (by
      change Real.sqrt (values14 (170 : Fin 455)) = Real.sqrt (values14 (170 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (171 : Fin 791) (by
      change Real.sqrt (values14 (171 : Fin 455)) = Real.sqrt (values14 (171 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (172 : Fin 791) (by
      change Real.sqrt (values14 (172 : Fin 455)) = Real.sqrt (values14 (172 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (173 : Fin 791) (by
      change Real.sqrt (values14 (173 : Fin 455)) = Real.sqrt (values14 (173 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (174 : Fin 791) (by
      change Real.sqrt (values14 (174 : Fin 455)) = Real.sqrt (values14 (174 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (175 : Fin 791) (by
      change Real.sqrt (values14 (175 : Fin 455)) = Real.sqrt (values14 (175 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (176 : Fin 791) (by
      change Real.sqrt (values14 (176 : Fin 455)) = Real.sqrt (values14 (176 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (177 : Fin 791) (by
      change Real.sqrt (values14 (177 : Fin 455)) = Real.sqrt (values14 (177 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (178 : Fin 791) (by
      change Real.sqrt (values14 (178 : Fin 455)) = Real.sqrt (values14 (178 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (179 : Fin 791) (by
      change Real.sqrt (values14 (179 : Fin 455)) = Real.sqrt (values14 (179 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (180 : Fin 791) (by
      change Real.sqrt (values14 (180 : Fin 455)) = Real.sqrt (values14 (180 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (181 : Fin 791) (by
      change Real.sqrt (values14 (181 : Fin 455)) = Real.sqrt (values14 (181 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (182 : Fin 791) (by
      change Real.sqrt (values14 (182 : Fin 455)) = Real.sqrt (values14 (182 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (183 : Fin 791) (by
      change Real.sqrt (values14 (183 : Fin 455)) = Real.sqrt (values14 (183 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (184 : Fin 791) (by
      change Real.sqrt (values14 (184 : Fin 455)) = Real.sqrt (values14 (184 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (185 : Fin 791) (by
      change Real.sqrt (values14 (185 : Fin 455)) = Real.sqrt (values14 (185 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (186 : Fin 791) (by
      change Real.sqrt (values14 (186 : Fin 455)) = Real.sqrt (values14 (186 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (187 : Fin 791) (by
      change Real.sqrt (values14 (187 : Fin 455)) = Real.sqrt (values14 (187 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (188 : Fin 791) (by
      change Real.sqrt (values14 (188 : Fin 455)) = Real.sqrt (values14 (188 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (189 : Fin 791) (by
      change Real.sqrt (values14 (189 : Fin 455)) = Real.sqrt (values14 (189 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (190 : Fin 791) (by
      change Real.sqrt (values14 (190 : Fin 455)) = Real.sqrt (values14 (190 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (191 : Fin 791) (by
      change Real.sqrt (values14 (191 : Fin 455)) = Real.sqrt (values14 (191 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (192 : Fin 791) (by
      change Real.sqrt (values14 (192 : Fin 455)) = Real.sqrt (values14 (192 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (193 : Fin 791) (by
      change Real.sqrt (values14 (193 : Fin 455)) = Real.sqrt (values14 (193 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (194 : Fin 791) (by
      change Real.sqrt (values14 (194 : Fin 455)) = Real.sqrt (values14 (194 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (195 : Fin 791) (by
      change Real.sqrt (values14 (195 : Fin 455)) = Real.sqrt (values14 (195 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (196 : Fin 791) (by
      change Real.sqrt (values14 (196 : Fin 455)) = Real.sqrt (values14 (196 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (197 : Fin 791) (by
      change Real.sqrt (values14 (197 : Fin 455)) = Real.sqrt (values14 (197 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (198 : Fin 791) (by
      change Real.sqrt (values14 (198 : Fin 455)) = Real.sqrt (values14 (198 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (199 : Fin 791) (by
      change Real.sqrt (values14 (199 : Fin 455)) = Real.sqrt (values14 (199 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (200 : Fin 791) (by
      change Real.sqrt (values14 (200 : Fin 455)) = Real.sqrt (values14 (200 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (201 : Fin 791) (by
      change Real.sqrt (values14 (201 : Fin 455)) = Real.sqrt (values14 (201 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (202 : Fin 791) (by
      change Real.sqrt (values14 (202 : Fin 455)) = Real.sqrt (values14 (202 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (203 : Fin 791) (by
      change Real.sqrt (values14 (203 : Fin 455)) = Real.sqrt (values14 (203 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (204 : Fin 791) (by
      change Real.sqrt (values14 (204 : Fin 455)) = Real.sqrt (values14 (204 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (205 : Fin 791) (by
      change Real.sqrt (values14 (205 : Fin 455)) = Real.sqrt (values14 (205 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (206 : Fin 791) (by
      change Real.sqrt (values14 (206 : Fin 455)) = Real.sqrt (values14 (206 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (207 : Fin 791) (by
      change Real.sqrt (values14 (207 : Fin 455)) = Real.sqrt (values14 (207 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (208 : Fin 791) (by
      change Real.sqrt (values14 (208 : Fin 455)) = Real.sqrt (values14 (208 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (209 : Fin 791) (by
      change Real.sqrt (values14 (209 : Fin 455)) = Real.sqrt (values14 (209 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (210 : Fin 791) (by
      change Real.sqrt (values14 (210 : Fin 455)) = Real.sqrt (values14 (210 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (211 : Fin 791) (by
      change Real.sqrt (values14 (211 : Fin 455)) = Real.sqrt (values14 (211 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (212 : Fin 791) (by
      change Real.sqrt (values14 (212 : Fin 455)) = Real.sqrt (values14 (212 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (213 : Fin 791) (by
      change Real.sqrt (values14 (213 : Fin 455)) = Real.sqrt (values14 (213 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (214 : Fin 791) (by
      change Real.sqrt (values14 (214 : Fin 455)) = Real.sqrt (values14 (214 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (215 : Fin 791) (by
      change Real.sqrt (values14 (215 : Fin 455)) = Real.sqrt (values14 (215 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (216 : Fin 791) (by
      change Real.sqrt (values14 (216 : Fin 455)) = Real.sqrt (values14 (216 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (217 : Fin 791) (by
      change Real.sqrt (values14 (217 : Fin 455)) = Real.sqrt (values14 (217 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (218 : Fin 791) (by
      change Real.sqrt (values14 (218 : Fin 455)) = Real.sqrt (values14 (218 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (219 : Fin 791) (by
      change Real.sqrt (values14 (219 : Fin 455)) = Real.sqrt (values14 (219 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (220 : Fin 791) (by
      change Real.sqrt (values14 (220 : Fin 455)) = Real.sqrt (values14 (220 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (221 : Fin 791) (by
      change Real.sqrt (values14 (221 : Fin 455)) = Real.sqrt (values14 (221 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (222 : Fin 791) (by
      change Real.sqrt (values14 (222 : Fin 455)) = Real.sqrt (values14 (222 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (223 : Fin 791) (by
      change Real.sqrt (values14 (223 : Fin 455)) = Real.sqrt (values14 (223 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (224 : Fin 791) (by
      change Real.sqrt (values14 (224 : Fin 455)) = Real.sqrt (values14 (224 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (225 : Fin 791) (by
      change Real.sqrt (values14 (225 : Fin 455)) = Real.sqrt (values14 (225 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (226 : Fin 791) (by
      change Real.sqrt (values14 (226 : Fin 455)) = Real.sqrt (values14 (226 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (227 : Fin 791) (by
      change Real.sqrt (values14 (227 : Fin 455)) = Real.sqrt (values14 (227 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (228 : Fin 791) (by
      change Real.sqrt (values14 (228 : Fin 455)) = Real.sqrt (values14 (228 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (229 : Fin 791) (by
      change Real.sqrt (values14 (229 : Fin 455)) = Real.sqrt (values14 (229 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (230 : Fin 791) (by
      change Real.sqrt (values14 (230 : Fin 455)) = Real.sqrt (values14 (230 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (231 : Fin 791) (by
      change Real.sqrt (values14 (231 : Fin 455)) = Real.sqrt (values14 (231 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (232 : Fin 791) (by
      change Real.sqrt (values14 (232 : Fin 455)) = Real.sqrt (values14 (232 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (233 : Fin 791) (by
      change Real.sqrt (values14 (233 : Fin 455)) = Real.sqrt (values14 (233 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (234 : Fin 791) (by
      change Real.sqrt (values14 (234 : Fin 455)) = Real.sqrt (values14 (234 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (235 : Fin 791) (by
      change Real.sqrt (values14 (235 : Fin 455)) = Real.sqrt (values14 (235 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (236 : Fin 791) (by
      change Real.sqrt (values14 (236 : Fin 455)) = Real.sqrt (values14 (236 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (237 : Fin 791) (by
      change Real.sqrt (values14 (237 : Fin 455)) = Real.sqrt (values14 (237 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (238 : Fin 791) (by
      change Real.sqrt (values14 (238 : Fin 455)) = Real.sqrt (values14 (238 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (239 : Fin 791) (by
      change Real.sqrt (values14 (239 : Fin 455)) = Real.sqrt (values14 (239 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (240 : Fin 791) (by
      change Real.sqrt (values14 (240 : Fin 455)) = Real.sqrt (values14 (240 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (241 : Fin 791) (by
      change Real.sqrt (values14 (241 : Fin 455)) = Real.sqrt (values14 (241 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (242 : Fin 791) (by
      change Real.sqrt (values14 (242 : Fin 455)) = Real.sqrt (values14 (242 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (243 : Fin 791) (by
      change Real.sqrt (values14 (243 : Fin 455)) = Real.sqrt (values14 (243 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (244 : Fin 791) (by
      change Real.sqrt (values14 (244 : Fin 455)) = Real.sqrt (values14 (244 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (245 : Fin 791) (by
      change Real.sqrt (values14 (245 : Fin 455)) = Real.sqrt (values14 (245 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (246 : Fin 791) (by
      change Real.sqrt (values14 (246 : Fin 455)) = Real.sqrt (values14 (246 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (247 : Fin 791) (by
      change Real.sqrt (values14 (247 : Fin 455)) = Real.sqrt (values14 (247 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (248 : Fin 791) (by
      change Real.sqrt (values14 (248 : Fin 455)) = Real.sqrt (values14 (248 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (249 : Fin 791) (by
      change Real.sqrt (values14 (249 : Fin 455)) = Real.sqrt (values14 (249 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (250 : Fin 791) (by
      change Real.sqrt (values14 (250 : Fin 455)) = Real.sqrt (values14 (250 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (251 : Fin 791) (by
      change Real.sqrt (values14 (251 : Fin 455)) = Real.sqrt (values14 (251 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (252 : Fin 791) (by
      change Real.sqrt (values14 (252 : Fin 455)) = Real.sqrt (values14 (252 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (253 : Fin 791) (by
      change Real.sqrt (values14 (253 : Fin 455)) = Real.sqrt (values14 (253 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (254 : Fin 791) (by
      change Real.sqrt (values14 (254 : Fin 455)) = Real.sqrt (values14 (254 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (255 : Fin 791) (by
      change Real.sqrt (values14 (255 : Fin 455)) = Real.sqrt (values14 (255 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (256 : Fin 791) (by
      change Real.sqrt (values14 (256 : Fin 455)) = Real.sqrt (values14 (256 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (257 : Fin 791) (by
      change Real.sqrt (values14 (257 : Fin 455)) = Real.sqrt (values14 (257 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (258 : Fin 791) (by
      change Real.sqrt (values14 (258 : Fin 455)) = Real.sqrt (values14 (258 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (259 : Fin 791) (by
      change Real.sqrt (values14 (259 : Fin 455)) = Real.sqrt (values14 (259 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (260 : Fin 791) (by
      change Real.sqrt (values14 (260 : Fin 455)) = Real.sqrt (values14 (260 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (261 : Fin 791) (by
      change Real.sqrt (values14 (261 : Fin 455)) = Real.sqrt (values14 (261 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (262 : Fin 791) (by
      change Real.sqrt (values14 (262 : Fin 455)) = Real.sqrt (values14 (262 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (263 : Fin 791) (by
      change Real.sqrt (values14 (263 : Fin 455)) = Real.sqrt (values14 (263 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (264 : Fin 791) (by
      change Real.sqrt (values14 (264 : Fin 455)) = Real.sqrt (values14 (264 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (265 : Fin 791) (by
      change Real.sqrt (values14 (265 : Fin 455)) = Real.sqrt (values14 (265 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (266 : Fin 791) (by
      change Real.sqrt (values14 (266 : Fin 455)) = Real.sqrt (values14 (266 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (267 : Fin 791) (by
      change Real.sqrt (values14 (267 : Fin 455)) = Real.sqrt (values14 (267 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (268 : Fin 791) (by
      change Real.sqrt (values14 (268 : Fin 455)) = Real.sqrt (values14 (268 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (269 : Fin 791) (by
      change Real.sqrt (values14 (269 : Fin 455)) = Real.sqrt (values14 (269 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (270 : Fin 791) (by
      change Real.sqrt (values14 (270 : Fin 455)) = Real.sqrt (values14 (270 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (271 : Fin 791) (by
      change Real.sqrt (values14 (271 : Fin 455)) = Real.sqrt (values14 (271 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (272 : Fin 791) (by
      change Real.sqrt (values14 (272 : Fin 455)) = Real.sqrt (values14 (272 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (273 : Fin 791) (by
      change Real.sqrt (values14 (273 : Fin 455)) = Real.sqrt (values14 (273 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (274 : Fin 791) (by
      change Real.sqrt (values14 (274 : Fin 455)) = Real.sqrt (values14 (274 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (275 : Fin 791) (by
      change Real.sqrt (values14 (275 : Fin 455)) = Real.sqrt (values14 (275 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (276 : Fin 791) (by
      change Real.sqrt (values14 (276 : Fin 455)) = Real.sqrt (values14 (276 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (277 : Fin 791) (by
      change Real.sqrt (values14 (277 : Fin 455)) = Real.sqrt (values14 (277 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (278 : Fin 791) (by
      change Real.sqrt (values14 (278 : Fin 455)) = Real.sqrt (values14 (278 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (279 : Fin 791) (by
      change Real.sqrt (values14 (279 : Fin 455)) = Real.sqrt (values14 (279 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (280 : Fin 791) (by
      change Real.sqrt (values14 (280 : Fin 455)) = Real.sqrt (values14 (280 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (281 : Fin 791) (by
      change Real.sqrt (values14 (281 : Fin 455)) = Real.sqrt (values14 (281 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (282 : Fin 791) (by
      change Real.sqrt (values14 (282 : Fin 455)) = Real.sqrt (values14 (282 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (283 : Fin 791) (by
      change Real.sqrt (values14 (283 : Fin 455)) = Real.sqrt (values14 (283 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (284 : Fin 791) (by
      change Real.sqrt (values14 (284 : Fin 455)) = Real.sqrt (values14 (284 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (285 : Fin 791) (by
      change Real.sqrt (values14 (285 : Fin 455)) = Real.sqrt (values14 (285 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (286 : Fin 791) (by
      change Real.sqrt (values14 (286 : Fin 455)) = Real.sqrt (values14 (286 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (287 : Fin 791) (by
      change Real.sqrt (values14 (287 : Fin 455)) = Real.sqrt (values14 (287 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (288 : Fin 791) (by
      change Real.sqrt (values14 (288 : Fin 455)) = Real.sqrt (values14 (288 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (289 : Fin 791) (by
      change Real.sqrt (values14 (289 : Fin 455)) = Real.sqrt (values14 (289 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (290 : Fin 791) (by
      change Real.sqrt (values14 (290 : Fin 455)) = Real.sqrt (values14 (290 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (291 : Fin 791) (by
      change Real.sqrt (values14 (291 : Fin 455)) = Real.sqrt (values14 (291 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (292 : Fin 791) (by
      change Real.sqrt (values14 (292 : Fin 455)) = Real.sqrt (values14 (292 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (293 : Fin 791) (by
      change Real.sqrt (values14 (293 : Fin 455)) = Real.sqrt (values14 (293 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (294 : Fin 791) (by
      change Real.sqrt (values14 (294 : Fin 455)) = Real.sqrt (values14 (294 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (295 : Fin 791) (by
      change Real.sqrt (values14 (295 : Fin 455)) = Real.sqrt (values14 (295 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (296 : Fin 791) (by
      change Real.sqrt (values14 (296 : Fin 455)) = Real.sqrt (values14 (296 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (297 : Fin 791) (by
      change Real.sqrt (values14 (297 : Fin 455)) = Real.sqrt (values14 (297 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (298 : Fin 791) (by
      change Real.sqrt (values14 (298 : Fin 455)) = Real.sqrt (values14 (298 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (299 : Fin 791) (by
      change Real.sqrt (values14 (299 : Fin 455)) = Real.sqrt (values14 (299 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (300 : Fin 791) (by
      change Real.sqrt (values14 (300 : Fin 455)) = Real.sqrt (values14 (300 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (301 : Fin 791) (by
      change Real.sqrt (values14 (301 : Fin 455)) = Real.sqrt (values14 (301 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (302 : Fin 791) (by
      change Real.sqrt (values14 (302 : Fin 455)) = Real.sqrt (values14 (302 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (303 : Fin 791) (by
      change Real.sqrt (values14 (303 : Fin 455)) = Real.sqrt (values14 (303 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (304 : Fin 791) (by
      change Real.sqrt (values14 (304 : Fin 455)) = Real.sqrt (values14 (304 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (305 : Fin 791) (by
      change Real.sqrt (values14 (305 : Fin 455)) = Real.sqrt (values14 (305 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (306 : Fin 791) (by
      change Real.sqrt (values14 (306 : Fin 455)) = Real.sqrt (values14 (306 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (307 : Fin 791) (by
      change Real.sqrt (values14 (307 : Fin 455)) = Real.sqrt (values14 (307 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (308 : Fin 791) (by
      change Real.sqrt (values14 (308 : Fin 455)) = Real.sqrt (values14 (308 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (309 : Fin 791) (by
      change Real.sqrt (values14 (309 : Fin 455)) = Real.sqrt (values14 (309 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (310 : Fin 791) (by
      change Real.sqrt (values14 (310 : Fin 455)) = Real.sqrt (values14 (310 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (311 : Fin 791) (by
      change Real.sqrt (values14 (311 : Fin 455)) = Real.sqrt (values14 (311 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (312 : Fin 791) (by
      change Real.sqrt (values14 (312 : Fin 455)) = Real.sqrt (values14 (312 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (313 : Fin 791) (by
      change Real.sqrt (values14 (313 : Fin 455)) = Real.sqrt (values14 (313 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (314 : Fin 791) (by
      change Real.sqrt (values14 (314 : Fin 455)) = Real.sqrt (values14 (314 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (315 : Fin 791) (by
      change Real.sqrt (values14 (315 : Fin 455)) = Real.sqrt (values14 (315 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (316 : Fin 791) (by
      change Real.sqrt (values14 (316 : Fin 455)) = Real.sqrt (values14 (316 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (317 : Fin 791) (by
      change Real.sqrt (values14 (317 : Fin 455)) = Real.sqrt (values14 (317 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (318 : Fin 791) (by
      change Real.sqrt (values14 (318 : Fin 455)) = Real.sqrt (values14 (318 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (319 : Fin 791) (by
      change Real.sqrt (values14 (319 : Fin 455)) = Real.sqrt (values14 (319 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (320 : Fin 791) (by
      change Real.sqrt (values14 (320 : Fin 455)) = Real.sqrt (values14 (320 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (321 : Fin 791) (by
      change Real.sqrt (values14 (321 : Fin 455)) = Real.sqrt (values14 (321 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (322 : Fin 791) (by
      change Real.sqrt (values14 (322 : Fin 455)) = Real.sqrt (values14 (322 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (323 : Fin 791) (by
      change Real.sqrt (values14 (323 : Fin 455)) = Real.sqrt (values14 (323 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (324 : Fin 791) (by
      change Real.sqrt (values14 (324 : Fin 455)) = Real.sqrt (values14 (324 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (325 : Fin 791) (by
      change Real.sqrt (values14 (325 : Fin 455)) = Real.sqrt (values14 (325 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (326 : Fin 791) (by
      change Real.sqrt (values14 (326 : Fin 455)) = Real.sqrt (values14 (326 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (327 : Fin 791) (by
      change Real.sqrt (values14 (327 : Fin 455)) = Real.sqrt (values14 (327 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (328 : Fin 791) (by
      change Real.sqrt (values14 (328 : Fin 455)) = Real.sqrt (values14 (328 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (329 : Fin 791) (by
      change Real.sqrt (values14 (329 : Fin 455)) = Real.sqrt (values14 (329 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (330 : Fin 791) (by
      change Real.sqrt (values14 (330 : Fin 455)) = Real.sqrt (values14 (330 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (331 : Fin 791) (by
      change Real.sqrt (values14 (331 : Fin 455)) = Real.sqrt (values14 (331 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (332 : Fin 791) (by
      change Real.sqrt (values14 (332 : Fin 455)) = Real.sqrt (values14 (332 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (333 : Fin 791) (by
      change Real.sqrt (values14 (333 : Fin 455)) = Real.sqrt (values14 (333 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (334 : Fin 791) (by
      change Real.sqrt (values14 (334 : Fin 455)) = Real.sqrt (values14 (334 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (335 : Fin 791) (by
      change Real.sqrt (values14 (335 : Fin 455)) = Real.sqrt (values14 (335 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (336 : Fin 791) (by
      change Real.sqrt (values14 (336 : Fin 455)) = Real.sqrt (values14 (336 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (337 : Fin 791) (by
      change Real.sqrt (values14 (337 : Fin 455)) = Real.sqrt (values14 (337 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (338 : Fin 791) (by
      change Real.sqrt (values14 (338 : Fin 455)) = Real.sqrt (values14 (338 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (339 : Fin 791) (by
      change Real.sqrt (values14 (339 : Fin 455)) = Real.sqrt (values14 (339 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (340 : Fin 791) (by
      change Real.sqrt (values14 (340 : Fin 455)) = Real.sqrt (values14 (340 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (341 : Fin 791) (by
      change Real.sqrt (values14 (341 : Fin 455)) = Real.sqrt (values14 (341 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (342 : Fin 791) (by
      change Real.sqrt (values14 (342 : Fin 455)) = Real.sqrt (values14 (342 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (343 : Fin 791) (by
      change Real.sqrt (values14 (343 : Fin 455)) = Real.sqrt (values14 (343 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (344 : Fin 791) (by
      change Real.sqrt (values14 (344 : Fin 455)) = Real.sqrt (values14 (344 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (345 : Fin 791) (by
      change Real.sqrt (values14 (345 : Fin 455)) = Real.sqrt (values14 (345 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (346 : Fin 791) (by
      change Real.sqrt (values14 (346 : Fin 455)) = Real.sqrt (values14 (346 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (347 : Fin 791) (by
      change Real.sqrt (values14 (347 : Fin 455)) = Real.sqrt (values14 (347 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (348 : Fin 791) (by
      change Real.sqrt (values14 (348 : Fin 455)) = Real.sqrt (values14 (348 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (349 : Fin 791) (by
      change Real.sqrt (values14 (349 : Fin 455)) = Real.sqrt (values14 (349 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (350 : Fin 791) (by
      change Real.sqrt (values14 (350 : Fin 455)) = Real.sqrt (values14 (350 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (351 : Fin 791) (by
      change Real.sqrt (values14 (351 : Fin 455)) = Real.sqrt (values14 (351 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (352 : Fin 791) (by
      change Real.sqrt (values14 (352 : Fin 455)) = Real.sqrt (values14 (352 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (353 : Fin 791) (by
      change Real.sqrt (values14 (353 : Fin 455)) = Real.sqrt (values14 (353 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (354 : Fin 791) (by
      change Real.sqrt (values14 (354 : Fin 455)) = Real.sqrt (values14 (354 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (355 : Fin 791) (by
      change Real.sqrt (values14 (355 : Fin 455)) = Real.sqrt (values14 (355 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (356 : Fin 791) (by
      change Real.sqrt (values14 (356 : Fin 455)) = Real.sqrt (values14 (356 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (357 : Fin 791) (by
      change Real.sqrt (values14 (357 : Fin 455)) = Real.sqrt (values14 (357 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (358 : Fin 791) (by
      change Real.sqrt (values14 (358 : Fin 455)) = Real.sqrt (values14 (358 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (359 : Fin 791) (by
      change Real.sqrt (values14 (359 : Fin 455)) = Real.sqrt (values14 (359 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (360 : Fin 791) (by
      change Real.sqrt (values14 (360 : Fin 455)) = Real.sqrt (values14 (360 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (361 : Fin 791) (by
      change Real.sqrt (values14 (361 : Fin 455)) = Real.sqrt (values14 (361 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (362 : Fin 791) (by
      change Real.sqrt (values14 (362 : Fin 455)) = Real.sqrt (values14 (362 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (363 : Fin 791) (by
      change Real.sqrt (values14 (363 : Fin 455)) = Real.sqrt (values14 (363 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (364 : Fin 791) (by
      change Real.sqrt (values14 (364 : Fin 455)) = Real.sqrt (values14 (364 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (365 : Fin 791) (by
      change Real.sqrt (values14 (365 : Fin 455)) = Real.sqrt (values14 (365 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (366 : Fin 791) (by
      change Real.sqrt (values14 (366 : Fin 455)) = Real.sqrt (values14 (366 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (367 : Fin 791) (by
      change Real.sqrt (values14 (367 : Fin 455)) = Real.sqrt (values14 (367 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (368 : Fin 791) (by
      change Real.sqrt (values14 (368 : Fin 455)) = Real.sqrt (values14 (368 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (369 : Fin 791) (by
      change Real.sqrt (values14 (369 : Fin 455)) = Real.sqrt (values14 (369 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (370 : Fin 791) (by
      change Real.sqrt (values14 (370 : Fin 455)) = Real.sqrt (values14 (370 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (371 : Fin 791) (by
      change Real.sqrt (values14 (371 : Fin 455)) = Real.sqrt (values14 (371 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (372 : Fin 791) (by
      change Real.sqrt (values14 (372 : Fin 455)) = Real.sqrt (values14 (372 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (373 : Fin 791) (by
      change Real.sqrt (values14 (373 : Fin 455)) = Real.sqrt (values14 (373 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (374 : Fin 791) (by
      change Real.sqrt (values14 (374 : Fin 455)) = Real.sqrt (values14 (374 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (375 : Fin 791) (by
      change Real.sqrt (values14 (375 : Fin 455)) = Real.sqrt (values14 (375 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (376 : Fin 791) (by
      change Real.sqrt (values14 (376 : Fin 455)) = Real.sqrt (values14 (376 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (377 : Fin 791) (by
      change Real.sqrt (values14 (377 : Fin 455)) = Real.sqrt (values14 (377 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (378 : Fin 791) (by
      change Real.sqrt (values14 (378 : Fin 455)) = Real.sqrt (values14 (378 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (379 : Fin 791) (by
      change Real.sqrt (values14 (379 : Fin 455)) = Real.sqrt (values14 (379 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (380 : Fin 791) (by
      change Real.sqrt (values14 (380 : Fin 455)) = Real.sqrt (values14 (380 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (381 : Fin 791) (by
      change Real.sqrt (values14 (381 : Fin 455)) = Real.sqrt (values14 (381 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (382 : Fin 791) (by
      change Real.sqrt (values14 (382 : Fin 455)) = Real.sqrt (values14 (382 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (383 : Fin 791) (by
      change Real.sqrt (values14 (383 : Fin 455)) = Real.sqrt (values14 (383 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (384 : Fin 791) (by
      change Real.sqrt (values14 (384 : Fin 455)) = Real.sqrt (values14 (384 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (385 : Fin 791) (by
      change Real.sqrt (values14 (385 : Fin 455)) = Real.sqrt (values14 (385 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (386 : Fin 791) (by
      change Real.sqrt (values14 (386 : Fin 455)) = Real.sqrt (values14 (386 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (387 : Fin 791) (by
      change Real.sqrt (values14 (387 : Fin 455)) = Real.sqrt (values14 (387 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (388 : Fin 791) (by
      change Real.sqrt (values14 (388 : Fin 455)) = Real.sqrt (values14 (388 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (389 : Fin 791) (by
      change Real.sqrt (values14 (389 : Fin 455)) = Real.sqrt (values14 (389 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (390 : Fin 791) (by
      change Real.sqrt (values14 (390 : Fin 455)) = Real.sqrt (values14 (390 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (391 : Fin 791) (by
      change Real.sqrt (values14 (391 : Fin 455)) = Real.sqrt (values14 (391 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (392 : Fin 791) (by
      change Real.sqrt (values14 (392 : Fin 455)) = Real.sqrt (values14 (392 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (393 : Fin 791) (by
      change Real.sqrt (values14 (393 : Fin 455)) = Real.sqrt (values14 (393 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (394 : Fin 791) (by
      change Real.sqrt (values14 (394 : Fin 455)) = Real.sqrt (values14 (394 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (395 : Fin 791) (by
      change Real.sqrt (values14 (395 : Fin 455)) = Real.sqrt (values14 (395 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (396 : Fin 791) (by
      change Real.sqrt (values14 (396 : Fin 455)) = Real.sqrt (values14 (396 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (397 : Fin 791) (by
      change Real.sqrt (values14 (397 : Fin 455)) = Real.sqrt (values14 (397 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (398 : Fin 791) (by
      change Real.sqrt (values14 (398 : Fin 455)) = Real.sqrt (values14 (398 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (399 : Fin 791) (by
      change Real.sqrt (values14 (399 : Fin 455)) = Real.sqrt (values14 (399 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (400 : Fin 791) (by
      change Real.sqrt (values14 (400 : Fin 455)) = Real.sqrt (values14 (400 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (401 : Fin 791) (by
      change Real.sqrt (values14 (401 : Fin 455)) = Real.sqrt (values14 (401 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (402 : Fin 791) (by
      change Real.sqrt (values14 (402 : Fin 455)) = Real.sqrt (values14 (402 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (403 : Fin 791) (by
      change Real.sqrt (values14 (403 : Fin 455)) = Real.sqrt (values14 (403 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (404 : Fin 791) (by
      change Real.sqrt (values14 (404 : Fin 455)) = Real.sqrt (values14 (404 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (405 : Fin 791) (by
      change Real.sqrt (values14 (405 : Fin 455)) = Real.sqrt (values14 (405 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (406 : Fin 791) (by
      change Real.sqrt (values14 (406 : Fin 455)) = Real.sqrt (values14 (406 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (407 : Fin 791) (by
      change Real.sqrt (values14 (407 : Fin 455)) = Real.sqrt (values14 (407 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (408 : Fin 791) (by
      change Real.sqrt (values14 (408 : Fin 455)) = Real.sqrt (values14 (408 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (409 : Fin 791) (by
      change Real.sqrt (values14 (409 : Fin 455)) = Real.sqrt (values14 (409 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (410 : Fin 791) (by
      change Real.sqrt (values14 (410 : Fin 455)) = Real.sqrt (values14 (410 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (411 : Fin 791) (by
      change Real.sqrt (values14 (411 : Fin 455)) = Real.sqrt (values14 (411 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (412 : Fin 791) (by
      change Real.sqrt (values14 (412 : Fin 455)) = Real.sqrt (values14 (412 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (413 : Fin 791) (by
      change Real.sqrt (values14 (413 : Fin 455)) = Real.sqrt (values14 (413 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (414 : Fin 791) (by
      change Real.sqrt (values14 (414 : Fin 455)) = Real.sqrt (values14 (414 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (415 : Fin 791) (by
      change Real.sqrt (values14 (415 : Fin 455)) = Real.sqrt (values14 (415 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (416 : Fin 791) (by
      change Real.sqrt (values14 (416 : Fin 455)) = Real.sqrt (values14 (416 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (417 : Fin 791) (by
      change Real.sqrt (values14 (417 : Fin 455)) = Real.sqrt (values14 (417 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (418 : Fin 791) (by
      change Real.sqrt (values14 (418 : Fin 455)) = Real.sqrt (values14 (418 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (419 : Fin 791) (by
      change Real.sqrt (values14 (419 : Fin 455)) = Real.sqrt (values14 (419 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (420 : Fin 791) (by
      change Real.sqrt (values14 (420 : Fin 455)) = Real.sqrt (values14 (420 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (421 : Fin 791) (by
      change Real.sqrt (values14 (421 : Fin 455)) = Real.sqrt (values14 (421 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (422 : Fin 791) (by
      change Real.sqrt (values14 (422 : Fin 455)) = Real.sqrt (values14 (422 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (423 : Fin 791) (by
      change Real.sqrt (values14 (423 : Fin 455)) = Real.sqrt (values14 (423 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (424 : Fin 791) (by
      change Real.sqrt (values14 (424 : Fin 455)) = Real.sqrt (values14 (424 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (425 : Fin 791) (by
      change Real.sqrt (values14 (425 : Fin 455)) = Real.sqrt (values14 (425 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (426 : Fin 791) (by
      change Real.sqrt (values14 (426 : Fin 455)) = Real.sqrt (values14 (426 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (427 : Fin 791) (by
      change Real.sqrt (values14 (427 : Fin 455)) = Real.sqrt (values14 (427 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (428 : Fin 791) (by
      change Real.sqrt (values14 (428 : Fin 455)) = Real.sqrt (values14 (428 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (429 : Fin 791) (by
      change Real.sqrt (values14 (429 : Fin 455)) = Real.sqrt (values14 (429 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (430 : Fin 791) (by
      change Real.sqrt (values14 (430 : Fin 455)) = Real.sqrt (values14 (430 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (436 : Fin 791) (by
      change Real.sqrt (values14 (431 : Fin 455)) = Real.sqrt (values14 (431 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (440 : Fin 791) (by
      change Real.sqrt (values14 (432 : Fin 455)) = Real.sqrt (values14 (432 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (445 : Fin 791) (by
      change Real.sqrt (values14 (433 : Fin 455)) = Real.sqrt (values14 (433 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (451 : Fin 791) (by
      change Real.sqrt (values14 (434 : Fin 455)) = Real.sqrt (values14 (434 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (452 : Fin 791) (by
      change Real.sqrt (values14 (435 : Fin 455)) = Real.sqrt (values14 (435 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (456 : Fin 791) (by
      change Real.sqrt (values14 (436 : Fin 455)) = Real.sqrt (values14 (436 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (461 : Fin 791) (by
      change Real.sqrt (values14 (437 : Fin 455)) = Real.sqrt (values14 (437 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (462 : Fin 791) (by
      change Real.sqrt (values14 (438 : Fin 455)) = Real.sqrt (values14 (438 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (464 : Fin 791) (by
      change Real.sqrt (values14 (439 : Fin 455)) = Real.sqrt (values14 (439 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (469 : Fin 791) (by
      change Real.sqrt (values14 (440 : Fin 455)) = Real.sqrt (values14 (440 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (477 : Fin 791) (by
      change Real.sqrt (values14 (441 : Fin 455)) = Real.sqrt (values14 (441 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (484 : Fin 791) (by
      change Real.sqrt (values14 (442 : Fin 455)) = Real.sqrt (values14 (442 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (489 : Fin 791) (by
      change Real.sqrt (values14 (443 : Fin 455)) = Real.sqrt (values14 (443 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (492 : Fin 791) (by
      change Real.sqrt (values14 (444 : Fin 455)) = Real.sqrt (values14 (444 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (497 : Fin 791) (by
      change Real.sqrt (values14 (445 : Fin 455)) = Real.sqrt (values14 (445 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (504 : Fin 791) (by
      change Real.sqrt (values14 (446 : Fin 455)) = Real.sqrt (values14 (446 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (518 : Fin 791) (by
      change Real.sqrt (values14 (447 : Fin 455)) = Real.sqrt (values14 (447 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (524 : Fin 791) (by
      change Real.sqrt (values14 (448 : Fin 455)) = Real.sqrt (values14 (448 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (530 : Fin 791) (by
      change Real.sqrt (values14 (449 : Fin 455)) = Real.sqrt (values14 (449 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (539 : Fin 791) (by
      change Real.sqrt (values14 (450 : Fin 455)) = Real.sqrt (values14 (450 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (550 : Fin 791) (by
      change Real.sqrt (values14 (451 : Fin 455)) = Real.sqrt (values14 (451 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (570 : Fin 791) (by
      change Real.sqrt (values14 (452 : Fin 455)) = Real.sqrt (values14 (452 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (589 : Fin 791) (by
      change Real.sqrt (values14 (453 : Fin 455)) = Real.sqrt (values14 (453 : Fin 455))
      rfl
    )
  next =>
    exact Exists.intro (614 : Fin 791) (by
      change Real.sqrt (values14 (454 : Fin 455)) = Real.sqrt (values14 (454 : Fin 455))
      rfl
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem one_add_values13_mem_range_values15 (i : Fin 264) :
    (Set.range values15) (1 + values13 i) := by
  fin_cases i
  next =>
    exact Exists.intro (430 : Fin 791) (by
      change Real.sqrt (values14 (430 : Fin 455)) = 1 + values13 (0 : Fin 264)
      rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values13 (0 : Fin 264) = Real.sqrt (values12 (0 : Fin 154)) by rfl]
      rw [show values12 (0 : Fin 154) = Real.sqrt (values11 (0 : Fin 91)) by rfl]
      rw [show values11 (0 : Fin 91) = Real.sqrt (values10 (0 : Fin 54)) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (431 : Fin 791) (by
      change 1 + values13 (1 : Fin 264) = 1 + values13 (1 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (432 : Fin 791) (by
      change 1 + values13 (2 : Fin 264) = 1 + values13 (2 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (433 : Fin 791) (by
      change 1 + values13 (3 : Fin 264) = 1 + values13 (3 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (434 : Fin 791) (by
      change 1 + values13 (4 : Fin 264) = 1 + values13 (4 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (435 : Fin 791) (by
      change 1 + values13 (5 : Fin 264) = 1 + values13 (5 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (437 : Fin 791) (by
      change 1 + values13 (6 : Fin 264) = 1 + values13 (6 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (438 : Fin 791) (by
      change 1 + values13 (7 : Fin 264) = 1 + values13 (7 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (439 : Fin 791) (by
      change 1 + values13 (8 : Fin 264) = 1 + values13 (8 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (441 : Fin 791) (by
      change 1 + values13 (9 : Fin 264) = 1 + values13 (9 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (442 : Fin 791) (by
      change 1 + values13 (10 : Fin 264) = 1 + values13 (10 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (443 : Fin 791) (by
      change 1 + values13 (11 : Fin 264) = 1 + values13 (11 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (444 : Fin 791) (by
      change 1 + values13 (12 : Fin 264) = 1 + values13 (12 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (446 : Fin 791) (by
      change 1 + values13 (13 : Fin 264) = 1 + values13 (13 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (447 : Fin 791) (by
      change 1 + values13 (14 : Fin 264) = 1 + values13 (14 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (448 : Fin 791) (by
      change 1 + values13 (15 : Fin 264) = 1 + values13 (15 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (449 : Fin 791) (by
      change 1 + values13 (16 : Fin 264) = 1 + values13 (16 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (450 : Fin 791) (by
      change 1 + values13 (17 : Fin 264) = 1 + values13 (17 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (453 : Fin 791) (by
      change 1 + values13 (18 : Fin 264) = 1 + values13 (18 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (454 : Fin 791) (by
      change 1 + values13 (19 : Fin 264) = 1 + values13 (19 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (455 : Fin 791) (by
      change 1 + values13 (20 : Fin 264) = 1 + values13 (20 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (457 : Fin 791) (by
      change 1 + values13 (21 : Fin 264) = 1 + values13 (21 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (458 : Fin 791) (by
      change 1 + values13 (22 : Fin 264) = 1 + values13 (22 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (459 : Fin 791) (by
      change 1 + values13 (23 : Fin 264) = 1 + values13 (23 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (460 : Fin 791) (by
      change 1 + values13 (24 : Fin 264) = 1 + values13 (24 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (463 : Fin 791) (by
      change 1 + values13 (25 : Fin 264) = 1 + values13 (25 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (465 : Fin 791) (by
      change 1 + values13 (26 : Fin 264) = 1 + values13 (26 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (466 : Fin 791) (by
      change 1 + values13 (27 : Fin 264) = 1 + values13 (27 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (467 : Fin 791) (by
      change 1 + values13 (28 : Fin 264) = 1 + values13 (28 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (468 : Fin 791) (by
      change 1 + values13 (29 : Fin 264) = 1 + values13 (29 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (470 : Fin 791) (by
      change 1 + values13 (30 : Fin 264) = 1 + values13 (30 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (472 : Fin 791) (by
      change 1 + values13 (31 : Fin 264) = 1 + values13 (31 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (473 : Fin 791) (by
      change 1 + values13 (32 : Fin 264) = 1 + values13 (32 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (474 : Fin 791) (by
      change 1 + values13 (33 : Fin 264) = 1 + values13 (33 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (475 : Fin 791) (by
      change 1 + values13 (34 : Fin 264) = 1 + values13 (34 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (476 : Fin 791) (by
      change 1 + values13 (35 : Fin 264) = 1 + values13 (35 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (478 : Fin 791) (by
      change 1 + values13 (36 : Fin 264) = 1 + values13 (36 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (479 : Fin 791) (by
      change 1 + values13 (37 : Fin 264) = 1 + values13 (37 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (480 : Fin 791) (by
      change 1 + values13 (38 : Fin 264) = 1 + values13 (38 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (481 : Fin 791) (by
      change 1 + values13 (39 : Fin 264) = 1 + values13 (39 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (483 : Fin 791) (by
      change 1 + values13 (40 : Fin 264) = 1 + values13 (40 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (485 : Fin 791) (by
      change 1 + values13 (41 : Fin 264) = 1 + values13 (41 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (486 : Fin 791) (by
      change 1 + values13 (42 : Fin 264) = 1 + values13 (42 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (487 : Fin 791) (by
      change 1 + values13 (43 : Fin 264) = 1 + values13 (43 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (488 : Fin 791) (by
      change 1 + values13 (44 : Fin 264) = 1 + values13 (44 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (491 : Fin 791) (by
      change 1 + values13 (45 : Fin 264) = 1 + values13 (45 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (493 : Fin 791) (by
      change 1 + values13 (46 : Fin 264) = 1 + values13 (46 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (494 : Fin 791) (by
      change 1 + values13 (47 : Fin 264) = 1 + values13 (47 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (495 : Fin 791) (by
      change 1 + values13 (48 : Fin 264) = 1 + values13 (48 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (496 : Fin 791) (by
      change 1 + values13 (49 : Fin 264) = 1 + values13 (49 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (498 : Fin 791) (by
      change 1 + values13 (50 : Fin 264) = 1 + values13 (50 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (500 : Fin 791) (by
      change 1 + values13 (51 : Fin 264) = 1 + values13 (51 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (501 : Fin 791) (by
      change 1 + values13 (52 : Fin 264) = 1 + values13 (52 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (502 : Fin 791) (by
      change 1 + values13 (53 : Fin 264) = 1 + values13 (53 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (503 : Fin 791) (by
      change 1 + values13 (54 : Fin 264) = 1 + values13 (54 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (505 : Fin 791) (by
      change 1 + values13 (55 : Fin 264) = 1 + values13 (55 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (507 : Fin 791) (by
      change 1 + values13 (56 : Fin 264) = 1 + values13 (56 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (508 : Fin 791) (by
      change 1 + values13 (57 : Fin 264) = 1 + values13 (57 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (509 : Fin 791) (by
      change 1 + values13 (58 : Fin 264) = 1 + values13 (58 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (510 : Fin 791) (by
      change 1 + values13 (59 : Fin 264) = 1 + values13 (59 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (512 : Fin 791) (by
      change 1 + values13 (60 : Fin 264) = 1 + values13 (60 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (513 : Fin 791) (by
      change 1 + values13 (61 : Fin 264) = 1 + values13 (61 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (514 : Fin 791) (by
      change 1 + values13 (62 : Fin 264) = 1 + values13 (62 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (515 : Fin 791) (by
      change 1 + values13 (63 : Fin 264) = 1 + values13 (63 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (517 : Fin 791) (by
      change 1 + values13 (64 : Fin 264) = 1 + values13 (64 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (520 : Fin 791) (by
      change 1 + values13 (65 : Fin 264) = 1 + values13 (65 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (521 : Fin 791) (by
      change 1 + values13 (66 : Fin 264) = 1 + values13 (66 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (522 : Fin 791) (by
      change 1 + values13 (67 : Fin 264) = 1 + values13 (67 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (523 : Fin 791) (by
      change 1 + values13 (68 : Fin 264) = 1 + values13 (68 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (525 : Fin 791) (by
      change 1 + values13 (69 : Fin 264) = 1 + values13 (69 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (527 : Fin 791) (by
      change 1 + values13 (70 : Fin 264) = 1 + values13 (70 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (528 : Fin 791) (by
      change 1 + values13 (71 : Fin 264) = 1 + values13 (71 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (529 : Fin 791) (by
      change 1 + values13 (72 : Fin 264) = 1 + values13 (72 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (532 : Fin 791) (by
      change 1 + values13 (73 : Fin 264) = 1 + values13 (73 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (533 : Fin 791) (by
      change 1 + values13 (74 : Fin 264) = 1 + values13 (74 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (534 : Fin 791) (by
      change 1 + values13 (75 : Fin 264) = 1 + values13 (75 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (536 : Fin 791) (by
      change 1 + values13 (76 : Fin 264) = 1 + values13 (76 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (537 : Fin 791) (by
      change 1 + values13 (77 : Fin 264) = 1 + values13 (77 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (538 : Fin 791) (by
      change 1 + values13 (78 : Fin 264) = 1 + values13 (78 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (540 : Fin 791) (by
      change 1 + values13 (79 : Fin 264) = 1 + values13 (79 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (541 : Fin 791) (by
      change 1 + values13 (80 : Fin 264) = 1 + values13 (80 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (544 : Fin 791) (by
      change 1 + values13 (81 : Fin 264) = 1 + values13 (81 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (545 : Fin 791) (by
      change 1 + values13 (82 : Fin 264) = 1 + values13 (82 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (547 : Fin 791) (by
      change 1 + values13 (83 : Fin 264) = 1 + values13 (83 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (549 : Fin 791) (by
      change 1 + values13 (84 : Fin 264) = 1 + values13 (84 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (551 : Fin 791) (by
      change 1 + values13 (85 : Fin 264) = 1 + values13 (85 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (554 : Fin 791) (by
      change 1 + values13 (86 : Fin 264) = 1 + values13 (86 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (555 : Fin 791) (by
      change 1 + values13 (87 : Fin 264) = 1 + values13 (87 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (556 : Fin 791) (by
      change 1 + values13 (88 : Fin 264) = 1 + values13 (88 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (558 : Fin 791) (by
      change 1 + values13 (89 : Fin 264) = 1 + values13 (89 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (560 : Fin 791) (by
      change 1 + values13 (90 : Fin 264) = 1 + values13 (90 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (561 : Fin 791) (by
      change 1 + values13 (91 : Fin 264) = 1 + values13 (91 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (562 : Fin 791) (by
      change 1 + values13 (92 : Fin 264) = 1 + values13 (92 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (563 : Fin 791) (by
      change 1 + values13 (93 : Fin 264) = 1 + values13 (93 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (566 : Fin 791) (by
      change 1 + values13 (94 : Fin 264) = 1 + values13 (94 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (567 : Fin 791) (by
      change 1 + values13 (95 : Fin 264) = 1 + values13 (95 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (569 : Fin 791) (by
      change 1 + values13 (96 : Fin 264) = 1 + values13 (96 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (571 : Fin 791) (by
      change 1 + values13 (97 : Fin 264) = 1 + values13 (97 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (572 : Fin 791) (by
      change 1 + values13 (98 : Fin 264) = 1 + values13 (98 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (574 : Fin 791) (by
      change 1 + values13 (99 : Fin 264) = 1 + values13 (99 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (576 : Fin 791) (by
      change 1 + values13 (100 : Fin 264) = 1 + values13 (100 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (577 : Fin 791) (by
      change 1 + values13 (101 : Fin 264) = 1 + values13 (101 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (579 : Fin 791) (by
      change 1 + values13 (102 : Fin 264) = 1 + values13 (102 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (580 : Fin 791) (by
      change 1 + values13 (103 : Fin 264) = 1 + values13 (103 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (581 : Fin 791) (by
      change 1 + values13 (104 : Fin 264) = 1 + values13 (104 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (584 : Fin 791) (by
      change 1 + values13 (105 : Fin 264) = 1 + values13 (105 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (585 : Fin 791) (by
      change 1 + values13 (106 : Fin 264) = 1 + values13 (106 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (587 : Fin 791) (by
      change 1 + values13 (107 : Fin 264) = 1 + values13 (107 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (590 : Fin 791) (by
      change 1 + values13 (108 : Fin 264) = 1 + values13 (108 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (591 : Fin 791) (by
      change 1 + values13 (109 : Fin 264) = 1 + values13 (109 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (592 : Fin 791) (by
      change 1 + values13 (110 : Fin 264) = 1 + values13 (110 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (593 : Fin 791) (by
      change 1 + values13 (111 : Fin 264) = 1 + values13 (111 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (595 : Fin 791) (by
      change 1 + values13 (112 : Fin 264) = 1 + values13 (112 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (596 : Fin 791) (by
      change 1 + values13 (113 : Fin 264) = 1 + values13 (113 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (597 : Fin 791) (by
      change 1 + values13 (114 : Fin 264) = 1 + values13 (114 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (599 : Fin 791) (by
      change 1 + values13 (115 : Fin 264) = 1 + values13 (115 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (600 : Fin 791) (by
      change 1 + values13 (116 : Fin 264) = 1 + values13 (116 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (601 : Fin 791) (by
      change 1 + values13 (117 : Fin 264) = 1 + values13 (117 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (603 : Fin 791) (by
      change 1 + values13 (118 : Fin 264) = 1 + values13 (118 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (605 : Fin 791) (by
      change 1 + values13 (119 : Fin 264) = 1 + values13 (119 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (606 : Fin 791) (by
      change 1 + values13 (120 : Fin 264) = 1 + values13 (120 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (608 : Fin 791) (by
      change 1 + values13 (121 : Fin 264) = 1 + values13 (121 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (612 : Fin 791) (by
      change 1 + values13 (122 : Fin 264) = 1 + values13 (122 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (615 : Fin 791) (by
      change 1 + values13 (123 : Fin 264) = 1 + values13 (123 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (616 : Fin 791) (by
      change 1 + values13 (124 : Fin 264) = 1 + values13 (124 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (619 : Fin 791) (by
      change 1 + values13 (125 : Fin 264) = 1 + values13 (125 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (620 : Fin 791) (by
      change 1 + values13 (126 : Fin 264) = 1 + values13 (126 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (621 : Fin 791) (by
      change 1 + values13 (127 : Fin 264) = 1 + values13 (127 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (623 : Fin 791) (by
      change 1 + values13 (128 : Fin 264) = 1 + values13 (128 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (624 : Fin 791) (by
      change 1 + values13 (129 : Fin 264) = 1 + values13 (129 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (626 : Fin 791) (by
      change 1 + values13 (130 : Fin 264) = 1 + values13 (130 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (627 : Fin 791) (by
      change 1 + values13 (131 : Fin 264) = 1 + values13 (131 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (629 : Fin 791) (by
      change 1 + values13 (132 : Fin 264) = 1 + values13 (132 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (631 : Fin 791) (by
      change 1 + values13 (133 : Fin 264) = 1 + values13 (133 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (633 : Fin 791) (by
      change 1 + values13 (134 : Fin 264) = 1 + values13 (134 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (634 : Fin 791) (by
      change 1 + values13 (135 : Fin 264) = 1 + values13 (135 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (636 : Fin 791) (by
      change 1 + values13 (136 : Fin 264) = 1 + values13 (136 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (637 : Fin 791) (by
      change 1 + values13 (137 : Fin 264) = 1 + values13 (137 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (638 : Fin 791) (by
      change 1 + values13 (138 : Fin 264) = 1 + values13 (138 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (639 : Fin 791) (by
      change 1 + values13 (139 : Fin 264) = 1 + values13 (139 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (644 : Fin 791) (by
      change 1 + values13 (140 : Fin 264) = 1 + values13 (140 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (646 : Fin 791) (by
      change 1 + values13 (141 : Fin 264) = 1 + values13 (141 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (649 : Fin 791) (by
      change 1 + values13 (142 : Fin 264) = 1 + values13 (142 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (651 : Fin 791) (by
      change 1 + values13 (143 : Fin 264) = 1 + values13 (143 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (653 : Fin 791) (by
      change 1 + values13 (144 : Fin 264) = 1 + values13 (144 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (655 : Fin 791) (by
      change 1 + values13 (145 : Fin 264) = 1 + values13 (145 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 1 + values13 (146 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (659 : Fin 791) (by
      change 1 + values13 (147 : Fin 264) = 1 + values13 (147 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (660 : Fin 791) (by
      change 1 + values13 (148 : Fin 264) = 1 + values13 (148 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (661 : Fin 791) (by
      change 1 + values13 (149 : Fin 264) = 1 + values13 (149 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (663 : Fin 791) (by
      change 1 + values13 (150 : Fin 264) = 1 + values13 (150 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 1 + values13 (151 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (665 : Fin 791) (by
      change 1 + values13 (152 : Fin 264) = 1 + values13 (152 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (666 : Fin 791) (by
      change 1 + values13 (153 : Fin 264) = 1 + values13 (153 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (667 : Fin 791) (by
      change 1 + values13 (154 : Fin 264) = 1 + values13 (154 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 1 + values13 (155 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (670 : Fin 791) (by
      change 1 + values13 (156 : Fin 264) = 1 + values13 (156 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (672 : Fin 791) (by
      change 1 + values13 (157 : Fin 264) = 1 + values13 (157 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (673 : Fin 791) (by
      change 1 + values13 (158 : Fin 264) = 1 + values13 (158 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (675 : Fin 791) (by
      change 1 + values13 (159 : Fin 264) = 1 + values13 (159 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 1 + values13 (160 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (678 : Fin 791) (by
      change 1 + values13 (161 : Fin 264) = 1 + values13 (161 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (679 : Fin 791) (by
      change 1 + values13 (162 : Fin 264) = 1 + values13 (162 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (680 : Fin 791) (by
      change 1 + values13 (163 : Fin 264) = 1 + values13 (163 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (682 : Fin 791) (by
      change 1 + values13 (164 : Fin 264) = 1 + values13 (164 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (683 : Fin 791) (by
      change 1 + values13 (165 : Fin 264) = 1 + values13 (165 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 1 + values13 (166 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (686 : Fin 791) (by
      change 1 + values13 (167 : Fin 264) = 1 + values13 (167 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (687 : Fin 791) (by
      change 1 + values13 (168 : Fin 264) = 1 + values13 (168 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (688 : Fin 791) (by
      change 1 + values13 (169 : Fin 264) = 1 + values13 (169 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 1 + values13 (170 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (690 : Fin 791) (by
      change 1 + values13 (171 : Fin 264) = 1 + values13 (171 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (692 : Fin 791) (by
      change 1 + values13 (172 : Fin 264) = 1 + values13 (172 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (694 : Fin 791) (by
      change 1 + values13 (173 : Fin 264) = 1 + values13 (173 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (695 : Fin 791) (by
      change 1 + values13 (174 : Fin 264) = 1 + values13 (174 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (696 : Fin 791) (by
      change 1 + values13 (175 : Fin 264) = 1 + values13 (175 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (697 : Fin 791) (by
      change 1 + values13 (176 : Fin 264) = 1 + values13 (176 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 1 + values13 (177 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (700 : Fin 791) (by
      change 1 + values13 (178 : Fin 264) = 1 + values13 (178 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (701 : Fin 791) (by
      change 1 + values13 (179 : Fin 264) = 1 + values13 (179 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (702 : Fin 791) (by
      change 1 + values13 (180 : Fin 264) = 1 + values13 (180 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (704 : Fin 791) (by
      change 1 + values13 (181 : Fin 264) = 1 + values13 (181 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 1 + values13 (182 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (706 : Fin 791) (by
      change 1 + values13 (183 : Fin 264) = 1 + values13 (183 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (707 : Fin 791) (by
      change 1 + values13 (184 : Fin 264) = 1 + values13 (184 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (708 : Fin 791) (by
      change 1 + values13 (185 : Fin 264) = 1 + values13 (185 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (709 : Fin 791) (by
      change 1 + values13 (186 : Fin 264) = 1 + values13 (186 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 1 + values13 (187 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (711 : Fin 791) (by
      change 1 + values13 (188 : Fin 264) = 1 + values13 (188 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (712 : Fin 791) (by
      change 1 + values13 (189 : Fin 264) = 1 + values13 (189 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (713 : Fin 791) (by
      change 1 + values13 (190 : Fin 264) = 1 + values13 (190 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (714 : Fin 791) (by
      change 1 + values13 (191 : Fin 264) = 1 + values13 (191 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (715 : Fin 791) (by
      change 1 + values13 (192 : Fin 264) = 1 + values13 (192 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (716 : Fin 791) (by
      change 1 + values13 (193 : Fin 264) = 1 + values13 (193 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (718 : Fin 791) (by
      change 1 + values13 (194 : Fin 264) = 1 + values13 (194 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 1 + values13 (195 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (720 : Fin 791) (by
      change 1 + values13 (196 : Fin 264) = 1 + values13 (196 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (721 : Fin 791) (by
      change 1 + values13 (197 : Fin 264) = 1 + values13 (197 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (722 : Fin 791) (by
      change 1 + values13 (198 : Fin 264) = 1 + values13 (198 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (723 : Fin 791) (by
      change 1 + values13 (199 : Fin 264) = 1 + values13 (199 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (724 : Fin 791) (by
      change 1 + values13 (200 : Fin 264) = 1 + values13 (200 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 1 + values13 (201 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (726 : Fin 791) (by
      change 1 + values13 (202 : Fin 264) = 1 + values13 (202 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (727 : Fin 791) (by
      change 1 + values13 (203 : Fin 264) = 1 + values13 (203 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (728 : Fin 791) (by
      change 1 + values13 (204 : Fin 264) = 1 + values13 (204 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (729 : Fin 791) (by
      change 1 + values13 (205 : Fin 264) = 1 + values13 (205 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (730 : Fin 791) (by
      change 1 + values13 (206 : Fin 264) = 1 + values13 (206 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (732 : Fin 791) (by
      change 1 + values13 (207 : Fin 264) = 1 + values13 (207 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (733 : Fin 791) (by
      change 1 + values13 (208 : Fin 264) = 1 + values13 (208 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (734 : Fin 791) (by
      change 1 + values13 (209 : Fin 264) = 1 + values13 (209 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (735 : Fin 791) (by
      change 1 + values13 (210 : Fin 264) = 1 + values13 (210 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 1 + values13 (211 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (737 : Fin 791) (by
      change 1 + values13 (212 : Fin 264) = 1 + values13 (212 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (738 : Fin 791) (by
      change 1 + values13 (213 : Fin 264) = 1 + values13 (213 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (739 : Fin 791) (by
      change 1 + values13 (214 : Fin 264) = 1 + values13 (214 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (740 : Fin 791) (by
      change 1 + values13 (215 : Fin 264) = 1 + values13 (215 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (741 : Fin 791) (by
      change 1 + values13 (216 : Fin 264) = 1 + values13 (216 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (742 : Fin 791) (by
      change 1 + values13 (217 : Fin 264) = 1 + values13 (217 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (743 : Fin 791) (by
      change 1 + values13 (218 : Fin 264) = 1 + values13 (218 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (744 : Fin 791) (by
      change 1 + values13 (219 : Fin 264) = 1 + values13 (219 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (745 : Fin 791) (by
      change 1 + values13 (220 : Fin 264) = 1 + values13 (220 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (746 : Fin 791) (by
      change 1 + values13 (221 : Fin 264) = 1 + values13 (221 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 1 + values13 (222 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (748 : Fin 791) (by
      change 1 + values13 (223 : Fin 264) = 1 + values13 (223 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (750 : Fin 791) (by
      change 1 + values13 (224 : Fin 264) = 1 + values13 (224 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (751 : Fin 791) (by
      change 1 + values13 (225 : Fin 264) = 1 + values13 (225 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (752 : Fin 791) (by
      change 1 + values13 (226 : Fin 264) = 1 + values13 (226 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 1 + values13 (227 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (754 : Fin 791) (by
      change 1 + values13 (228 : Fin 264) = 1 + values13 (228 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (755 : Fin 791) (by
      change 1 + values13 (229 : Fin 264) = 1 + values13 (229 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (756 : Fin 791) (by
      change 1 + values13 (230 : Fin 264) = 1 + values13 (230 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (757 : Fin 791) (by
      change 1 + values13 (231 : Fin 264) = 1 + values13 (231 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 1 + values13 (232 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (759 : Fin 791) (by
      change 1 + values13 (233 : Fin 264) = 1 + values13 (233 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (760 : Fin 791) (by
      change 1 + values13 (234 : Fin 264) = 1 + values13 (234 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (762 : Fin 791) (by
      change 1 + values13 (235 : Fin 264) = 1 + values13 (235 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (763 : Fin 791) (by
      change 1 + values13 (236 : Fin 264) = 1 + values13 (236 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (764 : Fin 791) (by
      change 1 + values13 (237 : Fin 264) = 1 + values13 (237 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 1 + values13 (238 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (766 : Fin 791) (by
      change 1 + values13 (239 : Fin 264) = 1 + values13 (239 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (767 : Fin 791) (by
      change 1 + values13 (240 : Fin 264) = 1 + values13 (240 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (768 : Fin 791) (by
      change 1 + values13 (241 : Fin 264) = 1 + values13 (241 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (769 : Fin 791) (by
      change 1 + values13 (242 : Fin 264) = 1 + values13 (242 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (770 : Fin 791) (by
      change 1 + values13 (243 : Fin 264) = 1 + values13 (243 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (771 : Fin 791) (by
      change 1 + values13 (244 : Fin 264) = 1 + values13 (244 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (772 : Fin 791) (by
      change 1 + values13 (245 : Fin 264) = 1 + values13 (245 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 1 + values13 (246 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = 1 + values13 (247 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (775 : Fin 791) (by
      change 1 + values13 (248 : Fin 264) = 1 + values13 (248 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 1 + values13 (249 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (777 : Fin 791) (by
      change 1 + values13 (250 : Fin 264) = 1 + values13 (250 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (778 : Fin 791) (by
      change 1 + values13 (251 : Fin 264) = 1 + values13 (251 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (779 : Fin 791) (by
      change 1 + values13 (252 : Fin 264) = 1 + values13 (252 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (780 : Fin 791) (by
      change 1 + values13 (253 : Fin 264) = 1 + values13 (253 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (781 : Fin 791) (by
      change 1 + values13 (254 : Fin 264) = 1 + values13 (254 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 1 + values13 (255 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (783 : Fin 791) (by
      change 1 + values13 (256 : Fin 264) = 1 + values13 (256 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (784 : Fin 791) (by
      change 1 + values13 (257 : Fin 264) = 1 + values13 (257 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (785 : Fin 791) (by
      change 1 + values13 (258 : Fin 264) = 1 + values13 (258 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 1 + values13 (259 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (787 : Fin 791) (by
      change 1 + values13 (260 : Fin 264) = 1 + values13 (260 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (788 : Fin 791) (by
      change 1 + values13 (261 : Fin 264) = 1 + values13 (261 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (789 : Fin 791) (by
      change 1 + values13 (262 : Fin 264) = 1 + values13 (262 : Fin 264)
      rfl
    )
  next =>
    exact Exists.intro (790 : Fin 791) (by
      change 1 + values13 (263 : Fin 264) = 1 + values13 (263 : Fin 264)
      rfl
    )


set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem one_add_values12_mem_range_values15 (i : Fin 154) :
    (Set.range values15) (1 + values12 i) := by
  fin_cases i
  next =>
    exact Exists.intro (430 : Fin 791) (by
      change Real.sqrt (values14 (430 : Fin 455)) = 1 + values12 (0 : Fin 154)
      rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values12 (0 : Fin 154) = Real.sqrt (values11 (0 : Fin 91)) by rfl]
      rw [show values11 (0 : Fin 91) = Real.sqrt (values10 (0 : Fin 54)) by rfl]
      rw [show values10 (0 : Fin 54) = Real.sqrt (values9 (0 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (432 : Fin 791) (by
      change 1 + values13 (2 : Fin 264) = 1 + values12 (1 : Fin 154)
      rw [show values13 (2 : Fin 264) = Real.sqrt (values12 (2 : Fin 154)) by rfl]
      rw [show values12 (2 : Fin 154) = Real.sqrt (values11 (2 : Fin 91)) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      rw [show values12 (1 : Fin 154) = Real.sqrt (values11 (1 : Fin 91)) by rfl]
      rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (433 : Fin 791) (by
      change 1 + values13 (3 : Fin 264) = 1 + values12 (2 : Fin 154)
      rw [show values13 (3 : Fin 264) = Real.sqrt (values12 (3 : Fin 154)) by rfl]
      rw [show values12 (3 : Fin 154) = Real.sqrt (values11 (3 : Fin 91)) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values12 (2 : Fin 154) = Real.sqrt (values11 (2 : Fin 91)) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (435 : Fin 791) (by
      change 1 + values13 (5 : Fin 264) = 1 + values12 (3 : Fin 154)
      rw [show values13 (5 : Fin 264) = Real.sqrt (values12 (5 : Fin 154)) by rfl]
      rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values12 (3 : Fin 154) = Real.sqrt (values11 (3 : Fin 91)) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (438 : Fin 791) (by
      change 1 + values13 (7 : Fin 264) = 1 + values12 (4 : Fin 154)
      rw [show values13 (7 : Fin 264) = Real.sqrt (values12 (7 : Fin 154)) by rfl]
      rw [show values12 (7 : Fin 154) = Real.sqrt (values11 (7 : Fin 91)) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      rw [show values12 (4 : Fin 154) = Real.sqrt (values11 (4 : Fin 91)) by rfl]
      rw [show values11 (4 : Fin 91) = Real.sqrt (values10 (4 : Fin 54)) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (439 : Fin 791) (by
      change 1 + values13 (8 : Fin 264) = 1 + values12 (5 : Fin 154)
      rw [show values13 (8 : Fin 264) = Real.sqrt (values12 (8 : Fin 154)) by rfl]
      rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (442 : Fin 791) (by
      change 1 + values13 (10 : Fin 264) = 1 + values12 (6 : Fin 154)
      rw [show values13 (10 : Fin 264) = Real.sqrt (values12 (10 : Fin 154)) by rfl]
      rw [show values12 (10 : Fin 154) = Real.sqrt (values11 (10 : Fin 91)) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      rw [show values12 (6 : Fin 154) = Real.sqrt (values11 (6 : Fin 91)) by rfl]
      rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (443 : Fin 791) (by
      change 1 + values13 (11 : Fin 264) = 1 + values12 (7 : Fin 154)
      rw [show values13 (11 : Fin 264) = Real.sqrt (values12 (11 : Fin 154)) by rfl]
      rw [show values12 (11 : Fin 154) = Real.sqrt (values11 (11 : Fin 91)) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values12 (7 : Fin 154) = Real.sqrt (values11 (7 : Fin 91)) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (444 : Fin 791) (by
      change 1 + values13 (12 : Fin 264) = 1 + values12 (8 : Fin 154)
      rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (447 : Fin 791) (by
      change 1 + values13 (14 : Fin 264) = 1 + values12 (9 : Fin 154)
      rw [show values13 (14 : Fin 264) = Real.sqrt (values12 (14 : Fin 154)) by rfl]
      rw [show values12 (14 : Fin 154) = Real.sqrt (values11 (14 : Fin 91)) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      rw [show values12 (9 : Fin 154) = Real.sqrt (values11 (9 : Fin 91)) by rfl]
      rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (448 : Fin 791) (by
      change 1 + values13 (15 : Fin 264) = 1 + values12 (10 : Fin 154)
      rw [show values13 (15 : Fin 264) = Real.sqrt (values12 (15 : Fin 154)) by rfl]
      rw [show values12 (15 : Fin 154) = Real.sqrt (values11 (15 : Fin 91)) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values12 (10 : Fin 154) = Real.sqrt (values11 (10 : Fin 91)) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (450 : Fin 791) (by
      change 1 + values13 (17 : Fin 264) = 1 + values12 (11 : Fin 154)
      rw [show values13 (17 : Fin 264) = Real.sqrt (values12 (17 : Fin 154)) by rfl]
      rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values12 (11 : Fin 154) = Real.sqrt (values11 (11 : Fin 91)) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (454 : Fin 791) (by
      change 1 + values13 (19 : Fin 264) = 1 + values12 (12 : Fin 154)
      rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
      rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (457 : Fin 791) (by
      change 1 + values13 (21 : Fin 264) = 1 + values12 (13 : Fin 154)
      rw [show values13 (21 : Fin 264) = Real.sqrt (values12 (21 : Fin 154)) by rfl]
      rw [show values12 (21 : Fin 154) = Real.sqrt (values11 (21 : Fin 91)) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      rw [show values12 (13 : Fin 154) = Real.sqrt (values11 (13 : Fin 91)) by rfl]
      rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (458 : Fin 791) (by
      change 1 + values13 (22 : Fin 264) = 1 + values12 (14 : Fin 154)
      rw [show values13 (22 : Fin 264) = Real.sqrt (values12 (22 : Fin 154)) by rfl]
      rw [show values12 (22 : Fin 154) = Real.sqrt (values11 (22 : Fin 91)) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values12 (14 : Fin 154) = Real.sqrt (values11 (14 : Fin 91)) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (460 : Fin 791) (by
      change 1 + values13 (24 : Fin 264) = 1 + values12 (15 : Fin 154)
      rw [show values13 (24 : Fin 264) = Real.sqrt (values12 (24 : Fin 154)) by rfl]
      rw [show values12 (24 : Fin 154) = Real.sqrt (values11 (24 : Fin 91)) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values12 (15 : Fin 154) = Real.sqrt (values11 (15 : Fin 91)) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (465 : Fin 791) (by
      change 1 + values13 (26 : Fin 264) = 1 + values12 (16 : Fin 154)
      rw [show values13 (26 : Fin 264) = Real.sqrt (values12 (26 : Fin 154)) by rfl]
      rw [show values12 (26 : Fin 154) = Real.sqrt (values11 (26 : Fin 91)) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      rw [show values12 (16 : Fin 154) = Real.sqrt (values11 (16 : Fin 91)) by rfl]
      rw [show values11 (16 : Fin 91) = Real.sqrt (values10 (16 : Fin 54)) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (467 : Fin 791) (by
      change 1 + values13 (28 : Fin 264) = 1 + values12 (17 : Fin 154)
      rw [show values13 (28 : Fin 264) = Real.sqrt (values12 (28 : Fin 154)) by rfl]
      rw [show values12 (28 : Fin 154) = Real.sqrt (values11 (28 : Fin 91)) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (470 : Fin 791) (by
      change 1 + values13 (30 : Fin 264) = 1 + values12 (18 : Fin 154)
      rw [show values13 (30 : Fin 264) = Real.sqrt (values12 (30 : Fin 154)) by rfl]
      rw [show values12 (30 : Fin 154) = Real.sqrt (values11 (30 : Fin 91)) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      rw [show values12 (18 : Fin 154) = Real.sqrt (values11 (18 : Fin 91)) by rfl]
      rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (472 : Fin 791) (by
      change 1 + values13 (31 : Fin 264) = 1 + values12 (19 : Fin 154)
      rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
      rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (474 : Fin 791) (by
      change 1 + values13 (33 : Fin 264) = 1 + values12 (20 : Fin 154)
      rw [show values13 (33 : Fin 264) = Real.sqrt (values12 (33 : Fin 154)) by rfl]
      rw [show values12 (33 : Fin 154) = Real.sqrt (values11 (33 : Fin 91)) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      rw [show values12 (20 : Fin 154) = Real.sqrt (values11 (20 : Fin 91)) by rfl]
      rw [show values11 (20 : Fin 91) = Real.sqrt (values10 (20 : Fin 54)) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (475 : Fin 791) (by
      change 1 + values13 (34 : Fin 264) = 1 + values12 (21 : Fin 154)
      rw [show values13 (34 : Fin 264) = Real.sqrt (values12 (34 : Fin 154)) by rfl]
      rw [show values12 (34 : Fin 154) = Real.sqrt (values11 (34 : Fin 91)) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values12 (21 : Fin 154) = Real.sqrt (values11 (21 : Fin 91)) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (478 : Fin 791) (by
      change 1 + values13 (36 : Fin 264) = 1 + values12 (22 : Fin 154)
      rw [show values13 (36 : Fin 264) = Real.sqrt (values12 (36 : Fin 154)) by rfl]
      rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values12 (22 : Fin 154) = Real.sqrt (values11 (22 : Fin 91)) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (481 : Fin 791) (by
      change 1 + values13 (39 : Fin 264) = 1 + values12 (23 : Fin 154)
      rw [show values13 (39 : Fin 264) = Real.sqrt (values12 (39 : Fin 154)) by rfl]
      rw [show values12 (39 : Fin 154) = Real.sqrt (values11 (39 : Fin 91)) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      rw [show values12 (23 : Fin 154) = Real.sqrt (values11 (23 : Fin 91)) by rfl]
      rw [show values11 (23 : Fin 91) = Real.sqrt (values10 (23 : Fin 54)) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (483 : Fin 791) (by
      change 1 + values13 (40 : Fin 264) = 1 + values12 (24 : Fin 154)
      rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
      rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values12 (24 : Fin 154) = Real.sqrt (values11 (24 : Fin 91)) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (486 : Fin 791) (by
      change 1 + values13 (42 : Fin 264) = 1 + values12 (25 : Fin 154)
      rw [show values13 (42 : Fin 264) = Real.sqrt (values12 (42 : Fin 154)) by rfl]
      rw [show values12 (42 : Fin 154) = Real.sqrt (values11 (42 : Fin 91)) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      rw [show values12 (25 : Fin 154) = Real.sqrt (values11 (25 : Fin 91)) by rfl]
      rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (488 : Fin 791) (by
      change 1 + values13 (44 : Fin 264) = 1 + values12 (26 : Fin 154)
      rw [show values13 (44 : Fin 264) = Real.sqrt (values12 (44 : Fin 154)) by rfl]
      rw [show values12 (44 : Fin 154) = Real.sqrt (values11 (44 : Fin 91)) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values12 (26 : Fin 154) = Real.sqrt (values11 (26 : Fin 91)) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (491 : Fin 791) (by
      change 1 + values13 (45 : Fin 264) = 1 + values12 (27 : Fin 154)
      rw [show values13 (45 : Fin 264) = Real.sqrt (values12 (45 : Fin 154)) by rfl]
      rw [show values12 (45 : Fin 154) = Real.sqrt (values11 (45 : Fin 91)) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      rw [show values12 (27 : Fin 154) = Real.sqrt (values11 (27 : Fin 91)) by rfl]
      rw [show values11 (27 : Fin 91) = Real.sqrt (values10 (27 : Fin 54)) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (493 : Fin 791) (by
      change 1 + values13 (46 : Fin 264) = 1 + values12 (28 : Fin 154)
      rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
      rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values12 (28 : Fin 154) = Real.sqrt (values11 (28 : Fin 91)) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (495 : Fin 791) (by
      change 1 + values13 (48 : Fin 264) = 1 + values12 (29 : Fin 154)
      rw [show values13 (48 : Fin 264) = Real.sqrt (values12 (48 : Fin 154)) by rfl]
      rw [show values12 (48 : Fin 154) = Real.sqrt (values11 (48 : Fin 91)) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      rw [show values12 (29 : Fin 154) = Real.sqrt (values11 (29 : Fin 91)) by rfl]
      rw [show values11 (29 : Fin 91) = Real.sqrt (values10 (29 : Fin 54)) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (496 : Fin 791) (by
      change 1 + values13 (49 : Fin 264) = 1 + values12 (30 : Fin 154)
      rw [show values13 (49 : Fin 264) = Real.sqrt (values12 (49 : Fin 154)) by rfl]
      rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values12 (30 : Fin 154) = Real.sqrt (values11 (30 : Fin 91)) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (500 : Fin 791) (by
      change 1 + values13 (51 : Fin 264) = 1 + values12 (31 : Fin 154)
      rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
      rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (502 : Fin 791) (by
      change 1 + values13 (53 : Fin 264) = 1 + values12 (32 : Fin 154)
      rw [show values13 (53 : Fin 264) = Real.sqrt (values12 (53 : Fin 154)) by rfl]
      rw [show values12 (53 : Fin 154) = Real.sqrt (values11 (53 : Fin 91)) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      rw [show values12 (32 : Fin 154) = Real.sqrt (values11 (32 : Fin 91)) by rfl]
      rw [show values11 (32 : Fin 91) = Real.sqrt (values10 (32 : Fin 54)) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (503 : Fin 791) (by
      change 1 + values13 (54 : Fin 264) = 1 + values12 (33 : Fin 154)
      rw [show values13 (54 : Fin 264) = Real.sqrt (values12 (54 : Fin 154)) by rfl]
      rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      rw [show values12 (33 : Fin 154) = Real.sqrt (values11 (33 : Fin 91)) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (507 : Fin 791) (by
      change 1 + values13 (56 : Fin 264) = 1 + values12 (34 : Fin 154)
      rw [show values13 (56 : Fin 264) = Real.sqrt (values12 (56 : Fin 154)) by rfl]
      rw [show values12 (56 : Fin 154) = Real.sqrt (values11 (56 : Fin 91)) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values12 (34 : Fin 154) = Real.sqrt (values11 (34 : Fin 91)) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (510 : Fin 791) (by
      change 1 + values13 (59 : Fin 264) = 1 + values12 (35 : Fin 154)
      rw [show values13 (59 : Fin 264) = Real.sqrt (values12 (59 : Fin 154)) by rfl]
      rw [show values12 (59 : Fin 154) = Real.sqrt (values11 (59 : Fin 91)) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      rw [show values12 (35 : Fin 154) = Real.sqrt (values11 (35 : Fin 91)) by rfl]
      rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (512 : Fin 791) (by
      change 1 + values13 (60 : Fin 264) = 1 + values12 (36 : Fin 154)
      rw [show values13 (60 : Fin 264) = Real.sqrt (values12 (60 : Fin 154)) by rfl]
      rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (514 : Fin 791) (by
      change 1 + values13 (62 : Fin 264) = 1 + values12 (37 : Fin 154)
      rw [show values13 (62 : Fin 264) = Real.sqrt (values12 (62 : Fin 154)) by rfl]
      rw [show values12 (62 : Fin 154) = Real.sqrt (values11 (62 : Fin 91)) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      rw [show values12 (37 : Fin 154) = Real.sqrt (values11 (37 : Fin 91)) by rfl]
      rw [show values11 (37 : Fin 91) = Real.sqrt (values10 (37 : Fin 54)) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (515 : Fin 791) (by
      change 1 + values13 (63 : Fin 264) = 1 + values12 (38 : Fin 154)
      rw [show values13 (63 : Fin 264) = Real.sqrt (values12 (63 : Fin 154)) by rfl]
      rw [show values12 (63 : Fin 154) = Real.sqrt (values11 (63 : Fin 91)) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      rw [show values12 (38 : Fin 154) = Real.sqrt (values11 (38 : Fin 91)) by rfl]
      rw [show values11 (38 : Fin 91) = Real.sqrt (values10 (38 : Fin 54)) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (517 : Fin 791) (by
      change 1 + values13 (64 : Fin 264) = 1 + values12 (39 : Fin 154)
      rw [show values13 (64 : Fin 264) = Real.sqrt (values12 (64 : Fin 154)) by rfl]
      rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      rw [show values12 (39 : Fin 154) = Real.sqrt (values11 (39 : Fin 91)) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (521 : Fin 791) (by
      change 1 + values13 (66 : Fin 264) = 1 + values12 (40 : Fin 154)
      rw [show values13 (66 : Fin 264) = Real.sqrt (values12 (66 : Fin 154)) by rfl]
      rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (523 : Fin 791) (by
      change 1 + values13 (68 : Fin 264) = 1 + values12 (41 : Fin 154)
      rw [show values13 (68 : Fin 264) = Real.sqrt (values12 (68 : Fin 154)) by rfl]
      rw [show values12 (68 : Fin 154) = Real.sqrt (values11 (68 : Fin 91)) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      rw [show values12 (41 : Fin 154) = Real.sqrt (values11 (41 : Fin 91)) by rfl]
      rw [show values11 (41 : Fin 91) = Real.sqrt (values10 (41 : Fin 54)) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (527 : Fin 791) (by
      change 1 + values13 (70 : Fin 264) = 1 + values12 (42 : Fin 154)
      rw [show values13 (70 : Fin 264) = Real.sqrt (values12 (70 : Fin 154)) by rfl]
      rw [show values12 (70 : Fin 154) = Real.sqrt (values11 (70 : Fin 91)) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      rw [show values12 (42 : Fin 154) = Real.sqrt (values11 (42 : Fin 91)) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (528 : Fin 791) (by
      change 1 + values13 (71 : Fin 264) = 1 + values12 (43 : Fin 154)
      rw [show values13 (71 : Fin 264) = Real.sqrt (values12 (71 : Fin 154)) by rfl]
      rw [show values12 (71 : Fin 154) = Real.sqrt (values11 (71 : Fin 91)) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      rw [show values12 (43 : Fin 154) = Real.sqrt (values11 (43 : Fin 91)) by rfl]
      rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (532 : Fin 791) (by
      change 1 + values13 (73 : Fin 264) = 1 + values12 (44 : Fin 154)
      rw [show values13 (73 : Fin 264) = Real.sqrt (values12 (73 : Fin 154)) by rfl]
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values12 (44 : Fin 154) = Real.sqrt (values11 (44 : Fin 91)) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (533 : Fin 791) (by
      change 1 + values13 (74 : Fin 264) = 1 + values12 (45 : Fin 154)
      rw [show values13 (74 : Fin 264) = Real.sqrt (values12 (74 : Fin 154)) by rfl]
      rw [show values12 (74 : Fin 154) = Real.sqrt (values11 (74 : Fin 91)) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values12 (45 : Fin 154) = Real.sqrt (values11 (45 : Fin 91)) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (536 : Fin 791) (by
      change 1 + values13 (76 : Fin 264) = 1 + values12 (46 : Fin 154)
      rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (538 : Fin 791) (by
      change 1 + values13 (78 : Fin 264) = 1 + values12 (47 : Fin 154)
      rw [show values13 (78 : Fin 264) = Real.sqrt (values12 (78 : Fin 154)) by rfl]
      rw [show values12 (78 : Fin 154) = Real.sqrt (values11 (78 : Fin 91)) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      rw [show values12 (47 : Fin 154) = Real.sqrt (values11 (47 : Fin 91)) by rfl]
      rw [show values11 (47 : Fin 91) = Real.sqrt (values10 (47 : Fin 54)) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (541 : Fin 791) (by
      change 1 + values13 (80 : Fin 264) = 1 + values12 (48 : Fin 154)
      rw [show values13 (80 : Fin 264) = Real.sqrt (values12 (80 : Fin 154)) by rfl]
      rw [show values12 (80 : Fin 154) = Real.sqrt (values11 (80 : Fin 91)) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      rw [show values12 (48 : Fin 154) = Real.sqrt (values11 (48 : Fin 91)) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (545 : Fin 791) (by
      change 1 + values13 (82 : Fin 264) = 1 + values12 (49 : Fin 154)
      rw [show values13 (82 : Fin 264) = Real.sqrt (values12 (82 : Fin 154)) by rfl]
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (549 : Fin 791) (by
      change 1 + values13 (84 : Fin 264) = 1 + values12 (50 : Fin 154)
      rw [show values13 (84 : Fin 264) = Real.sqrt (values12 (84 : Fin 154)) by rfl]
      rw [show values12 (84 : Fin 154) = Real.sqrt (values11 (84 : Fin 91)) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      rw [show values12 (50 : Fin 154) = Real.sqrt (values11 (50 : Fin 91)) by rfl]
      rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (554 : Fin 791) (by
      change 1 + values13 (86 : Fin 264) = 1 + values12 (51 : Fin 154)
      rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (556 : Fin 791) (by
      change 1 + values13 (88 : Fin 264) = 1 + values12 (52 : Fin 154)
      rw [show values13 (88 : Fin 264) = Real.sqrt (values12 (88 : Fin 154)) by rfl]
      rw [show values12 (88 : Fin 154) = 1 + values10 (2 : Fin 54) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      rw [show values12 (52 : Fin 154) = Real.sqrt (values11 (52 : Fin 91)) by rfl]
      rw [show values11 (52 : Fin 91) = 1 + values9 (1 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (558 : Fin 791) (by
      change 1 + values13 (89 : Fin 264) = 1 + values12 (53 : Fin 154)
      rw [show values13 (89 : Fin 264) = Real.sqrt (values12 (89 : Fin 154)) by rfl]
      rw [show values12 (89 : Fin 154) = 1 + values10 (3 : Fin 54) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values12 (53 : Fin 154) = Real.sqrt (values11 (53 : Fin 91)) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (561 : Fin 791) (by
      change 1 + values13 (91 : Fin 264) = 1 + values12 (54 : Fin 154)
      rw [show values13 (91 : Fin 264) = Real.sqrt (values12 (91 : Fin 154)) by rfl]
      rw [show values12 (91 : Fin 154) = 1 + values10 (5 : Fin 54) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (566 : Fin 791) (by
      change 1 + values13 (94 : Fin 264) = 1 + values12 (55 : Fin 154)
      rw [show values13 (94 : Fin 264) = Real.sqrt (values12 (94 : Fin 154)) by rfl]
      rw [show values12 (94 : Fin 154) = 1 + values10 (7 : Fin 54) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      rw [show values12 (55 : Fin 154) = Real.sqrt (values11 (55 : Fin 91)) by rfl]
      rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (567 : Fin 791) (by
      change 1 + values13 (95 : Fin 264) = 1 + values12 (56 : Fin 154)
      rw [show values13 (95 : Fin 264) = Real.sqrt (values12 (95 : Fin 154)) by rfl]
      rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values12 (56 : Fin 154) = Real.sqrt (values11 (56 : Fin 91)) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (569 : Fin 791) (by
      change 1 + values13 (96 : Fin 264) = 1 + values12 (57 : Fin 154)
      rw [show values13 (96 : Fin 264) = Real.sqrt (values12 (96 : Fin 154)) by rfl]
      rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      rw [show values12 (57 : Fin 154) = Real.sqrt (values11 (57 : Fin 91)) by rfl]
      rw [show values11 (57 : Fin 91) = Real.sqrt (values10 (52 : Fin 54)) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (572 : Fin 791) (by
      change 1 + values13 (98 : Fin 264) = 1 + values12 (58 : Fin 154)
      rw [show values13 (98 : Fin 264) = Real.sqrt (values12 (98 : Fin 154)) by rfl]
      rw [show values12 (98 : Fin 154) = 1 + values10 (10 : Fin 54) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      rw [show values12 (58 : Fin 154) = Real.sqrt (values11 (58 : Fin 91)) by rfl]
      rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (574 : Fin 791) (by
      change 1 + values13 (99 : Fin 264) = 1 + values12 (59 : Fin 154)
      rw [show values13 (99 : Fin 264) = Real.sqrt (values12 (99 : Fin 154)) by rfl]
      rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values12 (59 : Fin 154) = Real.sqrt (values11 (59 : Fin 91)) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (576 : Fin 791) (by
      change 1 + values13 (100 : Fin 264) = 1 + values12 (60 : Fin 154)
      rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
      rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (579 : Fin 791) (by
      change 1 + values13 (102 : Fin 264) = 1 + values12 (61 : Fin 154)
      rw [show values13 (102 : Fin 264) = Real.sqrt (values12 (102 : Fin 154)) by rfl]
      rw [show values12 (102 : Fin 154) = 1 + values10 (14 : Fin 54) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      rw [show values12 (61 : Fin 154) = Real.sqrt (values11 (61 : Fin 91)) by rfl]
      rw [show values11 (61 : Fin 91) = 1 + values9 (9 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (580 : Fin 791) (by
      change 1 + values13 (103 : Fin 264) = 1 + values12 (62 : Fin 154)
      rw [show values13 (103 : Fin 264) = Real.sqrt (values12 (103 : Fin 154)) by rfl]
      rw [show values12 (103 : Fin 154) = Real.sqrt (values11 (89 : Fin 91)) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      rw [show values12 (62 : Fin 154) = Real.sqrt (values11 (62 : Fin 91)) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (581 : Fin 791) (by
      change 1 + values13 (104 : Fin 264) = 1 + values12 (63 : Fin 154)
      rw [show values13 (104 : Fin 264) = Real.sqrt (values12 (104 : Fin 154)) by rfl]
      rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values12 (63 : Fin 154) = Real.sqrt (values11 (63 : Fin 91)) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (587 : Fin 791) (by
      change 1 + values13 (107 : Fin 264) = 1 + values12 (64 : Fin 154)
      rw [show values13 (107 : Fin 264) = Real.sqrt (values12 (107 : Fin 154)) by rfl]
      rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (591 : Fin 791) (by
      change 1 + values13 (109 : Fin 264) = 1 + values12 (65 : Fin 154)
      rw [show values13 (109 : Fin 264) = Real.sqrt (values12 (109 : Fin 154)) by rfl]
      rw [show values12 (109 : Fin 154) = values5 (1 : Fin 5) + values6 (2 : Fin 8) by rfl]
      rw [show values12 (65 : Fin 154) = Real.sqrt (values11 (65 : Fin 91)) by rfl]
      rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (592 : Fin 791) (by
      change 1 + values13 (110 : Fin 264) = 1 + values12 (66 : Fin 154)
      rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
      rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (595 : Fin 791) (by
      change 1 + values13 (112 : Fin 264) = 1 + values12 (67 : Fin 154)
      rw [show values13 (112 : Fin 264) = Real.sqrt (values12 (112 : Fin 154)) by rfl]
      rw [show values12 (112 : Fin 154) = 1 + values10 (21 : Fin 54) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      rw [show values12 (67 : Fin 154) = Real.sqrt (values11 (67 : Fin 91)) by rfl]
      rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (599 : Fin 791) (by
      change 1 + values13 (115 : Fin 264) = 1 + values12 (68 : Fin 154)
      rw [show values13 (115 : Fin 264) = Real.sqrt (values12 (115 : Fin 154)) by rfl]
      rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values12 (68 : Fin 154) = Real.sqrt (values11 (68 : Fin 91)) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (600 : Fin 791) (by
      change 1 + values13 (116 : Fin 264) = 1 + values12 (69 : Fin 154)
      rw [show values13 (116 : Fin 264) = Real.sqrt (values12 (116 : Fin 154)) by rfl]
      rw [show values12 (116 : Fin 154) = Real.sqrt 2 + values7 (2 : Fin 13) by rfl]
      rw [show values12 (69 : Fin 154) = Real.sqrt (values11 (69 : Fin 91)) by rfl]
      rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (603 : Fin 791) (by
      change 1 + values13 (118 : Fin 264) = 1 + values12 (70 : Fin 154)
      rw [show values13 (118 : Fin 264) = Real.sqrt (values12 (118 : Fin 154)) by rfl]
      rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values12 (70 : Fin 154) = Real.sqrt (values11 (70 : Fin 91)) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (606 : Fin 791) (by
      change 1 + values13 (120 : Fin 264) = 1 + values12 (71 : Fin 154)
      rw [show values13 (120 : Fin 264) = Real.sqrt (values12 (120 : Fin 154)) by rfl]
      rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by rfl]
      rw [show values12 (71 : Fin 154) = Real.sqrt (values11 (71 : Fin 91)) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (608 : Fin 791) (by
      change 1 + values13 (121 : Fin 264) = 1 + values12 (72 : Fin 154)
      rw [show values13 (121 : Fin 264) = Real.sqrt (values12 (121 : Fin 154)) by rfl]
      rw [show values12 (121 : Fin 154) = 1 + values10 (26 : Fin 54) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      rw [show values12 (72 : Fin 154) = Real.sqrt (values11 (72 : Fin 91)) by rfl]
      rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (616 : Fin 791) (by
      change 1 + values13 (124 : Fin 264) = 1 + values12 (73 : Fin 154)
      rw [show values13 (124 : Fin 264) = Real.sqrt (values12 (124 : Fin 154)) by rfl]
      rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (620 : Fin 791) (by
      change 1 + values13 (126 : Fin 264) = 1 + values12 (74 : Fin 154)
      rw [show values13 (126 : Fin 264) = Real.sqrt (values12 (126 : Fin 154)) by rfl]
      rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by rfl]
      rw [show values12 (74 : Fin 154) = Real.sqrt (values11 (74 : Fin 91)) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (621 : Fin 791) (by
      change 1 + values13 (127 : Fin 264) = 1 + values12 (75 : Fin 154)
      rw [show values13 (127 : Fin 264) = Real.sqrt (values12 (127 : Fin 154)) by rfl]
      rw [show values12 (127 : Fin 154) = 1 + values10 (30 : Fin 54) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      rw [show values12 (75 : Fin 154) = Real.sqrt (values11 (75 : Fin 91)) by rfl]
      rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (626 : Fin 791) (by
      change 1 + values13 (130 : Fin 264) = 1 + values12 (76 : Fin 154)
      rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (629 : Fin 791) (by
      change 1 + values13 (132 : Fin 264) = 1 + values12 (77 : Fin 154)
      rw [show values13 (132 : Fin 264) = Real.sqrt (values12 (132 : Fin 154)) by rfl]
      rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      rw [show values12 (77 : Fin 154) = Real.sqrt (values11 (77 : Fin 91)) by rfl]
      rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (631 : Fin 791) (by
      change 1 + values13 (133 : Fin 264) = 1 + values12 (78 : Fin 154)
      rw [show values13 (133 : Fin 264) = Real.sqrt (values12 (133 : Fin 154)) by rfl]
      rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values12 (78 : Fin 154) = Real.sqrt (values11 (78 : Fin 91)) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (633 : Fin 791) (by
      change 1 + values13 (134 : Fin 264) = 1 + values12 (79 : Fin 154)
      rw [show values13 (134 : Fin 264) = Real.sqrt (values12 (134 : Fin 154)) by rfl]
      rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by rfl]
      rw [show values12 (79 : Fin 154) = Real.sqrt (values11 (79 : Fin 91)) by rfl]
      rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (636 : Fin 791) (by
      change 1 + values13 (136 : Fin 264) = 1 + values12 (80 : Fin 154)
      rw [show values13 (136 : Fin 264) = Real.sqrt (values12 (136 : Fin 154)) by rfl]
      rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values12 (80 : Fin 154) = Real.sqrt (values11 (80 : Fin 91)) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (639 : Fin 791) (by
      change 1 + values13 (139 : Fin 264) = 1 + values12 (81 : Fin 154)
      rw [show values13 (139 : Fin 264) = Real.sqrt (values12 (139 : Fin 154)) by rfl]
      rw [show values12 (139 : Fin 154) = 1 + values10 (39 : Fin 54) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      rw [show values12 (81 : Fin 154) = Real.sqrt (values11 (81 : Fin 91)) by rfl]
      rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (644 : Fin 791) (by
      change 1 + values13 (140 : Fin 264) = 1 + values12 (82 : Fin 154)
      rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
      rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (649 : Fin 791) (by
      change 1 + values13 (142 : Fin 264) = 1 + values12 (83 : Fin 154)
      rw [show values13 (142 : Fin 264) = Real.sqrt (values12 (142 : Fin 154)) by rfl]
      rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      rw [show values12 (83 : Fin 154) = Real.sqrt (values11 (83 : Fin 91)) by rfl]
      rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (653 : Fin 791) (by
      change 1 + values13 (144 : Fin 264) = 1 + values12 (84 : Fin 154)
      rw [show values13 (144 : Fin 264) = Real.sqrt (values12 (144 : Fin 154)) by rfl]
      rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values12 (84 : Fin 154) = Real.sqrt (values11 (84 : Fin 91)) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (655 : Fin 791) (by
      change 1 + values13 (145 : Fin 264) = 1 + values12 (85 : Fin 154)
      rw [show values13 (145 : Fin 264) = Real.sqrt (values12 (145 : Fin 154)) by rfl]
      rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      rw [show values12 (85 : Fin 154) = Real.sqrt (values11 (85 : Fin 91)) by rfl]
      rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (658 : Fin 791) (by
      change 1 + values13 (146 : Fin 264) = 1 + values12 (86 : Fin 154)
      rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (660 : Fin 791) (by
      change 1 + values13 (148 : Fin 264) = 1 + values12 (87 : Fin 154)
      rw [show values13 (148 : Fin 264) = 1 + values11 (2 : Fin 91) by rfl]
      rw [show values11 (2 : Fin 91) = Real.sqrt (values10 (2 : Fin 54)) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      rw [show values12 (87 : Fin 154) = 1 + values10 (1 : Fin 54) by rfl]
      rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (661 : Fin 791) (by
      change 1 + values13 (149 : Fin 264) = 1 + values12 (88 : Fin 154)
      rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
      rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      rw [show values12 (88 : Fin 154) = 1 + values10 (2 : Fin 54) by rfl]
      rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (664 : Fin 791) (by
      change 1 + values13 (151 : Fin 264) = 1 + values12 (89 : Fin 154)
      rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
      rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      rw [show values12 (89 : Fin 154) = 1 + values10 (3 : Fin 54) by rfl]
      rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (667 : Fin 791) (by
      change 1 + values13 (154 : Fin 264) = 1 + values12 (90 : Fin 154)
      rw [show values13 (154 : Fin 264) = 1 + values11 (7 : Fin 91) by rfl]
      rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      rw [show values12 (90 : Fin 154) = 1 + values10 (4 : Fin 54) by rfl]
      rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (669 : Fin 791) (by
      change 1 + values13 (155 : Fin 264) = 1 + values12 (91 : Fin 154)
      rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
      rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      rw [show values12 (91 : Fin 154) = 1 + values10 (5 : Fin 54) by rfl]
      rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (670 : Fin 791) (by
      change 1 + values13 (156 : Fin 264) = 1 + values12 (92 : Fin 154)
      rw [show values13 (156 : Fin 264) = Real.sqrt (values12 (148 : Fin 154)) by rfl]
      rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      rw [show values12 (92 : Fin 154) = Real.sqrt (values11 (87 : Fin 91)) by rfl]
      rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (673 : Fin 791) (by
      change 1 + values13 (158 : Fin 264) = 1 + values12 (93 : Fin 154)
      rw [show values13 (158 : Fin 264) = 1 + values11 (10 : Fin 91) by rfl]
      rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      rw [show values12 (93 : Fin 154) = 1 + values10 (6 : Fin 54) by rfl]
      rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (675 : Fin 791) (by
      change 1 + values13 (159 : Fin 264) = 1 + values12 (94 : Fin 154)
      rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
      rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      rw [show values12 (94 : Fin 154) = 1 + values10 (7 : Fin 54) by rfl]
      rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (676 : Fin 791) (by
      change 1 + values13 (160 : Fin 264) = 1 + values12 (95 : Fin 154)
      rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
      rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
      rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (679 : Fin 791) (by
      change 1 + values13 (162 : Fin 264) = 1 + values12 (96 : Fin 154)
      rw [show values13 (162 : Fin 264) = Real.sqrt (values12 (149 : Fin 154)) by rfl]
      rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (680 : Fin 791) (by
      change 1 + values13 (163 : Fin 264) = 1 + values12 (97 : Fin 154)
      rw [show values13 (163 : Fin 264) = 1 + values11 (14 : Fin 91) by rfl]
      rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      rw [show values12 (97 : Fin 154) = 1 + values10 (9 : Fin 54) by rfl]
      rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (682 : Fin 791) (by
      change 1 + values13 (164 : Fin 264) = 1 + values12 (98 : Fin 154)
      rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
      rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      rw [show values12 (98 : Fin 154) = 1 + values10 (10 : Fin 54) by rfl]
      rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (685 : Fin 791) (by
      change 1 + values13 (166 : Fin 264) = 1 + values12 (99 : Fin 154)
      rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
      rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by rfl]
      rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (689 : Fin 791) (by
      change 1 + values13 (170 : Fin 264) = 1 + values12 (100 : Fin 154)
      rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
      rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
      rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (692 : Fin 791) (by
      change 1 + values13 (172 : Fin 264) = 1 + values12 (101 : Fin 154)
      rw [show values13 (172 : Fin 264) = 1 + values11 (21 : Fin 91) by rfl]
      rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      rw [show values12 (101 : Fin 154) = 1 + values10 (13 : Fin 54) by rfl]
      rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (694 : Fin 791) (by
      change 1 + values13 (173 : Fin 264) = 1 + values12 (102 : Fin 154)
      rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
      rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      rw [show values12 (102 : Fin 154) = 1 + values10 (14 : Fin 54) by rfl]
      rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (697 : Fin 791) (by
      change 1 + values13 (176 : Fin 264) = 1 + values12 (103 : Fin 154)
      rw [show values13 (176 : Fin 264) = Real.sqrt (values12 (151 : Fin 154)) by rfl]
      rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values12 (103 : Fin 154) = Real.sqrt (values11 (89 : Fin 91)) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (698 : Fin 791) (by
      change 1 + values13 (177 : Fin 264) = 1 + values12 (104 : Fin 154)
      rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
      rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by rfl]
      rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (701 : Fin 791) (by
      change 1 + values13 (179 : Fin 264) = 1 + values12 (105 : Fin 154)
      rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
      rw [show values12 (105 : Fin 154) = values5 (1 : Fin 5) + values6 (1 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (702 : Fin 791) (by
      change 1 + values13 (180 : Fin 264) = 1 + values12 (106 : Fin 154)
      rw [show values13 (180 : Fin 264) = 1 + values11 (26 : Fin 91) by rfl]
      rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      rw [show values12 (106 : Fin 154) = 1 + values10 (16 : Fin 54) by rfl]
      rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (705 : Fin 791) (by
      change 1 + values13 (182 : Fin 264) = 1 + values12 (107 : Fin 154)
      rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
      rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
      rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (708 : Fin 791) (by
      change 1 + values13 (185 : Fin 264) = 1 + values12 (108 : Fin 154)
      rw [show values13 (185 : Fin 264) = 1 + values11 (30 : Fin 91) by rfl]
      rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      rw [show values12 (108 : Fin 154) = 1 + values10 (18 : Fin 54) by rfl]
      rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (709 : Fin 791) (by
      change 1 + values13 (186 : Fin 264) = 1 + values12 (109 : Fin 154)
      rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
      rw [show values12 (109 : Fin 154) = values5 (1 : Fin 5) + values6 (2 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (710 : Fin 791) (by
      change 1 + values13 (187 : Fin 264) = 1 + values12 (110 : Fin 154)
      rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
      rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
      rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (712 : Fin 791) (by
      change 1 + values13 (189 : Fin 264) = 1 + values12 (111 : Fin 154)
      rw [show values13 (189 : Fin 264) = 1 + values11 (33 : Fin 91) by rfl]
      rw [show values11 (33 : Fin 91) = Real.sqrt (values10 (33 : Fin 54)) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      rw [show values12 (111 : Fin 154) = 1 + values10 (20 : Fin 54) by rfl]
      rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (714 : Fin 791) (by
      change 1 + values13 (191 : Fin 264) = 1 + values12 (112 : Fin 154)
      rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
      rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      rw [show values12 (112 : Fin 154) = 1 + values10 (21 : Fin 54) by rfl]
      rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (715 : Fin 791) (by
      change 1 + values13 (192 : Fin 264) = 1 + values12 (113 : Fin 154)
      rw [show values13 (192 : Fin 264) = Real.sqrt (values12 (153 : Fin 154)) by rfl]
      rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      rw [show values12 (113 : Fin 154) = Real.sqrt (values11 (90 : Fin 91)) by rfl]
      rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (716 : Fin 791) (by
      change 1 + values13 (193 : Fin 264) = 1 + values12 (114 : Fin 154)
      rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
      rw [show values12 (114 : Fin 154) = Real.sqrt 2 + values7 (1 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (719 : Fin 791) (by
      change 1 + values13 (195 : Fin 264) = 1 + values12 (115 : Fin 154)
      rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
      rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by rfl]
      rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (722 : Fin 791) (by
      change 1 + values13 (198 : Fin 264) = 1 + values12 (116 : Fin 154)
      rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
      rw [show values12 (116 : Fin 154) = Real.sqrt 2 + values7 (2 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (724 : Fin 791) (by
      change 1 + values13 (200 : Fin 264) = 1 + values12 (117 : Fin 154)
      rw [show values13 (200 : Fin 264) = 1 + values11 (39 : Fin 91) by rfl]
      rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      rw [show values12 (117 : Fin 154) = 1 + values10 (23 : Fin 54) by rfl]
      rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (725 : Fin 791) (by
      change 1 + values13 (201 : Fin 264) = 1 + values12 (118 : Fin 154)
      rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
      rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
      rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (728 : Fin 791) (by
      change 1 + values13 (204 : Fin 264) = 1 + values12 (119 : Fin 154)
      rw [show values13 (204 : Fin 264) = 1 + values11 (42 : Fin 91) by rfl]
      rw [show values11 (42 : Fin 91) = Real.sqrt (values10 (42 : Fin 54)) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      rw [show values12 (119 : Fin 154) = 1 + values10 (25 : Fin 54) by rfl]
      rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (729 : Fin 791) (by
      change 1 + values13 (205 : Fin 264) = 1 + values12 (120 : Fin 154)
      rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
      rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (732 : Fin 791) (by
      change 1 + values13 (207 : Fin 264) = 1 + values12 (121 : Fin 154)
      rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
      rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      rw [show values12 (121 : Fin 154) = 1 + values10 (26 : Fin 54) by rfl]
      rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (734 : Fin 791) (by
      change 1 + values13 (209 : Fin 264) = 1 + values12 (122 : Fin 154)
      rw [show values13 (209 : Fin 264) = 1 + values11 (45 : Fin 91) by rfl]
      rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      rw [show values12 (122 : Fin 154) = 1 + values10 (27 : Fin 54) by rfl]
      rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (735 : Fin 791) (by
      change 1 + values13 (210 : Fin 264) = 1 + values12 (123 : Fin 154)
      rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
      rw [show values12 (123 : Fin 154) = Real.sqrt 2 + values7 (4 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (736 : Fin 791) (by
      change 1 + values13 (211 : Fin 264) = 1 + values12 (124 : Fin 154)
      rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
      rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
      rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (739 : Fin 791) (by
      change 1 + values13 (214 : Fin 264) = 1 + values12 (125 : Fin 154)
      rw [show values13 (214 : Fin 264) = 1 + values11 (48 : Fin 91) by rfl]
      rw [show values11 (48 : Fin 91) = Real.sqrt (values10 (48 : Fin 54)) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      rw [show values12 (125 : Fin 154) = 1 + values10 (29 : Fin 54) by rfl]
      rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (741 : Fin 791) (by
      change 1 + values13 (216 : Fin 264) = 1 + values12 (126 : Fin 154)
      rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
      rw [show values12 (126 : Fin 154) = Real.sqrt 2 + values7 (5 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (742 : Fin 791) (by
      change 1 + values13 (217 : Fin 264) = 1 + values12 (127 : Fin 154)
      rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
      rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      rw [show values12 (127 : Fin 154) = 1 + values10 (30 : Fin 54) by rfl]
      rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (744 : Fin 791) (by
      change 1 + values13 (219 : Fin 264) = 1 + values12 (128 : Fin 154)
      rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
      rw [show values12 (128 : Fin 154) = values5 (1 : Fin 5) + values6 (4 : Fin 8) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (746 : Fin 791) (by
      change 1 + values13 (221 : Fin 264) = 1 + values12 (129 : Fin 154)
      rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
      rw [show values12 (129 : Fin 154) = Real.sqrt 2 + values7 (6 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (747 : Fin 791) (by
      change 1 + values13 (222 : Fin 264) = 1 + values12 (130 : Fin 154)
      rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
      rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
      rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (750 : Fin 791) (by
      change 1 + values13 (224 : Fin 264) = 1 + values12 (131 : Fin 154)
      rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
      rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
      rw [show values12 (131 : Fin 154) = 1 + values10 (32 : Fin 54) by rfl]
      rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (751 : Fin 791) (by
      change 1 + values13 (225 : Fin 264) = 1 + values12 (132 : Fin 154)
      rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
      rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
      rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
      rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (753 : Fin 791) (by
      change 1 + values13 (227 : Fin 264) = 1 + values12 (133 : Fin 154)
      rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
      rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
      rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
      rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (756 : Fin 791) (by
      change 1 + values13 (230 : Fin 264) = 1 + values12 (134 : Fin 154)
      rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
      rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (757 : Fin 791) (by
      change 1 + values13 (231 : Fin 264) = 1 + values12 (135 : Fin 154)
      rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
      rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
      rw [show values12 (135 : Fin 154) = 1 + values10 (35 : Fin 54) by rfl]
      rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (758 : Fin 791) (by
      change 1 + values13 (232 : Fin 264) = 1 + values12 (136 : Fin 154)
      rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
      rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
      rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
      rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (760 : Fin 791) (by
      change 1 + values13 (234 : Fin 264) = 1 + values12 (137 : Fin 154)
      rw [show values13 (234 : Fin 264) = 1 + values11 (62 : Fin 91) by rfl]
      rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      rw [show values12 (137 : Fin 154) = 1 + values10 (37 : Fin 54) by rfl]
      rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (762 : Fin 791) (by
      change 1 + values13 (235 : Fin 264) = 1 + values12 (138 : Fin 154)
      rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
      rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
      rw [show values12 (138 : Fin 154) = 1 + values10 (38 : Fin 54) by rfl]
      rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (763 : Fin 791) (by
      change 1 + values13 (236 : Fin 264) = 1 + values12 (139 : Fin 154)
      rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
      rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
      rw [show values12 (139 : Fin 154) = 1 + values10 (39 : Fin 54) by rfl]
      rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (765 : Fin 791) (by
      change 1 + values13 (238 : Fin 264) = 1 + values12 (140 : Fin 154)
      rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
      rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
      rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
      rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (768 : Fin 791) (by
      change 1 + values13 (241 : Fin 264) = 1 + values12 (141 : Fin 154)
      rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
      rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
      rw [show values12 (141 : Fin 154) = 1 + values10 (41 : Fin 54) by rfl]
      rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (770 : Fin 791) (by
      change 1 + values13 (243 : Fin 264) = 1 + values12 (142 : Fin 154)
      rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
      rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
      rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
      rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (771 : Fin 791) (by
      change 1 + values13 (244 : Fin 264) = 1 + values12 (143 : Fin 154)
      rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
      rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
      rw [show values12 (143 : Fin 154) = 1 + values10 (43 : Fin 54) by rfl]
      rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (773 : Fin 791) (by
      change 1 + values13 (246 : Fin 264) = 1 + values12 (144 : Fin 154)
      rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
      rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
      rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
      rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (774 : Fin 791) (by
      change 1 + values13 (247 : Fin 264) = 1 + values12 (145 : Fin 154)
      rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
      rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
      rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
      rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (776 : Fin 791) (by
      change 1 + values13 (249 : Fin 264) = 1 + values12 (146 : Fin 154)
      rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
      rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
      rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
      rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (778 : Fin 791) (by
      change 1 + values13 (251 : Fin 264) = 1 + values12 (147 : Fin 154)
      rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
      rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
      rw [show values12 (147 : Fin 154) = 1 + values10 (47 : Fin 54) by rfl]
      rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (780 : Fin 791) (by
      change 1 + values13 (253 : Fin 264) = 1 + values12 (148 : Fin 154)
      rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
      rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
      rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by rfl]
      rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (782 : Fin 791) (by
      change 1 + values13 (255 : Fin 264) = 1 + values12 (149 : Fin 154)
      rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
      rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
      rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by rfl]
      rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (784 : Fin 791) (by
      change 1 + values13 (257 : Fin 264) = 1 + values12 (150 : Fin 154)
      rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
      rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
      rw [show values12 (150 : Fin 154) = 1 + values10 (50 : Fin 54) by rfl]
      rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (786 : Fin 791) (by
      change 1 + values13 (259 : Fin 264) = 1 + values12 (151 : Fin 154)
      rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
      rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
      rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
      rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (788 : Fin 791) (by
      change 1 + values13 (261 : Fin 264) = 1 + values12 (152 : Fin 154)
      rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
      rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
      rw [show values12 (152 : Fin 154) = 1 + values10 (52 : Fin 54) by rfl]
      rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )
  next =>
    exact Exists.intro (789 : Fin 791) (by
      change 1 + values13 (262 : Fin 264) = 1 + values12 (153 : Fin 154)
      rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
      rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
      rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by rfl]
      rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
      a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
    )



end Expr
end A158415
end LeanProofs
