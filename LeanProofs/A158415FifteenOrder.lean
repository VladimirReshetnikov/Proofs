import LeanProofs.A158415FifteenIntervals

/-!
# Size-fifteen order certificate for OEIS A158415

This module proves that the size-15 representative table is strictly sorted,
which gives the cardinality of its range.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
theorem values14_nonneg (i : Fin 455) : (0 : Real) ≤ values14 i := by
  have h0 : (0 : Real) ≤ values14 (0 : Fin 455) := by
    change (0 : Real) ≤ Real.sqrt (values13 (0 : Fin 264))
    exact Real.sqrt_nonneg _
  exact h0.trans (values14_strictMono.monotone (Fin.zero_le i))

theorem sqrt_values14_strictMono :
    StrictMono fun i : Fin 455 => Real.sqrt (values14 i) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (values14_nonneg i) (values14_strictMono hij)

set_option maxHeartbeats 2000000 in
theorem values15_strictMono : StrictMono values15 := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact sqrt_values14_strictMono (by decide)
  next => exact values15_special_430
  next =>
    change 1 + values13 (1 : Fin 264) < 1 + values13 (2 : Fin 264)
    linarith [values13_strictMono (by native_decide : (1 : Fin 264) < 2)]
  next =>
    change 1 + values13 (2 : Fin 264) < 1 + values13 (3 : Fin 264)
    linarith [values13_strictMono (by native_decide : (2 : Fin 264) < 3)]
  next =>
    change 1 + values13 (3 : Fin 264) < 1 + values13 (4 : Fin 264)
    linarith [values13_strictMono (by native_decide : (3 : Fin 264) < 4)]
  next =>
    change 1 + values13 (4 : Fin 264) < 1 + values13 (5 : Fin 264)
    linarith [values13_strictMono (by native_decide : (4 : Fin 264) < 5)]
  next => exact values15_special_435
  next => exact values15_special_436
  next =>
    change 1 + values13 (6 : Fin 264) < 1 + values13 (7 : Fin 264)
    linarith [values13_strictMono (by native_decide : (6 : Fin 264) < 7)]
  next =>
    change 1 + values13 (7 : Fin 264) < 1 + values13 (8 : Fin 264)
    linarith [values13_strictMono (by native_decide : (7 : Fin 264) < 8)]
  next => exact values15_special_439
  next => exact values15_special_440
  next =>
    change 1 + values13 (9 : Fin 264) < 1 + values13 (10 : Fin 264)
    linarith [values13_strictMono (by native_decide : (9 : Fin 264) < 10)]
  next =>
    change 1 + values13 (10 : Fin 264) < 1 + values13 (11 : Fin 264)
    linarith [values13_strictMono (by native_decide : (10 : Fin 264) < 11)]
  next =>
    change 1 + values13 (11 : Fin 264) < 1 + values13 (12 : Fin 264)
    linarith [values13_strictMono (by native_decide : (11 : Fin 264) < 12)]
  next => exact values15_special_444
  next => exact values15_special_445
  next =>
    change 1 + values13 (13 : Fin 264) < 1 + values13 (14 : Fin 264)
    linarith [values13_strictMono (by native_decide : (13 : Fin 264) < 14)]
  next =>
    change 1 + values13 (14 : Fin 264) < 1 + values13 (15 : Fin 264)
    linarith [values13_strictMono (by native_decide : (14 : Fin 264) < 15)]
  next =>
    change 1 + values13 (15 : Fin 264) < 1 + values13 (16 : Fin 264)
    linarith [values13_strictMono (by native_decide : (15 : Fin 264) < 16)]
  next =>
    change 1 + values13 (16 : Fin 264) < 1 + values13 (17 : Fin 264)
    linarith [values13_strictMono (by native_decide : (16 : Fin 264) < 17)]
  next => exact values15_special_450
  next => exact sqrt_values14_strictMono (by decide)
  next => exact values15_special_452
  next =>
    change 1 + values13 (18 : Fin 264) < 1 + values13 (19 : Fin 264)
    linarith [values13_strictMono (by native_decide : (18 : Fin 264) < 19)]
  next =>
    change 1 + values13 (19 : Fin 264) < 1 + values13 (20 : Fin 264)
    linarith [values13_strictMono (by native_decide : (19 : Fin 264) < 20)]
  next => exact values15_special_455
  next => exact values15_special_456
  next =>
    change 1 + values13 (21 : Fin 264) < 1 + values13 (22 : Fin 264)
    linarith [values13_strictMono (by native_decide : (21 : Fin 264) < 22)]
  next =>
    change 1 + values13 (22 : Fin 264) < 1 + values13 (23 : Fin 264)
    linarith [values13_strictMono (by native_decide : (22 : Fin 264) < 23)]
  next =>
    change 1 + values13 (23 : Fin 264) < 1 + values13 (24 : Fin 264)
    linarith [values13_strictMono (by native_decide : (23 : Fin 264) < 24)]
  next => exact values15_special_460
  next => exact sqrt_values14_strictMono (by decide)
  next => exact values15_special_462
  next => exact values15_special_463
  next => exact values15_special_464
  next =>
    change 1 + values13 (26 : Fin 264) < 1 + values13 (27 : Fin 264)
    linarith [values13_strictMono (by native_decide : (26 : Fin 264) < 27)]
  next =>
    change 1 + values13 (27 : Fin 264) < 1 + values13 (28 : Fin 264)
    linarith [values13_strictMono (by native_decide : (27 : Fin 264) < 28)]
  next =>
    change 1 + values13 (28 : Fin 264) < 1 + values13 (29 : Fin 264)
    linarith [values13_strictMono (by native_decide : (28 : Fin 264) < 29)]
  next => exact values15_special_468
  next => exact values15_special_469
  next => exact values15_special_470
  next => exact values15_special_471
  next =>
    change 1 + values13 (31 : Fin 264) < 1 + values13 (32 : Fin 264)
    linarith [values13_strictMono (by native_decide : (31 : Fin 264) < 32)]
  next =>
    change 1 + values13 (32 : Fin 264) < 1 + values13 (33 : Fin 264)
    linarith [values13_strictMono (by native_decide : (32 : Fin 264) < 33)]
  next =>
    change 1 + values13 (33 : Fin 264) < 1 + values13 (34 : Fin 264)
    linarith [values13_strictMono (by native_decide : (33 : Fin 264) < 34)]
  next =>
    change 1 + values13 (34 : Fin 264) < 1 + values13 (35 : Fin 264)
    linarith [values13_strictMono (by native_decide : (34 : Fin 264) < 35)]
  next => exact values15_special_476
  next => exact values15_special_477
  next =>
    change 1 + values13 (36 : Fin 264) < 1 + values13 (37 : Fin 264)
    linarith [values13_strictMono (by native_decide : (36 : Fin 264) < 37)]
  next =>
    change 1 + values13 (37 : Fin 264) < 1 + values13 (38 : Fin 264)
    linarith [values13_strictMono (by native_decide : (37 : Fin 264) < 38)]
  next =>
    change 1 + values13 (38 : Fin 264) < 1 + values13 (39 : Fin 264)
    linarith [values13_strictMono (by native_decide : (38 : Fin 264) < 39)]
  next => exact values15_special_481
  next => exact values15_special_482
  next => exact values15_special_483
  next => exact values15_special_484
  next =>
    change 1 + values13 (41 : Fin 264) < 1 + values13 (42 : Fin 264)
    linarith [values13_strictMono (by native_decide : (41 : Fin 264) < 42)]
  next =>
    change 1 + values13 (42 : Fin 264) < 1 + values13 (43 : Fin 264)
    linarith [values13_strictMono (by native_decide : (42 : Fin 264) < 43)]
  next =>
    change 1 + values13 (43 : Fin 264) < 1 + values13 (44 : Fin 264)
    linarith [values13_strictMono (by native_decide : (43 : Fin 264) < 44)]
  next => exact values15_special_488
  next => exact values15_special_489
  next => exact values15_special_490
  next => exact values15_special_491
  next => exact values15_special_492
  next =>
    change 1 + values13 (46 : Fin 264) < 1 + values13 (47 : Fin 264)
    linarith [values13_strictMono (by native_decide : (46 : Fin 264) < 47)]
  next =>
    change 1 + values13 (47 : Fin 264) < 1 + values13 (48 : Fin 264)
    linarith [values13_strictMono (by native_decide : (47 : Fin 264) < 48)]
  next =>
    change 1 + values13 (48 : Fin 264) < 1 + values13 (49 : Fin 264)
    linarith [values13_strictMono (by native_decide : (48 : Fin 264) < 49)]
  next => exact values15_special_496
  next => exact values15_special_497
  next => exact values15_special_498
  next => exact values15_special_499
  next =>
    change 1 + values13 (51 : Fin 264) < 1 + values13 (52 : Fin 264)
    linarith [values13_strictMono (by native_decide : (51 : Fin 264) < 52)]
  next =>
    change 1 + values13 (52 : Fin 264) < 1 + values13 (53 : Fin 264)
    linarith [values13_strictMono (by native_decide : (52 : Fin 264) < 53)]
  next =>
    change 1 + values13 (53 : Fin 264) < 1 + values13 (54 : Fin 264)
    linarith [values13_strictMono (by native_decide : (53 : Fin 264) < 54)]
  next => exact values15_special_503
  next => exact values15_special_504
  next => exact values15_special_505
  next => exact values15_special_506
  next =>
    change 1 + values13 (56 : Fin 264) < 1 + values13 (57 : Fin 264)
    linarith [values13_strictMono (by native_decide : (56 : Fin 264) < 57)]
  next =>
    change 1 + values13 (57 : Fin 264) < 1 + values13 (58 : Fin 264)
    linarith [values13_strictMono (by native_decide : (57 : Fin 264) < 58)]
  next =>
    change 1 + values13 (58 : Fin 264) < 1 + values13 (59 : Fin 264)
    linarith [values13_strictMono (by native_decide : (58 : Fin 264) < 59)]
  next => exact values15_special_510
  next => exact values15_special_511
  next =>
    change 1 + values13 (60 : Fin 264) < 1 + values13 (61 : Fin 264)
    linarith [values13_strictMono (by native_decide : (60 : Fin 264) < 61)]
  next =>
    change 1 + values13 (61 : Fin 264) < 1 + values13 (62 : Fin 264)
    linarith [values13_strictMono (by native_decide : (61 : Fin 264) < 62)]
  next =>
    change 1 + values13 (62 : Fin 264) < 1 + values13 (63 : Fin 264)
    linarith [values13_strictMono (by native_decide : (62 : Fin 264) < 63)]
  next => exact values15_special_515
  next => exact values15_special_516
  next => exact values15_special_517
  next => exact values15_special_518
  next => exact values15_special_519
  next =>
    change 1 + values13 (65 : Fin 264) < 1 + values13 (66 : Fin 264)
    linarith [values13_strictMono (by native_decide : (65 : Fin 264) < 66)]
  next =>
    change 1 + values13 (66 : Fin 264) < 1 + values13 (67 : Fin 264)
    linarith [values13_strictMono (by native_decide : (66 : Fin 264) < 67)]
  next =>
    change 1 + values13 (67 : Fin 264) < 1 + values13 (68 : Fin 264)
    linarith [values13_strictMono (by native_decide : (67 : Fin 264) < 68)]
  next => exact values15_special_523
  next => exact values15_special_524
  next => exact values15_special_525
  next => exact values15_special_526
  next =>
    change 1 + values13 (70 : Fin 264) < 1 + values13 (71 : Fin 264)
    linarith [values13_strictMono (by native_decide : (70 : Fin 264) < 71)]
  next =>
    change 1 + values13 (71 : Fin 264) < 1 + values13 (72 : Fin 264)
    linarith [values13_strictMono (by native_decide : (71 : Fin 264) < 72)]
  next => exact values15_special_529
  next => exact values15_special_530
  next => exact values15_special_531
  next =>
    change 1 + values13 (73 : Fin 264) < 1 + values13 (74 : Fin 264)
    linarith [values13_strictMono (by native_decide : (73 : Fin 264) < 74)]
  next =>
    change 1 + values13 (74 : Fin 264) < 1 + values13 (75 : Fin 264)
    linarith [values13_strictMono (by native_decide : (74 : Fin 264) < 75)]
  next => exact values15_special_534
  next => exact values15_special_535
  next =>
    change 1 + values13 (76 : Fin 264) < 1 + values13 (77 : Fin 264)
    linarith [values13_strictMono (by native_decide : (76 : Fin 264) < 77)]
  next =>
    change 1 + values13 (77 : Fin 264) < 1 + values13 (78 : Fin 264)
    linarith [values13_strictMono (by native_decide : (77 : Fin 264) < 78)]
  next => exact values15_special_538
  next => exact values15_special_539
  next =>
    change 1 + values13 (79 : Fin 264) < 1 + values13 (80 : Fin 264)
    linarith [values13_strictMono (by native_decide : (79 : Fin 264) < 80)]
  next => exact values15_special_541
  next => exact values15_special_542
  next => exact values15_special_543
  next =>
    change 1 + values13 (81 : Fin 264) < 1 + values13 (82 : Fin 264)
    linarith [values13_strictMono (by native_decide : (81 : Fin 264) < 82)]
  next => exact values15_special_545
  next => exact values15_special_546
  next => exact values15_special_547
  next => exact values15_special_548
  next => exact values15_special_549
  next => exact values15_special_550
  next => exact values15_special_551
  next => exact values15_special_552
  next => exact values15_special_553
  next =>
    change 1 + values13 (86 : Fin 264) < 1 + values13 (87 : Fin 264)
    linarith [values13_strictMono (by native_decide : (86 : Fin 264) < 87)]
  next =>
    change 1 + values13 (87 : Fin 264) < 1 + values13 (88 : Fin 264)
    linarith [values13_strictMono (by native_decide : (87 : Fin 264) < 88)]
  next => exact values15_special_556
  next => exact values15_special_557
  next => exact values15_special_558
  next => exact values15_special_559
  next =>
    change 1 + values13 (90 : Fin 264) < 1 + values13 (91 : Fin 264)
    linarith [values13_strictMono (by native_decide : (90 : Fin 264) < 91)]
  next =>
    change 1 + values13 (91 : Fin 264) < 1 + values13 (92 : Fin 264)
    linarith [values13_strictMono (by native_decide : (91 : Fin 264) < 92)]
  next =>
    change 1 + values13 (92 : Fin 264) < 1 + values13 (93 : Fin 264)
    linarith [values13_strictMono (by native_decide : (92 : Fin 264) < 93)]
  next => exact values15_special_563
  next => exact values15_special_564
  next => exact values15_special_565
  next =>
    change 1 + values13 (94 : Fin 264) < 1 + values13 (95 : Fin 264)
    linarith [values13_strictMono (by native_decide : (94 : Fin 264) < 95)]
  next => exact values15_special_567
  next => exact values15_special_568
  next => exact values15_special_569
  next => exact values15_special_570
  next =>
    change 1 + values13 (97 : Fin 264) < 1 + values13 (98 : Fin 264)
    linarith [values13_strictMono (by native_decide : (97 : Fin 264) < 98)]
  next => exact values15_special_572
  next => exact values15_special_573
  next => exact values15_special_574
  next => exact values15_special_575
  next =>
    change 1 + values13 (100 : Fin 264) < 1 + values13 (101 : Fin 264)
    linarith [values13_strictMono (by native_decide : (100 : Fin 264) < 101)]
  next => exact values15_special_577
  next => exact values15_special_578
  next =>
    change 1 + values13 (102 : Fin 264) < 1 + values13 (103 : Fin 264)
    linarith [values13_strictMono (by native_decide : (102 : Fin 264) < 103)]
  next =>
    change 1 + values13 (103 : Fin 264) < 1 + values13 (104 : Fin 264)
    linarith [values13_strictMono (by native_decide : (103 : Fin 264) < 104)]
  next => exact values15_special_581
  next => exact values15_special_582
  next => exact values15_special_583
  next =>
    change 1 + values13 (105 : Fin 264) < 1 + values13 (106 : Fin 264)
    linarith [values13_strictMono (by native_decide : (105 : Fin 264) < 106)]
  next => exact values15_special_585
  next => exact values15_special_586
  next => exact values15_special_587
  next => exact values15_special_588
  next => exact values15_special_589
  next =>
    change 1 + values13 (108 : Fin 264) < 1 + values13 (109 : Fin 264)
    linarith [values13_strictMono (by native_decide : (108 : Fin 264) < 109)]
  next =>
    change 1 + values13 (109 : Fin 264) < 1 + values13 (110 : Fin 264)
    linarith [values13_strictMono (by native_decide : (109 : Fin 264) < 110)]
  next =>
    change 1 + values13 (110 : Fin 264) < 1 + values13 (111 : Fin 264)
    linarith [values13_strictMono (by native_decide : (110 : Fin 264) < 111)]
  next => exact values15_special_593
  next => exact values15_special_594
  next =>
    change 1 + values13 (112 : Fin 264) < 1 + values13 (113 : Fin 264)
    linarith [values13_strictMono (by native_decide : (112 : Fin 264) < 113)]
  next =>
    change 1 + values13 (113 : Fin 264) < 1 + values13 (114 : Fin 264)
    linarith [values13_strictMono (by native_decide : (113 : Fin 264) < 114)]
  next => exact values15_special_597
  next => exact values15_special_598
  next =>
    change 1 + values13 (115 : Fin 264) < 1 + values13 (116 : Fin 264)
    linarith [values13_strictMono (by native_decide : (115 : Fin 264) < 116)]
  next =>
    change 1 + values13 (116 : Fin 264) < 1 + values13 (117 : Fin 264)
    linarith [values13_strictMono (by native_decide : (116 : Fin 264) < 117)]
  next => exact values15_special_601
  next => exact values15_special_602
  next => exact values15_special_603
  next => exact values15_special_604
  next =>
    change 1 + values13 (119 : Fin 264) < 1 + values13 (120 : Fin 264)
    linarith [values13_strictMono (by native_decide : (119 : Fin 264) < 120)]
  next => exact values15_special_606
  next => exact values15_special_607
  next => exact values15_special_608
  next => exact values15_special_609
  next => exact values15_special_610
  next => exact values15_special_611
  next => exact values15_special_612
  next => exact values15_special_613
  next => exact values15_special_614
  next =>
    change 1 + values13 (123 : Fin 264) < 1 + values13 (124 : Fin 264)
    linarith [values13_strictMono (by native_decide : (123 : Fin 264) < 124)]
  next => exact values15_special_616
  next => exact values15_special_617
  next => exact values15_special_618
  next =>
    change 1 + values13 (125 : Fin 264) < 1 + values13 (126 : Fin 264)
    linarith [values13_strictMono (by native_decide : (125 : Fin 264) < 126)]
  next =>
    change 1 + values13 (126 : Fin 264) < 1 + values13 (127 : Fin 264)
    linarith [values13_strictMono (by native_decide : (126 : Fin 264) < 127)]
  next => exact values15_special_621
  next => exact values15_special_622
  next =>
    change 1 + values13 (128 : Fin 264) < 1 + values13 (129 : Fin 264)
    linarith [values13_strictMono (by native_decide : (128 : Fin 264) < 129)]
  next => exact values15_special_624
  next => exact values15_special_625
  next =>
    change 1 + values13 (130 : Fin 264) < 1 + values13 (131 : Fin 264)
    linarith [values13_strictMono (by native_decide : (130 : Fin 264) < 131)]
  next => exact values15_special_627
  next => exact values15_special_628
  next => exact values15_special_629
  next => exact values15_special_630
  next => exact values15_special_631
  next => exact values15_special_632
  next =>
    change 1 + values13 (134 : Fin 264) < 1 + values13 (135 : Fin 264)
    linarith [values13_strictMono (by native_decide : (134 : Fin 264) < 135)]
  next => exact values15_special_634
  next => exact values15_special_635
  next =>
    change 1 + values13 (136 : Fin 264) < 1 + values13 (137 : Fin 264)
    linarith [values13_strictMono (by native_decide : (136 : Fin 264) < 137)]
  next =>
    change 1 + values13 (137 : Fin 264) < 1 + values13 (138 : Fin 264)
    linarith [values13_strictMono (by native_decide : (137 : Fin 264) < 138)]
  next =>
    change 1 + values13 (138 : Fin 264) < 1 + values13 (139 : Fin 264)
    linarith [values13_strictMono (by native_decide : (138 : Fin 264) < 139)]
  next => exact values15_special_639
  next => exact values15_special_640
  next => exact values15_special_641
  next => exact values15_special_642
  next => exact values15_special_643
  next => exact values15_special_644
  next => exact values15_special_645
  next => exact values15_special_646
  next => exact values15_special_647
  next => exact values15_special_648
  next => exact values15_special_649
  next => exact values15_special_650
  next => exact values15_special_651
  next => exact values15_special_652
  next => exact values15_special_653
  next => exact values15_special_654
  next => exact values15_special_655
  next => exact values15_special_656
  next => exact values15_special_657
  next =>
    change 1 + values13 (146 : Fin 264) < 1 + values13 (147 : Fin 264)
    linarith [values13_strictMono (by native_decide : (146 : Fin 264) < 147)]
  next =>
    change 1 + values13 (147 : Fin 264) < 1 + values13 (148 : Fin 264)
    linarith [values13_strictMono (by native_decide : (147 : Fin 264) < 148)]
  next =>
    change 1 + values13 (148 : Fin 264) < 1 + values13 (149 : Fin 264)
    linarith [values13_strictMono (by native_decide : (148 : Fin 264) < 149)]
  next => exact values15_special_661
  next => exact values15_special_662
  next =>
    change 1 + values13 (150 : Fin 264) < 1 + values13 (151 : Fin 264)
    linarith [values13_strictMono (by native_decide : (150 : Fin 264) < 151)]
  next =>
    change 1 + values13 (151 : Fin 264) < 1 + values13 (152 : Fin 264)
    linarith [values13_strictMono (by native_decide : (151 : Fin 264) < 152)]
  next =>
    change 1 + values13 (152 : Fin 264) < 1 + values13 (153 : Fin 264)
    linarith [values13_strictMono (by native_decide : (152 : Fin 264) < 153)]
  next =>
    change 1 + values13 (153 : Fin 264) < 1 + values13 (154 : Fin 264)
    linarith [values13_strictMono (by native_decide : (153 : Fin 264) < 154)]
  next => exact values15_special_667
  next => exact values15_special_668
  next =>
    change 1 + values13 (155 : Fin 264) < 1 + values13 (156 : Fin 264)
    linarith [values13_strictMono (by native_decide : (155 : Fin 264) < 156)]
  next => exact values15_special_670
  next => exact values15_special_671
  next =>
    change 1 + values13 (157 : Fin 264) < 1 + values13 (158 : Fin 264)
    linarith [values13_strictMono (by native_decide : (157 : Fin 264) < 158)]
  next => exact values15_special_673
  next => exact values15_special_674
  next =>
    change 1 + values13 (159 : Fin 264) < 1 + values13 (160 : Fin 264)
    linarith [values13_strictMono (by native_decide : (159 : Fin 264) < 160)]
  next => exact values15_special_676
  next => exact values15_special_677
  next =>
    change 1 + values13 (161 : Fin 264) < 1 + values13 (162 : Fin 264)
    linarith [values13_strictMono (by native_decide : (161 : Fin 264) < 162)]
  next =>
    change 1 + values13 (162 : Fin 264) < 1 + values13 (163 : Fin 264)
    linarith [values13_strictMono (by native_decide : (162 : Fin 264) < 163)]
  next => exact values15_special_680
  next => exact values15_special_681
  next =>
    change 1 + values13 (164 : Fin 264) < 1 + values13 (165 : Fin 264)
    linarith [values13_strictMono (by native_decide : (164 : Fin 264) < 165)]
  next => exact values15_special_683
  next => exact values15_special_684
  next =>
    change 1 + values13 (166 : Fin 264) < 1 + values13 (167 : Fin 264)
    linarith [values13_strictMono (by native_decide : (166 : Fin 264) < 167)]
  next =>
    change 1 + values13 (167 : Fin 264) < 1 + values13 (168 : Fin 264)
    linarith [values13_strictMono (by native_decide : (167 : Fin 264) < 168)]
  next =>
    change 1 + values13 (168 : Fin 264) < 1 + values13 (169 : Fin 264)
    linarith [values13_strictMono (by native_decide : (168 : Fin 264) < 169)]
  next =>
    change 1 + values13 (169 : Fin 264) < 1 + values13 (170 : Fin 264)
    linarith [values13_strictMono (by native_decide : (169 : Fin 264) < 170)]
  next =>
    change 1 + values13 (170 : Fin 264) < 1 + values13 (171 : Fin 264)
    linarith [values13_strictMono (by native_decide : (170 : Fin 264) < 171)]
  next => exact values15_special_690
  next => exact values15_special_691
  next => exact values15_special_692
  next => exact values15_special_693
  next =>
    change 1 + values13 (173 : Fin 264) < 1 + values13 (174 : Fin 264)
    linarith [values13_strictMono (by native_decide : (173 : Fin 264) < 174)]
  next =>
    change 1 + values13 (174 : Fin 264) < 1 + values13 (175 : Fin 264)
    linarith [values13_strictMono (by native_decide : (174 : Fin 264) < 175)]
  next =>
    change 1 + values13 (175 : Fin 264) < 1 + values13 (176 : Fin 264)
    linarith [values13_strictMono (by native_decide : (175 : Fin 264) < 176)]
  next =>
    change 1 + values13 (176 : Fin 264) < 1 + values13 (177 : Fin 264)
    linarith [values13_strictMono (by native_decide : (176 : Fin 264) < 177)]
  next => exact values15_special_698
  next => exact values15_special_699
  next =>
    change 1 + values13 (178 : Fin 264) < 1 + values13 (179 : Fin 264)
    linarith [values13_strictMono (by native_decide : (178 : Fin 264) < 179)]
  next =>
    change 1 + values13 (179 : Fin 264) < 1 + values13 (180 : Fin 264)
    linarith [values13_strictMono (by native_decide : (179 : Fin 264) < 180)]
  next => exact values15_special_702
  next => exact values15_special_703
  next =>
    change 1 + values13 (181 : Fin 264) < 1 + values13 (182 : Fin 264)
    linarith [values13_strictMono (by native_decide : (181 : Fin 264) < 182)]
  next =>
    change 1 + values13 (182 : Fin 264) < 1 + values13 (183 : Fin 264)
    linarith [values13_strictMono (by native_decide : (182 : Fin 264) < 183)]
  next =>
    change 1 + values13 (183 : Fin 264) < 1 + values13 (184 : Fin 264)
    linarith [values13_strictMono (by native_decide : (183 : Fin 264) < 184)]
  next =>
    change 1 + values13 (184 : Fin 264) < 1 + values13 (185 : Fin 264)
    linarith [values13_strictMono (by native_decide : (184 : Fin 264) < 185)]
  next =>
    change 1 + values13 (185 : Fin 264) < 1 + values13 (186 : Fin 264)
    linarith [values13_strictMono (by native_decide : (185 : Fin 264) < 186)]
  next =>
    change 1 + values13 (186 : Fin 264) < 1 + values13 (187 : Fin 264)
    linarith [values13_strictMono (by native_decide : (186 : Fin 264) < 187)]
  next =>
    change 1 + values13 (187 : Fin 264) < 1 + values13 (188 : Fin 264)
    linarith [values13_strictMono (by native_decide : (187 : Fin 264) < 188)]
  next =>
    change 1 + values13 (188 : Fin 264) < 1 + values13 (189 : Fin 264)
    linarith [values13_strictMono (by native_decide : (188 : Fin 264) < 189)]
  next =>
    change 1 + values13 (189 : Fin 264) < 1 + values13 (190 : Fin 264)
    linarith [values13_strictMono (by native_decide : (189 : Fin 264) < 190)]
  next =>
    change 1 + values13 (190 : Fin 264) < 1 + values13 (191 : Fin 264)
    linarith [values13_strictMono (by native_decide : (190 : Fin 264) < 191)]
  next =>
    change 1 + values13 (191 : Fin 264) < 1 + values13 (192 : Fin 264)
    linarith [values13_strictMono (by native_decide : (191 : Fin 264) < 192)]
  next =>
    change 1 + values13 (192 : Fin 264) < 1 + values13 (193 : Fin 264)
    linarith [values13_strictMono (by native_decide : (192 : Fin 264) < 193)]
  next => exact values15_special_716
  next => exact values15_special_717
  next =>
    change 1 + values13 (194 : Fin 264) < 1 + values13 (195 : Fin 264)
    linarith [values13_strictMono (by native_decide : (194 : Fin 264) < 195)]
  next =>
    change 1 + values13 (195 : Fin 264) < 1 + values13 (196 : Fin 264)
    linarith [values13_strictMono (by native_decide : (195 : Fin 264) < 196)]
  next =>
    change 1 + values13 (196 : Fin 264) < 1 + values13 (197 : Fin 264)
    linarith [values13_strictMono (by native_decide : (196 : Fin 264) < 197)]
  next =>
    change 1 + values13 (197 : Fin 264) < 1 + values13 (198 : Fin 264)
    linarith [values13_strictMono (by native_decide : (197 : Fin 264) < 198)]
  next =>
    change 1 + values13 (198 : Fin 264) < 1 + values13 (199 : Fin 264)
    linarith [values13_strictMono (by native_decide : (198 : Fin 264) < 199)]
  next =>
    change 1 + values13 (199 : Fin 264) < 1 + values13 (200 : Fin 264)
    linarith [values13_strictMono (by native_decide : (199 : Fin 264) < 200)]
  next =>
    change 1 + values13 (200 : Fin 264) < 1 + values13 (201 : Fin 264)
    linarith [values13_strictMono (by native_decide : (200 : Fin 264) < 201)]
  next =>
    change 1 + values13 (201 : Fin 264) < 1 + values13 (202 : Fin 264)
    linarith [values13_strictMono (by native_decide : (201 : Fin 264) < 202)]
  next =>
    change 1 + values13 (202 : Fin 264) < 1 + values13 (203 : Fin 264)
    linarith [values13_strictMono (by native_decide : (202 : Fin 264) < 203)]
  next =>
    change 1 + values13 (203 : Fin 264) < 1 + values13 (204 : Fin 264)
    linarith [values13_strictMono (by native_decide : (203 : Fin 264) < 204)]
  next =>
    change 1 + values13 (204 : Fin 264) < 1 + values13 (205 : Fin 264)
    linarith [values13_strictMono (by native_decide : (204 : Fin 264) < 205)]
  next =>
    change 1 + values13 (205 : Fin 264) < 1 + values13 (206 : Fin 264)
    linarith [values13_strictMono (by native_decide : (205 : Fin 264) < 206)]
  next => exact values15_special_730
  next => exact values15_special_731
  next =>
    change 1 + values13 (207 : Fin 264) < 1 + values13 (208 : Fin 264)
    linarith [values13_strictMono (by native_decide : (207 : Fin 264) < 208)]
  next =>
    change 1 + values13 (208 : Fin 264) < 1 + values13 (209 : Fin 264)
    linarith [values13_strictMono (by native_decide : (208 : Fin 264) < 209)]
  next =>
    change 1 + values13 (209 : Fin 264) < 1 + values13 (210 : Fin 264)
    linarith [values13_strictMono (by native_decide : (209 : Fin 264) < 210)]
  next =>
    change 1 + values13 (210 : Fin 264) < 1 + values13 (211 : Fin 264)
    linarith [values13_strictMono (by native_decide : (210 : Fin 264) < 211)]
  next =>
    change 1 + values13 (211 : Fin 264) < 1 + values13 (212 : Fin 264)
    linarith [values13_strictMono (by native_decide : (211 : Fin 264) < 212)]
  next =>
    change 1 + values13 (212 : Fin 264) < 1 + values13 (213 : Fin 264)
    linarith [values13_strictMono (by native_decide : (212 : Fin 264) < 213)]
  next =>
    change 1 + values13 (213 : Fin 264) < 1 + values13 (214 : Fin 264)
    linarith [values13_strictMono (by native_decide : (213 : Fin 264) < 214)]
  next =>
    change 1 + values13 (214 : Fin 264) < 1 + values13 (215 : Fin 264)
    linarith [values13_strictMono (by native_decide : (214 : Fin 264) < 215)]
  next =>
    change 1 + values13 (215 : Fin 264) < 1 + values13 (216 : Fin 264)
    linarith [values13_strictMono (by native_decide : (215 : Fin 264) < 216)]
  next =>
    change 1 + values13 (216 : Fin 264) < 1 + values13 (217 : Fin 264)
    linarith [values13_strictMono (by native_decide : (216 : Fin 264) < 217)]
  next =>
    change 1 + values13 (217 : Fin 264) < 1 + values13 (218 : Fin 264)
    linarith [values13_strictMono (by native_decide : (217 : Fin 264) < 218)]
  next =>
    change 1 + values13 (218 : Fin 264) < 1 + values13 (219 : Fin 264)
    linarith [values13_strictMono (by native_decide : (218 : Fin 264) < 219)]
  next =>
    change 1 + values13 (219 : Fin 264) < 1 + values13 (220 : Fin 264)
    linarith [values13_strictMono (by native_decide : (219 : Fin 264) < 220)]
  next =>
    change 1 + values13 (220 : Fin 264) < 1 + values13 (221 : Fin 264)
    linarith [values13_strictMono (by native_decide : (220 : Fin 264) < 221)]
  next =>
    change 1 + values13 (221 : Fin 264) < 1 + values13 (222 : Fin 264)
    linarith [values13_strictMono (by native_decide : (221 : Fin 264) < 222)]
  next =>
    change 1 + values13 (222 : Fin 264) < 1 + values13 (223 : Fin 264)
    linarith [values13_strictMono (by native_decide : (222 : Fin 264) < 223)]
  next => exact values15_special_748
  next => exact values15_special_749
  next =>
    change 1 + values13 (224 : Fin 264) < 1 + values13 (225 : Fin 264)
    linarith [values13_strictMono (by native_decide : (224 : Fin 264) < 225)]
  next =>
    change 1 + values13 (225 : Fin 264) < 1 + values13 (226 : Fin 264)
    linarith [values13_strictMono (by native_decide : (225 : Fin 264) < 226)]
  next =>
    change 1 + values13 (226 : Fin 264) < 1 + values13 (227 : Fin 264)
    linarith [values13_strictMono (by native_decide : (226 : Fin 264) < 227)]
  next =>
    change 1 + values13 (227 : Fin 264) < 1 + values13 (228 : Fin 264)
    linarith [values13_strictMono (by native_decide : (227 : Fin 264) < 228)]
  next =>
    change 1 + values13 (228 : Fin 264) < 1 + values13 (229 : Fin 264)
    linarith [values13_strictMono (by native_decide : (228 : Fin 264) < 229)]
  next =>
    change 1 + values13 (229 : Fin 264) < 1 + values13 (230 : Fin 264)
    linarith [values13_strictMono (by native_decide : (229 : Fin 264) < 230)]
  next =>
    change 1 + values13 (230 : Fin 264) < 1 + values13 (231 : Fin 264)
    linarith [values13_strictMono (by native_decide : (230 : Fin 264) < 231)]
  next =>
    change 1 + values13 (231 : Fin 264) < 1 + values13 (232 : Fin 264)
    linarith [values13_strictMono (by native_decide : (231 : Fin 264) < 232)]
  next =>
    change 1 + values13 (232 : Fin 264) < 1 + values13 (233 : Fin 264)
    linarith [values13_strictMono (by native_decide : (232 : Fin 264) < 233)]
  next =>
    change 1 + values13 (233 : Fin 264) < 1 + values13 (234 : Fin 264)
    linarith [values13_strictMono (by native_decide : (233 : Fin 264) < 234)]
  next => exact values15_special_760
  next => exact values15_special_761
  next =>
    change 1 + values13 (235 : Fin 264) < 1 + values13 (236 : Fin 264)
    linarith [values13_strictMono (by native_decide : (235 : Fin 264) < 236)]
  next =>
    change 1 + values13 (236 : Fin 264) < 1 + values13 (237 : Fin 264)
    linarith [values13_strictMono (by native_decide : (236 : Fin 264) < 237)]
  next =>
    change 1 + values13 (237 : Fin 264) < 1 + values13 (238 : Fin 264)
    linarith [values13_strictMono (by native_decide : (237 : Fin 264) < 238)]
  next =>
    change 1 + values13 (238 : Fin 264) < 1 + values13 (239 : Fin 264)
    linarith [values13_strictMono (by native_decide : (238 : Fin 264) < 239)]
  next =>
    change 1 + values13 (239 : Fin 264) < 1 + values13 (240 : Fin 264)
    linarith [values13_strictMono (by native_decide : (239 : Fin 264) < 240)]
  next =>
    change 1 + values13 (240 : Fin 264) < 1 + values13 (241 : Fin 264)
    linarith [values13_strictMono (by native_decide : (240 : Fin 264) < 241)]
  next =>
    change 1 + values13 (241 : Fin 264) < 1 + values13 (242 : Fin 264)
    linarith [values13_strictMono (by native_decide : (241 : Fin 264) < 242)]
  next =>
    change 1 + values13 (242 : Fin 264) < 1 + values13 (243 : Fin 264)
    linarith [values13_strictMono (by native_decide : (242 : Fin 264) < 243)]
  next =>
    change 1 + values13 (243 : Fin 264) < 1 + values13 (244 : Fin 264)
    linarith [values13_strictMono (by native_decide : (243 : Fin 264) < 244)]
  next =>
    change 1 + values13 (244 : Fin 264) < 1 + values13 (245 : Fin 264)
    linarith [values13_strictMono (by native_decide : (244 : Fin 264) < 245)]
  next =>
    change 1 + values13 (245 : Fin 264) < 1 + values13 (246 : Fin 264)
    linarith [values13_strictMono (by native_decide : (245 : Fin 264) < 246)]
  next =>
    change 1 + values13 (246 : Fin 264) < 1 + values13 (247 : Fin 264)
    linarith [values13_strictMono (by native_decide : (246 : Fin 264) < 247)]
  next =>
    change 1 + values13 (247 : Fin 264) < 1 + values13 (248 : Fin 264)
    linarith [values13_strictMono (by native_decide : (247 : Fin 264) < 248)]
  next =>
    change 1 + values13 (248 : Fin 264) < 1 + values13 (249 : Fin 264)
    linarith [values13_strictMono (by native_decide : (248 : Fin 264) < 249)]
  next =>
    change 1 + values13 (249 : Fin 264) < 1 + values13 (250 : Fin 264)
    linarith [values13_strictMono (by native_decide : (249 : Fin 264) < 250)]
  next =>
    change 1 + values13 (250 : Fin 264) < 1 + values13 (251 : Fin 264)
    linarith [values13_strictMono (by native_decide : (250 : Fin 264) < 251)]
  next =>
    change 1 + values13 (251 : Fin 264) < 1 + values13 (252 : Fin 264)
    linarith [values13_strictMono (by native_decide : (251 : Fin 264) < 252)]
  next =>
    change 1 + values13 (252 : Fin 264) < 1 + values13 (253 : Fin 264)
    linarith [values13_strictMono (by native_decide : (252 : Fin 264) < 253)]
  next =>
    change 1 + values13 (253 : Fin 264) < 1 + values13 (254 : Fin 264)
    linarith [values13_strictMono (by native_decide : (253 : Fin 264) < 254)]
  next =>
    change 1 + values13 (254 : Fin 264) < 1 + values13 (255 : Fin 264)
    linarith [values13_strictMono (by native_decide : (254 : Fin 264) < 255)]
  next =>
    change 1 + values13 (255 : Fin 264) < 1 + values13 (256 : Fin 264)
    linarith [values13_strictMono (by native_decide : (255 : Fin 264) < 256)]
  next =>
    change 1 + values13 (256 : Fin 264) < 1 + values13 (257 : Fin 264)
    linarith [values13_strictMono (by native_decide : (256 : Fin 264) < 257)]
  next =>
    change 1 + values13 (257 : Fin 264) < 1 + values13 (258 : Fin 264)
    linarith [values13_strictMono (by native_decide : (257 : Fin 264) < 258)]
  next =>
    change 1 + values13 (258 : Fin 264) < 1 + values13 (259 : Fin 264)
    linarith [values13_strictMono (by native_decide : (258 : Fin 264) < 259)]
  next =>
    change 1 + values13 (259 : Fin 264) < 1 + values13 (260 : Fin 264)
    linarith [values13_strictMono (by native_decide : (259 : Fin 264) < 260)]
  next =>
    change 1 + values13 (260 : Fin 264) < 1 + values13 (261 : Fin 264)
    linarith [values13_strictMono (by native_decide : (260 : Fin 264) < 261)]
  next =>
    change 1 + values13 (261 : Fin 264) < 1 + values13 (262 : Fin 264)
    linarith [values13_strictMono (by native_decide : (261 : Fin 264) < 262)]
  next =>
    change 1 + values13 (262 : Fin 264) < 1 + values13 (263 : Fin 264)
    linarith [values13_strictMono (by native_decide : (262 : Fin 264) < 263)]

theorem values15_range_ncard :
    (Set.range values15).ncard = 791 := by
  rw [Set.ncard_range_of_injective values15_strictMono.injective]
  norm_num

end Expr
end A158415
end LeanProofs
