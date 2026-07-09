import LeanProofs.A158415FifteenTable
import LeanProofs.A158415IntervalCert

/-!
# Size-fifteen interval order certificates for OEIS A158415

This generated module replaces the large hand-expanded rational-bound
ladders for the exceptional adjacent comparisons in `values15` with
compact interval certificates checked by one soundness theorem.
-/

namespace LeanProofs
namespace A158415
namespace Expr

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def values15_special_430_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (3999 / 1000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_430_rightCert : IntervalCert :=
  IntervalCert.add (10003 / 5000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (100067 / 100000 : Rat) (1001 / 1000 : Rat) (IntervalCert.sqrt (20027 / 20000 : Rat) (501 / 500 : Rat) (IntervalCert.sqrt (100271 / 100000 : Rat) (1003 / 1000 : Rat) (IntervalCert.sqrt (1005429 / 1000000 : Rat) (503 / 500 : Rat) (IntervalCert.sqrt (1010889 / 1000000 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (1021897 / 1000000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_430 :
    values15 (430 : Fin 791) < values15 (431 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_430_leftCert values15_special_430_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_430_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_430_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (430 : Fin 791) = Real.sqrt (values14 (430 : Fin 455)) by rfl]
    simp only [values15_special_430_leftCert, IntervalCert.expr, eval]
    rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (431 : Fin 791) = 1 + values13 (1 : Fin 264) by rfl]
    simp only [values15_special_430_rightCert, IntervalCert.expr, eval]
    rw [show values13 (1 : Fin 264) = Real.sqrt (values12 (1 : Fin 154)) by rfl]
    rw [show values12 (1 : Fin 154) = Real.sqrt (values11 (1 : Fin 91)) by rfl]
    rw [show values11 (1 : Fin 91) = Real.sqrt (values10 (1 : Fin 54)) by rfl]
    rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_430_leftCert, values15_special_430_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_435_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (200543 / 100000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (201 / 200 : Rat) (100542991 / 100000000 : Rat) (IntervalCert.sqrt (2527 / 2500 : Rat) (10108893 / 10000000 : Rat) (IntervalCert.sqrt (5109 / 5000 : Rat) (20437943 / 20000000 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (1044273783 / 1000000000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1090507733 / 1000000000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (11892071151 / 10000000000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767766953 / 1250000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)))))))))))))

private def values15_special_435_rightCert : IntervalCert :=
  IntervalCert.sqrt (100273 / 50000 : Rat) (100 : Rat) (IntervalCert.add (402189 / 100000 : Rat) (2011 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3021897 / 1000000 : Rat) (30219 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (20218971 / 10000000 : Rat) (1010949 / 500000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (51094857 / 50000000 : Rat) (2554743 / 2500000 : Rat) (IntervalCert.sqrt (52213689 / 50000000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (109050773 / 100000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (118920711 / 100000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_435 :
    values15 (435 : Fin 791) < values15 (436 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_435_leftCert values15_special_435_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_435_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_435_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (435 : Fin 791) = 1 + values13 (5 : Fin 264) by rfl]
    simp only [values15_special_435_leftCert, IntervalCert.expr, eval]
    rw [show values13 (5 : Fin 264) = Real.sqrt (values12 (5 : Fin 154)) by rfl]
    rw [show values12 (5 : Fin 154) = Real.sqrt (values11 (5 : Fin 91)) by rfl]
    rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (436 : Fin 791) = Real.sqrt (values14 (431 : Fin 455)) by rfl]
    simp only [values15_special_435_rightCert, IntervalCert.expr, eval]
    rw [show values14 (431 : Fin 455) = 1 + values12 (131 : Fin 154) by rfl]
    rw [show values12 (131 : Fin 154) = 1 + values10 (32 : Fin 54) by rfl]
    rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_435_leftCert, values15_special_435_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_436_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (4011 / 2000 : Rat) (IntervalCert.add (4021 / 1000 : Rat) (2011 / 500 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (15109 / 5000 : Rat) (30219 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (202189 / 100000 : Rat) (1010949 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1021897 / 1000000 : Rat) (2554743 / 2500000 : Rat) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_436_rightCert : IntervalCert :=
  IntervalCert.add (20069 / 10000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1006909 / 1000000 : Rat) (1007 / 1000 : Rat) (IntervalCert.sqrt (506933 / 500000 : Rat) (507 / 500 : Rat) (IntervalCert.sqrt (41117 / 40000 : Rat) (257 / 250 : Rat) (IntervalCert.sqrt (105663 / 100000 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_436 :
    values15 (436 : Fin 791) < values15 (437 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_436_leftCert values15_special_436_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_436_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_436_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (436 : Fin 791) = Real.sqrt (values14 (431 : Fin 455)) by rfl]
    simp only [values15_special_436_leftCert, IntervalCert.expr, eval]
    rw [show values14 (431 : Fin 455) = 1 + values12 (131 : Fin 154) by rfl]
    rw [show values12 (131 : Fin 154) = 1 + values10 (32 : Fin 54) by rfl]
    rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (437 : Fin 791) = 1 + values13 (6 : Fin 264) by rfl]
    simp only [values15_special_436_rightCert, IntervalCert.expr, eval]
    rw [show values13 (6 : Fin 264) = Real.sqrt (values12 (6 : Fin 154)) by rfl]
    rw [show values12 (6 : Fin 154) = Real.sqrt (values11 (6 : Fin 91)) by rfl]
    rw [show values11 (6 : Fin 91) = Real.sqrt (values10 (6 : Fin 54)) by rfl]
    rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_436_leftCert, values15_special_436_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_439_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (20109 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (101 / 100 : Rat) (101089 / 100000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)))))))))))))

private def values15_special_439_rightCert : IntervalCert :=
  IntervalCert.sqrt (2011 / 1000 : Rat) (100 : Rat) (IntervalCert.add (20221 / 5000 : Rat) (809 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (304427 / 100000 : Rat) (30443 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_439 :
    values15 (439 : Fin 791) < values15 (440 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_439_leftCert values15_special_439_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_439_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_439_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (439 : Fin 791) = 1 + values13 (8 : Fin 264) by rfl]
    simp only [values15_special_439_leftCert, IntervalCert.expr, eval]
    rw [show values13 (8 : Fin 264) = Real.sqrt (values12 (8 : Fin 154)) by rfl]
    rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (440 : Fin 791) = Real.sqrt (values14 (432 : Fin 455)) by rfl]
    simp only [values15_special_439_rightCert, IntervalCert.expr, eval]
    rw [show values14 (432 : Fin 455) = 1 + values12 (132 : Fin 154) by rfl]
    rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
    rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_439_leftCert, values15_special_439_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_440_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (20111 / 10000 : Rat) (IntervalCert.add (1011 / 250 : Rat) (40443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (15221 / 5000 : Rat) (76107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (204427 / 100000 : Rat) (1022137 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1044273 / 1000000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_440_rightCert : IntervalCert :=
  IntervalCert.add (503 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (10123 / 10000 : Rat) (1013 / 1000 : Rat) (IntervalCert.sqrt (51239 / 50000 : Rat) (41 / 40 : Rat) (IntervalCert.sqrt (105019 / 100000 : Rat) (5251 / 5000 : Rat) (IntervalCert.sqrt (86164 / 78125 : Rat) (11029 / 10000 : Rat) (IntervalCert.sqrt (3040967 / 2500000 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (14795969 / 10000000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_440 :
    values15 (440 : Fin 791) < values15 (441 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_440_leftCert values15_special_440_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_440_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_440_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (440 : Fin 791) = Real.sqrt (values14 (432 : Fin 455)) by rfl]
    simp only [values15_special_440_leftCert, IntervalCert.expr, eval]
    rw [show values14 (432 : Fin 455) = 1 + values12 (132 : Fin 154) by rfl]
    rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
    rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (441 : Fin 791) = 1 + values13 (9 : Fin 264) by rfl]
    simp only [values15_special_440_rightCert, IntervalCert.expr, eval]
    rw [show values13 (9 : Fin 264) = Real.sqrt (values12 (9 : Fin 154)) by rfl]
    rw [show values12 (9 : Fin 154) = Real.sqrt (values11 (9 : Fin 91)) by rfl]
    rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by rfl]
    rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_440_leftCert, values15_special_440_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_444_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1011 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1021 / 1000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))))

private def values15_special_444_rightCert : IntervalCert :=
  IntervalCert.sqrt (809 / 400 : Rat) (100 : Rat) (IntervalCert.add (4090507 / 1000000 : Rat) (4091 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (30905077 / 10000000 : Rat) (15453 / 5000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (209050773 / 100000000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (272626933 / 250000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_444 :
    values15 (444 : Fin 791) < values15 (445 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_444_leftCert values15_special_444_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_444_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_444_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (444 : Fin 791) = 1 + values13 (12 : Fin 264) by rfl]
    simp only [values15_special_444_leftCert, IntervalCert.expr, eval]
    rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
    rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (445 : Fin 791) = Real.sqrt (values14 (433 : Fin 455)) by rfl]
    simp only [values15_special_444_rightCert, IntervalCert.expr, eval]
    rw [show values14 (433 : Fin 455) = 1 + values12 (133 : Fin 154) by rfl]
    rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
    rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_444_leftCert, values15_special_444_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_445_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (10113 / 5000 : Rat) (IntervalCert.add (409 / 100 : Rat) (20453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6181 / 2000 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2090507 / 1000000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_445_rightCert : IntervalCert :=
  IntervalCert.add (20233 / 10000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (102331 / 100000 : Rat) (128 / 125 : Rat) (IntervalCert.sqrt (523583 / 500000 : Rat) (131 / 125 : Rat) (IntervalCert.sqrt (1096557 / 1000000 : Rat) (1097 / 1000 : Rat) (IntervalCert.sqrt (601219 / 500000 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (722929 / 500000 : Rat) (723 / 500 : Rat) (IntervalCert.add (2090507 / 1000000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_445 :
    values15 (445 : Fin 791) < values15 (446 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_445_leftCert values15_special_445_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_445_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_445_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (445 : Fin 791) = Real.sqrt (values14 (433 : Fin 455)) by rfl]
    simp only [values15_special_445_leftCert, IntervalCert.expr, eval]
    rw [show values14 (433 : Fin 455) = 1 + values12 (133 : Fin 154) by rfl]
    rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
    rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (446 : Fin 791) = 1 + values13 (13 : Fin 264) by rfl]
    simp only [values15_special_445_rightCert, IntervalCert.expr, eval]
    rw [show values13 (13 : Fin 264) = Real.sqrt (values12 (13 : Fin 154)) by rfl]
    rw [show values12 (13 : Fin 154) = Real.sqrt (values11 (13 : Fin 91)) by rfl]
    rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by rfl]
    rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_445_leftCert, values15_special_445_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_450_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (407 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (517 / 500 : Rat) (103493 / 100000 : Rat) (IntervalCert.sqrt (1071 / 1000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

private def values15_special_450_rightCert : IntervalCert :=
  IntervalCert.sqrt (509 / 250 : Rat) (100 : Rat) (IntervalCert.add (2073 / 500 : Rat) (4147 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (15731 / 5000 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_450 :
    values15 (450 : Fin 791) < values15 (451 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_450_leftCert values15_special_450_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_450_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_450_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (450 : Fin 791) = 1 + values13 (17 : Fin 264) by rfl]
    simp only [values15_special_450_leftCert, IntervalCert.expr, eval]
    rw [show values13 (17 : Fin 264) = Real.sqrt (values12 (17 : Fin 154)) by rfl]
    rw [show values12 (17 : Fin 154) = Real.sqrt (values11 (17 : Fin 91)) by rfl]
    rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (451 : Fin 791) = Real.sqrt (values14 (434 : Fin 455)) by rfl]
    simp only [values15_special_450_rightCert, IntervalCert.expr, eval]
    rw [show values14 (434 : Fin 455) = 1 + values12 (134 : Fin 154) by rfl]
    rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_450_leftCert, values15_special_450_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_452_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2037 / 1000 : Rat) (IntervalCert.add (4147 / 1000 : Rat) (1037 / 250 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1967 / 625 : Rat) (31473 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1073601 / 500000 : Rat) (214721 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5736013 / 5000000 : Rat) (1147203 / 1000000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13160741 / 10000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_452_rightCert : IntervalCert :=
  IntervalCert.add (2039 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (10391 / 10000 : Rat) (26 / 25 : Rat) (IntervalCert.sqrt (13497 / 12500 : Rat) (27 / 25 : Rat) (IntervalCert.sqrt (11659 / 10000 : Rat) (583 / 500 : Rat) (IntervalCert.sqrt (1359323 / 1000000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (92387953 / 50000000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (85355339 / 25000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1207106781 / 500000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (14142135623 / 10000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999999 / 10000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_452 :
    values15 (452 : Fin 791) < values15 (453 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_452_leftCert values15_special_452_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_452_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_452_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (452 : Fin 791) = Real.sqrt (values14 (435 : Fin 455)) by rfl]
    simp only [values15_special_452_leftCert, IntervalCert.expr, eval]
    rw [show values14 (435 : Fin 455) = 1 + values12 (135 : Fin 154) by rfl]
    rw [show values12 (135 : Fin 154) = 1 + values10 (35 : Fin 54) by rfl]
    rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (453 : Fin 791) = 1 + values13 (18 : Fin 264) by rfl]
    simp only [values15_special_452_rightCert, IntervalCert.expr, eval]
    rw [show values13 (18 : Fin 264) = Real.sqrt (values12 (18 : Fin 154)) by rfl]
    rw [show values12 (18 : Fin 154) = Real.sqrt (values11 (18 : Fin 91)) by rfl]
    rw [show values11 (18 : Fin 91) = Real.sqrt (values10 (18 : Fin 54)) by rfl]
    rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_452_leftCert, values15_special_452_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_455_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1023 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (209 / 200 : Rat) (5229 / 5000 : Rat) (IntervalCert.sqrt (1093 / 1000 : Rat) (2187 / 2000 : Rat) (IntervalCert.sqrt (239 / 200 : Rat) (59787 / 50000 : Rat) (IntervalCert.sqrt (1429 / 1000 : Rat) (142979 / 100000 : Rat) (IntervalCert.add (511 / 250 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))))))

private def values15_special_455_rightCert : IntervalCert :=
  IntervalCert.sqrt (20467 / 10000 : Rat) (100 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (419 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_455 :
    values15 (455 : Fin 791) < values15 (456 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_455_leftCert values15_special_455_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_455_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_455_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (455 : Fin 791) = 1 + values13 (20 : Fin 264) by rfl]
    simp only [values15_special_455_leftCert, IntervalCert.expr, eval]
    rw [show values13 (20 : Fin 264) = Real.sqrt (values12 (20 : Fin 154)) by rfl]
    rw [show values12 (20 : Fin 154) = Real.sqrt (values11 (20 : Fin 91)) by rfl]
    rw [show values11 (20 : Fin 91) = Real.sqrt (values10 (20 : Fin 54)) by rfl]
    rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (456 : Fin 791) = Real.sqrt (values14 (436 : Fin 455)) by rfl]
    simp only [values15_special_455_rightCert, IntervalCert.expr, eval]
    rw [show values14 (436 : Fin 455) = 1 + values12 (136 : Fin 154) by rfl]
    rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_455_leftCert, values15_special_455_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_456_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_456_rightCert : IntervalCert :=
  IntervalCert.add (20471 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (26179 / 25000 : Rat) (131 / 125 : Rat) (IntervalCert.sqrt (21931 / 20000 : Rat) (1097 / 1000 : Rat) (IntervalCert.sqrt (120243 / 100000 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_456 :
    values15 (456 : Fin 791) < values15 (457 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_456_leftCert values15_special_456_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_456_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_456_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (456 : Fin 791) = Real.sqrt (values14 (436 : Fin 455)) by rfl]
    simp only [values15_special_456_leftCert, IntervalCert.expr, eval]
    rw [show values14 (436 : Fin 455) = 1 + values12 (136 : Fin 154) by rfl]
    rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (457 : Fin 791) = 1 + values13 (21 : Fin 264) by rfl]
    simp only [values15_special_456_rightCert, IntervalCert.expr, eval]
    rw [show values13 (21 : Fin 264) = Real.sqrt (values12 (21 : Fin 154)) by rfl]
    rw [show values12 (21 : Fin 154) = Real.sqrt (values11 (21 : Fin 91)) by rfl]
    rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_456_leftCert, values15_special_456_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_460_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2057 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (132 / 125 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (279 / 250 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

private def values15_special_460_rightCert : IntervalCert :=
  IntervalCert.sqrt (1029 / 500 : Rat) (100 : Rat) (IntervalCert.add (1059 / 250 : Rat) (4237 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (161803 / 50000 : Rat) (32361 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2236067 / 1000000 : Rat) (223607 / 100000 : Rat) (IntervalCert.add (4999999 / 1000000 : Rat) (5000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (39999999 / 10000000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_460 :
    values15 (460 : Fin 791) < values15 (461 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_460_leftCert values15_special_460_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_460_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_460_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (460 : Fin 791) = 1 + values13 (24 : Fin 264) by rfl]
    simp only [values15_special_460_leftCert, IntervalCert.expr, eval]
    rw [show values13 (24 : Fin 264) = Real.sqrt (values12 (24 : Fin 154)) by rfl]
    rw [show values12 (24 : Fin 154) = Real.sqrt (values11 (24 : Fin 91)) by rfl]
    rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (461 : Fin 791) = Real.sqrt (values14 (437 : Fin 455)) by rfl]
    simp only [values15_special_460_rightCert, IntervalCert.expr, eval]
    rw [show values14 (437 : Fin 455) = 1 + values12 (137 : Fin 154) by rfl]
    rw [show values12 (137 : Fin 154) = 1 + values10 (37 : Fin 54) by rfl]
    rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_460_leftCert, values15_special_460_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_462_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (10299 / 5000 : Rat) (IntervalCert.add (2121 / 500 : Rat) (42427 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.add (7071 / 2500 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values15_special_462_rightCert : IntervalCert :=
  IntervalCert.add (20603 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (53017 / 50000 : Rat) (1061 / 1000 : Rat) (IntervalCert.sqrt (56217 / 50000 : Rat) (9 / 8 : Rat) (IntervalCert.sqrt (1264141 / 1000000 : Rat) (253 / 200 : Rat) (IntervalCert.sqrt (1598053 / 1000000 : Rat) (1599 / 1000 : Rat) (IntervalCert.add (25537739 / 10000000 : Rat) (1277 / 500 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_462 :
    values15 (462 : Fin 791) < values15 (463 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_462_leftCert values15_special_462_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_462_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_462_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (462 : Fin 791) = Real.sqrt (values14 (438 : Fin 455)) by rfl]
    simp only [values15_special_462_leftCert, IntervalCert.expr, eval]
    rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (463 : Fin 791) = 1 + values13 (25 : Fin 264) by rfl]
    simp only [values15_special_462_rightCert, IntervalCert.expr, eval]
    rw [show values13 (25 : Fin 264) = Real.sqrt (values12 (25 : Fin 154)) by rfl]
    rw [show values12 (25 : Fin 154) = Real.sqrt (values11 (25 : Fin 91)) by rfl]
    rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_462_leftCert, values15_special_462_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_463_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (5151 / 2500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (53 / 50 : Rat) (21207 / 20000 : Rat) (IntervalCert.sqrt (281 / 250 : Rat) (1124341 / 1000000 : Rat) (IntervalCert.sqrt (158 / 125 : Rat) (632071 / 500000 : Rat) (IntervalCert.sqrt (799 / 500 : Rat) (799027 / 500000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (1276887 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (77688699 / 50000000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (241421357 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))))

private def values15_special_463_rightCert : IntervalCert :=
  IntervalCert.sqrt (20607 / 10000 : Rat) (100 : Rat) (IntervalCert.add (8493 / 2000 : Rat) (4247 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (405813 / 125000 : Rat) (16233 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (22465047 / 10000000 : Rat) (224651 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (623252351 / 500000000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (776886987 / 500000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (24142135623 / 10000000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_463 :
    values15 (463 : Fin 791) < values15 (464 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_463_leftCert values15_special_463_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_463_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_463_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (463 : Fin 791) = 1 + values13 (25 : Fin 264) by rfl]
    simp only [values15_special_463_leftCert, IntervalCert.expr, eval]
    rw [show values13 (25 : Fin 264) = Real.sqrt (values12 (25 : Fin 154)) by rfl]
    rw [show values12 (25 : Fin 154) = Real.sqrt (values11 (25 : Fin 91)) by rfl]
    rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (464 : Fin 791) = Real.sqrt (values14 (439 : Fin 455)) by rfl]
    simp only [values15_special_463_rightCert, IntervalCert.expr, eval]
    rw [show values14 (439 : Fin 455) = 1 + values12 (138 : Fin 154) by rfl]
    rw [show values12 (138 : Fin 154) = 1 + values10 (38 : Fin 54) by rfl]
    rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_463_leftCert, values15_special_463_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_464_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2061 / 1000 : Rat) (IntervalCert.add (2123 / 500 : Rat) (4247 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (6493 / 2000 : Rat) (16233 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (280813 / 125000 : Rat) (224651 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (12465047 / 10000000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_464_rightCert : IntervalCert :=
  IntervalCert.add (258 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1331 / 1250 : Rat) (213 / 200 : Rat) (IntervalCert.sqrt (5669 / 5000 : Rat) (567 / 500 : Rat) (IntervalCert.sqrt (1607 / 1250 : Rat) (12857 / 10000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_464 :
    values15 (464 : Fin 791) < values15 (465 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_464_leftCert values15_special_464_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_464_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_464_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (464 : Fin 791) = Real.sqrt (values14 (439 : Fin 455)) by rfl]
    simp only [values15_special_464_leftCert, IntervalCert.expr, eval]
    rw [show values14 (439 : Fin 455) = 1 + values12 (138 : Fin 154) by rfl]
    rw [show values12 (138 : Fin 154) = 1 + values10 (38 : Fin 54) by rfl]
    rw [show values10 (38 : Fin 54) = 1 + values8 (6 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (465 : Fin 791) = 1 + values13 (26 : Fin 264) by rfl]
    simp only [values15_special_464_rightCert, IntervalCert.expr, eval]
    rw [show values13 (26 : Fin 264) = Real.sqrt (values12 (26 : Fin 154)) by rfl]
    rw [show values12 (26 : Fin 154) = Real.sqrt (values11 (26 : Fin 91)) by rfl]
    rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_464_leftCert, values15_special_464_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_468_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1297 / 625 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (43 / 40 : Rat) (53759 / 50000 : Rat) (IntervalCert.sqrt (289 / 250 : Rat) (115601 / 100000 : Rat) (IntervalCert.sqrt (26727 / 20000 : Rat) (41761 / 31250 : Rat) (IntervalCert.sqrt (357167 / 200000 : Rat) (446459 / 250000 : Rat) (IntervalCert.add (3189207 / 1000000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_468_rightCert : IntervalCert :=
  IntervalCert.sqrt (2077 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_468 :
    values15 (468 : Fin 791) < values15 (469 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_468_leftCert values15_special_468_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_468_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_468_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (468 : Fin 791) = 1 + values13 (29 : Fin 264) by rfl]
    simp only [values15_special_468_leftCert, IntervalCert.expr, eval]
    rw [show values13 (29 : Fin 264) = Real.sqrt (values12 (29 : Fin 154)) by rfl]
    rw [show values12 (29 : Fin 154) = Real.sqrt (values11 (29 : Fin 91)) by rfl]
    rw [show values11 (29 : Fin 91) = Real.sqrt (values10 (29 : Fin 54)) by rfl]
    rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (469 : Fin 791) = Real.sqrt (values14 (440 : Fin 455)) by rfl]
    simp only [values15_special_468_rightCert, IntervalCert.expr, eval]
    rw [show values14 (440 : Fin 455) = 1 + values12 (139 : Fin 154) by rfl]
    rw [show values12 (139 : Fin 154) = 1 + values10 (39 : Fin 54) by rfl]
    rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_468_leftCert, values15_special_468_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_469_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1039 / 500 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_469_rightCert : IntervalCert :=
  IntervalCert.add (20797 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13497 / 12500 : Rat) (27 / 25 : Rat) (IntervalCert.sqrt (11659 / 10000 : Rat) (583 / 500 : Rat) (IntervalCert.sqrt (1359323 / 1000000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (92387953 / 50000000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (85355339 / 25000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1207106781 / 500000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (14142135623 / 10000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999999 / 10000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_469 :
    values15 (469 : Fin 791) < values15 (470 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_469_leftCert values15_special_469_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_469_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_469_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (469 : Fin 791) = Real.sqrt (values14 (440 : Fin 455)) by rfl]
    simp only [values15_special_469_leftCert, IntervalCert.expr, eval]
    rw [show values14 (440 : Fin 455) = 1 + values12 (139 : Fin 154) by rfl]
    rw [show values12 (139 : Fin 154) = 1 + values10 (39 : Fin 54) by rfl]
    rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (470 : Fin 791) = 1 + values13 (30 : Fin 264) by rfl]
    simp only [values15_special_469_rightCert, IntervalCert.expr, eval]
    rw [show values13 (30 : Fin 264) = Real.sqrt (values12 (30 : Fin 154)) by rfl]
    rw [show values12 (30 : Fin 154) = Real.sqrt (values11 (30 : Fin 91)) by rfl]
    rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_469_leftCert, values15_special_469_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_470_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (52 / 25 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1079 / 1000 : Rat) (5399 / 5000 : Rat) (IntervalCert.sqrt (233 / 200 : Rat) (116591 / 100000 : Rat) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_470_rightCert : IntervalCert :=
  IntervalCert.add (261 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_470 :
    values15 (470 : Fin 791) < values15 (471 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_470_leftCert values15_special_470_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_470_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_470_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (470 : Fin 791) = 1 + values13 (30 : Fin 264) by rfl]
    simp only [values15_special_470_leftCert, IntervalCert.expr, eval]
    rw [show values13 (30 : Fin 264) = Real.sqrt (values12 (30 : Fin 154)) by rfl]
    rw [show values12 (30 : Fin 154) = Real.sqrt (values11 (30 : Fin 91)) by rfl]
    rw [show values11 (30 : Fin 91) = Real.sqrt (values10 (30 : Fin 54)) by rfl]
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (471 : Fin 791) = values7 (1 : Fin 13) + values7 (1 : Fin 13) by rfl]
    simp only [values15_special_470_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_470_leftCert, values15_special_470_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_471_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2089 / 1000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_471_rightCert : IntervalCert :=
  IntervalCert.add (209 / 100 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_471 :
    values15 (471 : Fin 791) < values15 (472 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_471_leftCert values15_special_471_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_471_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_471_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (471 : Fin 791) = values7 (1 : Fin 13) + values7 (1 : Fin 13) by rfl]
    simp only [values15_special_471_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (472 : Fin 791) = 1 + values13 (31 : Fin 264) by rfl]
    simp only [values15_special_471_rightCert, IntervalCert.expr, eval]
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_471_leftCert, values15_special_471_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_476_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (21003 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (11 / 10 : Rat) (13753 / 12500 : Rat) (IntervalCert.sqrt (2421 / 2000 : Rat) (121051 / 100000 : Rat) (IntervalCert.sqrt (146533 / 100000 : Rat) (732667 / 500000 : Rat) (IntervalCert.add (1342 / 625 : Rat) (2147203 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))))

private def values15_special_476_rightCert : IntervalCert :=
  IntervalCert.sqrt (2101 / 1000 : Rat) (100 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (883 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_476 :
    values15 (476 : Fin 791) < values15 (477 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_476_leftCert values15_special_476_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_476_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_476_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (476 : Fin 791) = 1 + values13 (35 : Fin 264) by rfl]
    simp only [values15_special_476_leftCert, IntervalCert.expr, eval]
    rw [show values13 (35 : Fin 264) = Real.sqrt (values12 (35 : Fin 154)) by rfl]
    rw [show values12 (35 : Fin 154) = Real.sqrt (values11 (35 : Fin 91)) by rfl]
    rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by rfl]
    rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (477 : Fin 791) = Real.sqrt (values14 (441 : Fin 455)) by rfl]
    simp only [values15_special_476_rightCert, IntervalCert.expr, eval]
    rw [show values14 (441 : Fin 455) = 1 + values12 (140 : Fin 154) by rfl]
    rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_476_leftCert, values15_special_476_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_477_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (21011 / 10000 : Rat) (IntervalCert.add (2207 / 500 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (17071 / 5000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (241421 / 100000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_477_rightCert : IntervalCert :=
  IntervalCert.add (5257 / 2500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (110289 / 100000 : Rat) (1103 / 1000 : Rat) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_477 :
    values15 (477 : Fin 791) < values15 (478 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_477_leftCert values15_special_477_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_477_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_477_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (477 : Fin 791) = Real.sqrt (values14 (441 : Fin 455)) by rfl]
    simp only [values15_special_477_leftCert, IntervalCert.expr, eval]
    rw [show values14 (441 : Fin 455) = 1 + values12 (140 : Fin 154) by rfl]
    rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (478 : Fin 791) = 1 + values13 (36 : Fin 264) by rfl]
    simp only [values15_special_477_rightCert, IntervalCert.expr, eval]
    rw [show values13 (36 : Fin 264) = Real.sqrt (values12 (36 : Fin 154)) by rfl]
    rw [show values12 (36 : Fin 154) = Real.sqrt (values11 (36 : Fin 91)) by rfl]
    rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_477_leftCert, values15_special_477_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_481_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2111 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (111 / 100 : Rat) (11107 / 10000 : Rat) (IntervalCert.sqrt (1233 / 1000 : Rat) (30841 / 25000 : Rat) (IntervalCert.sqrt (1521 / 1000 : Rat) (760933 / 500000 : Rat) (IntervalCert.add (579 / 250 : Rat) (92643 / 40000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (13160741 / 10000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_481_rightCert : IntervalCert :=
  IntervalCert.add (264 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (5109 / 5000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_481 :
    values15 (481 : Fin 791) < values15 (482 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_481_leftCert values15_special_481_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_481_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_481_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (481 : Fin 791) = 1 + values13 (39 : Fin 264) by rfl]
    simp only [values15_special_481_leftCert, IntervalCert.expr, eval]
    rw [show values13 (39 : Fin 264) = Real.sqrt (values12 (39 : Fin 154)) by rfl]
    rw [show values12 (39 : Fin 154) = Real.sqrt (values11 (39 : Fin 91)) by rfl]
    rw [show values11 (39 : Fin 91) = Real.sqrt (values10 (39 : Fin 54)) by rfl]
    rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (482 : Fin 791) = values6 (1 : Fin 8) + values8 (1 : Fin 20) by rfl]
    simp only [values15_special_481_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_481_leftCert, values15_special_481_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_482_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2113 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_482_rightCert : IntervalCert :=
  IntervalCert.add (529 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_482 :
    values15 (482 : Fin 791) < values15 (483 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_482_leftCert values15_special_482_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_482_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_482_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (482 : Fin 791) = values6 (1 : Fin 8) + values8 (1 : Fin 20) by rfl]
    simp only [values15_special_482_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (483 : Fin 791) = 1 + values13 (40 : Fin 264) by rfl]
    simp only [values15_special_482_rightCert, IntervalCert.expr, eval]
    rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
    rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_482_leftCert, values15_special_482_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_483_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (211647 / 100000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (279 / 250 : Rat) (5582349 / 5000000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (1558131 / 1250000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))))

private def values15_special_483_rightCert : IntervalCert :=
  IntervalCert.sqrt (4233 / 2000 : Rat) (100 : Rat) (IntervalCert.add (447959 / 100000 : Rat) (112 / 25 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (869899 / 250000 : Rat) (8699 / 2500 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (24795969 / 10000000 : Rat) (2479597 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (73979847 / 50000000 : Rat) (29591939 / 20000000 : Rat) (IntervalCert.add (218920711 / 100000000 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_483 :
    values15 (483 : Fin 791) < values15 (484 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_483_leftCert values15_special_483_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_483_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_483_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (483 : Fin 791) = 1 + values13 (40 : Fin 264) by rfl]
    simp only [values15_special_483_leftCert, IntervalCert.expr, eval]
    rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
    rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (484 : Fin 791) = Real.sqrt (values14 (442 : Fin 455)) by rfl]
    simp only [values15_special_483_rightCert, IntervalCert.expr, eval]
    rw [show values14 (442 : Fin 455) = 1 + values12 (141 : Fin 154) by rfl]
    rw [show values12 (141 : Fin 154) = 1 + values10 (41 : Fin 54) by rfl]
    rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_483_leftCert, values15_special_483_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_484_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2117 / 1000 : Rat) (IntervalCert.add (4479 / 1000 : Rat) (112 / 25 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (6959 / 2000 : Rat) (8699 / 2500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (247959 / 100000 : Rat) (2479597 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (369899 / 250000 : Rat) (29591939 / 20000000 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

private def values15_special_484_rightCert : IntervalCert :=
  IntervalCert.add (53 / 25 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (5601 / 5000 : Rat) (1121 / 1000 : Rat) (IntervalCert.sqrt (25097 / 20000 : Rat) (251 / 200 : Rat) (IntervalCert.sqrt (157467 / 100000 : Rat) (63 / 40 : Rat) (IntervalCert.add (247959 / 100000 : Rat) (62 / 25 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (369899 / 250000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_484 :
    values15 (484 : Fin 791) < values15 (485 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_484_leftCert values15_special_484_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_484_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_484_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (484 : Fin 791) = Real.sqrt (values14 (442 : Fin 455)) by rfl]
    simp only [values15_special_484_leftCert, IntervalCert.expr, eval]
    rw [show values14 (442 : Fin 455) = 1 + values12 (141 : Fin 154) by rfl]
    rw [show values12 (141 : Fin 154) = 1 + values10 (41 : Fin 54) by rfl]
    rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (485 : Fin 791) = 1 + values13 (41 : Fin 264) by rfl]
    simp only [values15_special_484_rightCert, IntervalCert.expr, eval]
    rw [show values13 (41 : Fin 264) = Real.sqrt (values12 (41 : Fin 154)) by rfl]
    rw [show values12 (41 : Fin 154) = Real.sqrt (values11 (41 : Fin 91)) by rfl]
    rw [show values11 (41 : Fin 91) = Real.sqrt (values10 (41 : Fin 54)) by rfl]
    rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_484_leftCert, values15_special_484_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_488_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (213387 / 100000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1133 / 1000 : Rat) (226773 / 200000 : Rat) (IntervalCert.sqrt (257 / 200 : Rat) (1285649 / 1000000 : Rat) (IntervalCert.sqrt (413 / 250 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))))

private def values15_special_488_rightCert : IntervalCert :=
  IntervalCert.sqrt (42679 / 20000 : Rat) (100 : Rat) (IntervalCert.add (455377 / 100000 : Rat) (2277 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3553773 / 1000000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (25537739 / 10000000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_488 :
    values15 (488 : Fin 791) < values15 (489 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_488_leftCert values15_special_488_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_488_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_488_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (488 : Fin 791) = 1 + values13 (44 : Fin 264) by rfl]
    simp only [values15_special_488_leftCert, IntervalCert.expr, eval]
    rw [show values13 (44 : Fin 264) = Real.sqrt (values12 (44 : Fin 154)) by rfl]
    rw [show values12 (44 : Fin 154) = Real.sqrt (values11 (44 : Fin 91)) by rfl]
    rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (489 : Fin 791) = Real.sqrt (values14 (443 : Fin 455)) by rfl]
    simp only [values15_special_488_rightCert, IntervalCert.expr, eval]
    rw [show values14 (443 : Fin 455) = 1 + values12 (142 : Fin 154) by rfl]
    rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
    rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_488_leftCert, values15_special_488_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_489_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1067 / 500 : Rat) (IntervalCert.add (4553 / 1000 : Rat) (22769 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (35537 / 10000 : Rat) (177689 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (1276887 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77688699 / 50000000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (241421357 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

private def values15_special_489_rightCert : IntervalCert :=
  IntervalCert.add (21347 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (104427 / 100000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_489 :
    values15 (489 : Fin 791) < values15 (490 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_489_leftCert values15_special_489_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_489_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_489_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (489 : Fin 791) = Real.sqrt (values14 (443 : Fin 455)) by rfl]
    simp only [values15_special_489_leftCert, IntervalCert.expr, eval]
    rw [show values14 (443 : Fin 455) = 1 + values12 (142 : Fin 154) by rfl]
    rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
    rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (490 : Fin 791) = values6 (1 : Fin 8) + values8 (2 : Fin 20) by rfl]
    simp only [values15_special_489_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_489_leftCert, values15_special_489_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_490_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (427 / 200 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_490_rightCert : IntervalCert :=
  IntervalCert.add (1069 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (11387 / 10000 : Rat) (1139 / 1000 : Rat) (IntervalCert.sqrt (1621 / 1250 : Rat) (1297 / 1000 : Rat) (IntervalCert.sqrt (16817 / 10000 : Rat) (841 / 500 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_490 :
    values15 (490 : Fin 791) < values15 (491 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_490_leftCert values15_special_490_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_490_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_490_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (490 : Fin 791) = values6 (1 : Fin 8) + values8 (2 : Fin 20) by rfl]
    simp only [values15_special_490_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (491 : Fin 791) = 1 + values13 (45 : Fin 264) by rfl]
    simp only [values15_special_490_rightCert, IntervalCert.expr, eval]
    rw [show values13 (45 : Fin 264) = Real.sqrt (values12 (45 : Fin 154)) by rfl]
    rw [show values12 (45 : Fin 154) = Real.sqrt (values11 (45 : Fin 91)) by rfl]
    rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_490_leftCert, values15_special_490_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_491_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2139 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (569 / 500 : Rat) (2847 / 2500 : Rat) (IntervalCert.sqrt (162 / 125 : Rat) (32421 / 25000 : Rat) (IntervalCert.sqrt (1681 / 1000 : Rat) (1681793 / 1000000 : Rat) (IntervalCert.add (707 / 250 : Rat) (1767767 / 625000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_491_rightCert : IntervalCert :=
  IntervalCert.sqrt (429 / 200 : Rat) (100 : Rat) (IntervalCert.add (4603 / 1000 : Rat) (1151 / 250 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (18017 / 5000 : Rat) (7207 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (130171 / 50000 : Rat) (260343 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_491 :
    values15 (491 : Fin 791) < values15 (492 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_491_leftCert values15_special_491_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_491_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_491_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (491 : Fin 791) = 1 + values13 (45 : Fin 264) by rfl]
    simp only [values15_special_491_leftCert, IntervalCert.expr, eval]
    rw [show values13 (45 : Fin 264) = Real.sqrt (values12 (45 : Fin 154)) by rfl]
    rw [show values12 (45 : Fin 154) = Real.sqrt (values11 (45 : Fin 91)) by rfl]
    rw [show values11 (45 : Fin 91) = Real.sqrt (values10 (45 : Fin 54)) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (492 : Fin 791) = Real.sqrt (values14 (444 : Fin 455)) by rfl]
    simp only [values15_special_491_rightCert, IntervalCert.expr, eval]
    rw [show values14 (444 : Fin 455) = 1 + values12 (143 : Fin 154) by rfl]
    rw [show values12 (143 : Fin 154) = 1 + values10 (43 : Fin 54) by rfl]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_491_leftCert, values15_special_491_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_492_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1073 / 500 : Rat) (IntervalCert.add (4603 / 1000 : Rat) (1151 / 250 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (18017 / 5000 : Rat) (7207 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (130171 / 50000 : Rat) (260343 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_492_rightCert : IntervalCert :=
  IntervalCert.add (2147 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_492 :
    values15 (492 : Fin 791) < values15 (493 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_492_leftCert values15_special_492_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_492_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_492_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (492 : Fin 791) = Real.sqrt (values14 (444 : Fin 455)) by rfl]
    simp only [values15_special_492_leftCert, IntervalCert.expr, eval]
    rw [show values14 (444 : Fin 455) = 1 + values12 (143 : Fin 154) by rfl]
    rw [show values12 (143 : Fin 154) = 1 + values10 (43 : Fin 54) by rfl]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (493 : Fin 791) = 1 + values13 (46 : Fin 264) by rfl]
    simp only [values15_special_492_rightCert, IntervalCert.expr, eval]
    rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
    rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_492_leftCert, values15_special_492_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_496_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1083 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (233 / 200 : Rat) (116591 / 100000 : Rat) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_496_rightCert : IntervalCert :=
  IntervalCert.sqrt (87 / 40 : Rat) (100 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_496 :
    values15 (496 : Fin 791) < values15 (497 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_496_leftCert values15_special_496_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_496_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_496_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (496 : Fin 791) = 1 + values13 (49 : Fin 264) by rfl]
    simp only [values15_special_496_leftCert, IntervalCert.expr, eval]
    rw [show values13 (49 : Fin 264) = Real.sqrt (values12 (49 : Fin 154)) by rfl]
    rw [show values12 (49 : Fin 154) = Real.sqrt (values11 (49 : Fin 91)) by rfl]
    rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
    rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (497 : Fin 791) = Real.sqrt (values14 (445 : Fin 455)) by rfl]
    simp only [values15_special_496_rightCert, IntervalCert.expr, eval]
    rw [show values14 (445 : Fin 455) = 1 + values12 (144 : Fin 154) by rfl]
    rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_496_leftCert, values15_special_496_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_497_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (272 / 125 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_497_rightCert : IntervalCert :=
  IntervalCert.add (1089 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (11789 / 10000 : Rat) (1179 / 1000 : Rat) (IntervalCert.sqrt (13899 / 10000 : Rat) (139 / 100 : Rat) (IntervalCert.sqrt (38637 / 20000 : Rat) (483 / 250 : Rat) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_497 :
    values15 (497 : Fin 791) < values15 (498 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_497_leftCert values15_special_497_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_497_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_497_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (497 : Fin 791) = Real.sqrt (values14 (445 : Fin 455)) by rfl]
    simp only [values15_special_497_leftCert, IntervalCert.expr, eval]
    rw [show values14 (445 : Fin 455) = 1 + values12 (144 : Fin 154) by rfl]
    rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (498 : Fin 791) = 1 + values13 (50 : Fin 264) by rfl]
    simp only [values15_special_497_rightCert, IntervalCert.expr, eval]
    rw [show values13 (50 : Fin 264) = Real.sqrt (values12 (50 : Fin 154)) by rfl]
    rw [show values12 (50 : Fin 154) = Real.sqrt (values11 (50 : Fin 91)) by rfl]
    rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by rfl]
    rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_497_leftCert, values15_special_497_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_498_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2179 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (589 / 500 : Rat) (23579 / 20000 : Rat) (IntervalCert.sqrt (1389 / 1000 : Rat) (8687 / 6250 : Rat) (IntervalCert.sqrt (1931 / 1000 : Rat) (96593 / 50000 : Rat) (IntervalCert.add (933 / 250 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_498_rightCert : IntervalCert :=
  IntervalCert.add (2181 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_498 :
    values15 (498 : Fin 791) < values15 (499 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_498_leftCert values15_special_498_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_498_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_498_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (498 : Fin 791) = 1 + values13 (50 : Fin 264) by rfl]
    simp only [values15_special_498_leftCert, IntervalCert.expr, eval]
    rw [show values13 (50 : Fin 264) = Real.sqrt (values12 (50 : Fin 154)) by rfl]
    rw [show values12 (50 : Fin 154) = Real.sqrt (values11 (50 : Fin 91)) by rfl]
    rw [show values11 (50 : Fin 91) = Real.sqrt (values10 (50 : Fin 54)) by rfl]
    rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (499 : Fin 791) = values6 (1 : Fin 8) + values8 (3 : Fin 20) by rfl]
    simp only [values15_special_498_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_498_leftCert, values15_special_498_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_499_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1091 / 500 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))))))

private def values15_special_499_rightCert : IntervalCert :=
  IntervalCert.add (2189 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_499 :
    values15 (499 : Fin 791) < values15 (500 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_499_leftCert values15_special_499_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_499_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_499_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (499 : Fin 791) = values6 (1 : Fin 8) + values8 (3 : Fin 20) by rfl]
    simp only [values15_special_499_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (500 : Fin 791) = 1 + values13 (51 : Fin 264) by rfl]
    simp only [values15_special_499_rightCert, IntervalCert.expr, eval]
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_499_leftCert, values15_special_499_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_503_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (549 / 250 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (239 / 200 : Rat) (5979 / 5000 : Rat) (IntervalCert.sqrt (1429 / 1000 : Rat) (7149 / 5000 : Rat) (IntervalCert.add (511 / 250 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values15_special_503_rightCert : IntervalCert :=
  IntervalCert.sqrt (2197 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_503 :
    values15 (503 : Fin 791) < values15 (504 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_503_leftCert values15_special_503_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_503_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_503_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (503 : Fin 791) = 1 + values13 (54 : Fin 264) by rfl]
    simp only [values15_special_503_leftCert, IntervalCert.expr, eval]
    rw [show values13 (54 : Fin 264) = Real.sqrt (values12 (54 : Fin 154)) by rfl]
    rw [show values12 (54 : Fin 154) = Real.sqrt (values11 (54 : Fin 91)) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (504 : Fin 791) = Real.sqrt (values14 (446 : Fin 455)) by rfl]
    simp only [values15_special_503_rightCert, IntervalCert.expr, eval]
    rw [show values14 (446 : Fin 455) = 1 + values12 (145 : Fin 154) by rfl]
    rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_503_leftCert, values15_special_503_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_504_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1099 / 500 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_504_rightCert : IntervalCert :=
  IntervalCert.add (2199 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2999 / 2500 : Rat) (6 / 5 : Rat) (IntervalCert.sqrt (14391 / 10000 : Rat) (1799 / 1250 : Rat) (IntervalCert.add (207107 / 100000 : Rat) (20711 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_504 :
    values15 (504 : Fin 791) < values15 (505 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_504_leftCert values15_special_504_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_504_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_504_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (504 : Fin 791) = Real.sqrt (values14 (446 : Fin 455)) by rfl]
    simp only [values15_special_504_leftCert, IntervalCert.expr, eval]
    rw [show values14 (446 : Fin 455) = 1 + values12 (145 : Fin 154) by rfl]
    rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (505 : Fin 791) = 1 + values13 (55 : Fin 264) by rfl]
    simp only [values15_special_504_rightCert, IntervalCert.expr, eval]
    rw [show values13 (55 : Fin 264) = Real.sqrt (values12 (55 : Fin 154)) by rfl]
    rw [show values12 (55 : Fin 154) = Real.sqrt (values11 (55 : Fin 91)) by rfl]
    rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_504_leftCert, values15_special_504_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_505_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (21997 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1199 / 1000 : Rat) (29991 / 25000 : Rat) (IntervalCert.sqrt (1439 / 1000 : Rat) (143913 / 100000 : Rat) (IntervalCert.add (2071 / 1000 : Rat) (51777 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (107107 / 100000 : Rat) (267769 / 250000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (1147203 / 1000000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (13160741 / 10000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_505_rightCert : IntervalCert :=
  IntervalCert.add (11 / 5 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_505 :
    values15 (505 : Fin 791) < values15 (506 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_505_leftCert values15_special_505_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_505_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_505_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (505 : Fin 791) = 1 + values13 (55 : Fin 264) by rfl]
    simp only [values15_special_505_leftCert, IntervalCert.expr, eval]
    rw [show values13 (55 : Fin 264) = Real.sqrt (values12 (55 : Fin 154)) by rfl]
    rw [show values12 (55 : Fin 154) = Real.sqrt (values11 (55 : Fin 91)) by rfl]
    rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (506 : Fin 791) = values5 (1 : Fin 5) + values9 (1 : Fin 33) by rfl]
    simp only [values15_special_505_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_505_leftCert, values15_special_505_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_506_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (22001 / 10000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (101 / 100 : Rat) (101089 / 100000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values15_special_506_rightCert : IntervalCert :=
  IntervalCert.add (1101 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1503 / 1250 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (7229 / 5000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_506 :
    values15 (506 : Fin 791) < values15 (507 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_506_leftCert values15_special_506_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_506_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_506_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (506 : Fin 791) = values5 (1 : Fin 5) + values9 (1 : Fin 33) by rfl]
    simp only [values15_special_506_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (507 : Fin 791) = 1 + values13 (56 : Fin 264) by rfl]
    simp only [values15_special_506_rightCert, IntervalCert.expr, eval]
    rw [show values13 (56 : Fin 264) = Real.sqrt (values12 (56 : Fin 154)) by rfl]
    rw [show values12 (56 : Fin 154) = Real.sqrt (values11 (56 : Fin 91)) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_506_leftCert, values15_special_506_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_510_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (11053 / 5000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (121 / 100 : Rat) (121051 / 100000 : Rat) (IntervalCert.sqrt (293 / 200 : Rat) (732667 / 500000 : Rat) (IntervalCert.add (2147 / 1000 : Rat) (2147203 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (717 / 625 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))))

private def values15_special_510_rightCert : IntervalCert :=
  IntervalCert.add (2211 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_510 :
    values15 (510 : Fin 791) < values15 (511 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_510_leftCert values15_special_510_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_510_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_510_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (510 : Fin 791) = 1 + values13 (59 : Fin 264) by rfl]
    simp only [values15_special_510_leftCert, IntervalCert.expr, eval]
    rw [show values13 (59 : Fin 264) = Real.sqrt (values12 (59 : Fin 154)) by rfl]
    rw [show values12 (59 : Fin 154) = Real.sqrt (values11 (59 : Fin 91)) by rfl]
    rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (511 : Fin 791) = values5 (1 : Fin 5) + values9 (2 : Fin 33) by rfl]
    simp only [values15_special_510_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_510_leftCert, values15_special_510_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_511_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (553 / 250 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_511_rightCert : IntervalCert :=
  IntervalCert.add (277 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_511 :
    values15 (511 : Fin 791) < values15 (512 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_511_leftCert values15_special_511_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_511_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_511_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (511 : Fin 791) = values5 (1 : Fin 5) + values9 (2 : Fin 33) by rfl]
    simp only [values15_special_511_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (512 : Fin 791) = 1 + values13 (60 : Fin 264) by rfl]
    simp only [values15_special_511_rightCert, IntervalCert.expr, eval]
    rw [show values13 (60 : Fin 264) = Real.sqrt (values12 (60 : Fin 154)) by rfl]
    rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_511_leftCert, values15_special_511_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_515_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (89 / 40 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (153 / 125 : Rat) (12243 / 10000 : Rat) (IntervalCert.sqrt (3747 / 2500 : Rat) (14989 / 10000 : Rat) (IntervalCert.add (4493 / 2000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_515_rightCert : IntervalCert :=
  IntervalCert.add (2233 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_515 :
    values15 (515 : Fin 791) < values15 (516 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_515_leftCert values15_special_515_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_515_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_515_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (515 : Fin 791) = 1 + values13 (63 : Fin 264) by rfl]
    simp only [values15_special_515_leftCert, IntervalCert.expr, eval]
    rw [show values13 (63 : Fin 264) = Real.sqrt (values12 (63 : Fin 154)) by rfl]
    rw [show values12 (63 : Fin 154) = Real.sqrt (values11 (63 : Fin 91)) by rfl]
    rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (516 : Fin 791) = values5 (1 : Fin 5) + values9 (3 : Fin 33) by rfl]
    simp only [values15_special_515_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_515_leftCert, values15_special_515_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_516_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4467 / 2000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_516_rightCert : IntervalCert :=
  IntervalCert.add (1396 / 625 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (123363 / 100000 : Rat) (617 / 500 : Rat) (IntervalCert.sqrt (76093 / 50000 : Rat) (761 / 500 : Rat) (IntervalCert.add (231607 / 100000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_516 :
    values15 (516 : Fin 791) < values15 (517 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_516_leftCert values15_special_516_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_516_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_516_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (516 : Fin 791) = values5 (1 : Fin 5) + values9 (3 : Fin 33) by rfl]
    simp only [values15_special_516_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (517 : Fin 791) = 1 + values13 (64 : Fin 264) by rfl]
    simp only [values15_special_516_rightCert, IntervalCert.expr, eval]
    rw [show values13 (64 : Fin 264) = Real.sqrt (values12 (64 : Fin 154)) by rfl]
    rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_516_leftCert, values15_special_516_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_517_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1117 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1233 / 1000 : Rat) (12337 / 10000 : Rat) (IntervalCert.sqrt (1521 / 1000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_517_rightCert : IntervalCert :=
  IntervalCert.sqrt (559 / 250 : Rat) (100 : Rat) (IntervalCert.add (49999 / 10000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_517 :
    values15 (517 : Fin 791) < values15 (518 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_517_leftCert values15_special_517_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_517_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_517_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (517 : Fin 791) = 1 + values13 (64 : Fin 264) by rfl]
    simp only [values15_special_517_leftCert, IntervalCert.expr, eval]
    rw [show values13 (64 : Fin 264) = Real.sqrt (values12 (64 : Fin 154)) by rfl]
    rw [show values12 (64 : Fin 154) = Real.sqrt (values11 (64 : Fin 91)) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (518 : Fin 791) = Real.sqrt (values14 (447 : Fin 455)) by rfl]
    simp only [values15_special_517_rightCert, IntervalCert.expr, eval]
    rw [show values14 (447 : Fin 455) = 1 + values12 (146 : Fin 154) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_517_leftCert, values15_special_517_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_518_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (22361 / 10000 : Rat) (IntervalCert.add (4999 / 1000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (39999 / 10000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.add (3999999 / 1000000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))

private def values15_special_518_rightCert : IntervalCert :=
  IntervalCert.add (22377 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_518 :
    values15 (518 : Fin 791) < values15 (519 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_518_leftCert values15_special_518_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_518_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_518_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (518 : Fin 791) = Real.sqrt (values14 (447 : Fin 455)) by rfl]
    simp only [values15_special_518_leftCert, IntervalCert.expr, eval]
    rw [show values14 (447 : Fin 455) = 1 + values12 (146 : Fin 154) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (519 : Fin 791) = values6 (1 : Fin 8) + values8 (4 : Fin 20) by rfl]
    simp only [values15_special_518_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_518_leftCert, values15_special_518_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_519_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1119 / 500 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (1147 / 1000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_519_rightCert : IntervalCert :=
  IntervalCert.add (2241 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (6209 / 5000 : Rat) (621 / 500 : Rat) (IntervalCert.sqrt (7711 / 5000 : Rat) (15423 / 10000 : Rat) (IntervalCert.add (2973 / 1250 : Rat) (4757 / 2000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_519 :
    values15 (519 : Fin 791) < values15 (520 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_519_leftCert values15_special_519_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_519_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_519_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (519 : Fin 791) = values6 (1 : Fin 8) + values8 (4 : Fin 20) by rfl]
    simp only [values15_special_519_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (520 : Fin 791) = 1 + values13 (65 : Fin 264) by rfl]
    simp only [values15_special_519_rightCert, IntervalCert.expr, eval]
    rw [show values13 (65 : Fin 264) = Real.sqrt (values12 (65 : Fin 154)) by rfl]
    rw [show values12 (65 : Fin 154) = Real.sqrt (values11 (65 : Fin 91)) by rfl]
    rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_519_leftCert, values15_special_519_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_523_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (451 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (627 / 500 : Rat) (12549 / 10000 : Rat) (IntervalCert.sqrt (787 / 500 : Rat) (15747 / 10000 : Rat) (IntervalCert.add (2479 / 1000 : Rat) (6199 / 2500 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2959 / 2000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_523_rightCert : IntervalCert :=
  IntervalCert.sqrt (282 / 125 : Rat) (100 : Rat) (IntervalCert.add (509 / 100 : Rat) (5091 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (8181 / 2000 : Rat) (20453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3090507 / 1000000 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (20905077 / 10000000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (109050773 / 100000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (118920711 / 100000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_523 :
    values15 (523 : Fin 791) < values15 (524 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_523_leftCert values15_special_523_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_523_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_523_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (523 : Fin 791) = 1 + values13 (68 : Fin 264) by rfl]
    simp only [values15_special_523_leftCert, IntervalCert.expr, eval]
    rw [show values13 (68 : Fin 264) = Real.sqrt (values12 (68 : Fin 154)) by rfl]
    rw [show values12 (68 : Fin 154) = Real.sqrt (values11 (68 : Fin 91)) by rfl]
    rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (524 : Fin 791) = Real.sqrt (values14 (448 : Fin 455)) by rfl]
    simp only [values15_special_523_rightCert, IntervalCert.expr, eval]
    rw [show values14 (448 : Fin 455) = 1 + values12 (147 : Fin 154) by rfl]
    rw [show values12 (147 : Fin 154) = 1 + values10 (47 : Fin 54) by rfl]
    rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_523_leftCert, values15_special_523_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_524_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (22563 / 10000 : Rat) (IntervalCert.add (509 / 100 : Rat) (25453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (8181 / 2000 : Rat) (409051 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3090507 / 1000000 : Rat) (772627 / 250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (20905077 / 10000000 : Rat) (10452539 / 5000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (109050773 / 100000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (118920711 / 100000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_524_rightCert : IntervalCert :=
  IntervalCert.add (1129 / 500 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (62901 / 50000 : Rat) (1259 / 1000 : Rat) (IntervalCert.sqrt (158263 / 100000 : Rat) (1583 / 1000 : Rat) (IntervalCert.add (31309 / 12500 : Rat) (501 / 200 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_524 :
    values15 (524 : Fin 791) < values15 (525 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_524_leftCert values15_special_524_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_524_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_524_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (524 : Fin 791) = Real.sqrt (values14 (448 : Fin 455)) by rfl]
    simp only [values15_special_524_leftCert, IntervalCert.expr, eval]
    rw [show values14 (448 : Fin 455) = 1 + values12 (147 : Fin 154) by rfl]
    rw [show values12 (147 : Fin 154) = 1 + values10 (47 : Fin 54) by rfl]
    rw [show values10 (47 : Fin 54) = 1 + values8 (13 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (525 : Fin 791) = 1 + values13 (69 : Fin 264) by rfl]
    simp only [values15_special_524_rightCert, IntervalCert.expr, eval]
    rw [show values13 (69 : Fin 264) = Real.sqrt (values12 (69 : Fin 154)) by rfl]
    rw [show values12 (69 : Fin 154) = Real.sqrt (values11 (69 : Fin 91)) by rfl]
    rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_524_leftCert, values15_special_524_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_525_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (22581 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (629 / 500 : Rat) (125803 / 100000 : Rat) (IntervalCert.sqrt (7913 / 5000 : Rat) (197829 / 125000 : Rat) (IntervalCert.add (25047 / 10000 : Rat) (1252361 / 500000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values15_special_525_rightCert : IntervalCert :=
  IntervalCert.add (113 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (1071 / 1000 : Rat) (134 / 125 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_525 :
    values15 (525 : Fin 791) < values15 (526 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_525_leftCert values15_special_525_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_525_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_525_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (525 : Fin 791) = 1 + values13 (69 : Fin 264) by rfl]
    simp only [values15_special_525_leftCert, IntervalCert.expr, eval]
    rw [show values13 (69 : Fin 264) = Real.sqrt (values12 (69 : Fin 154)) by rfl]
    rw [show values12 (69 : Fin 154) = Real.sqrt (values11 (69 : Fin 91)) by rfl]
    rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (526 : Fin 791) = values5 (1 : Fin 5) + values9 (4 : Fin 33) by rfl]
    simp only [values15_special_525_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_525_leftCert, values15_special_525_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_526_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2261 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_526_rightCert : IntervalCert :=
  IntervalCert.add (283 / 125 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (12641 / 10000 : Rat) (253 / 200 : Rat) (IntervalCert.sqrt (799 / 500 : Rat) (1599 / 1000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (1277 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_526 :
    values15 (526 : Fin 791) < values15 (527 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_526_leftCert values15_special_526_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_526_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_526_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (526 : Fin 791) = values5 (1 : Fin 5) + values9 (4 : Fin 33) by rfl]
    simp only [values15_special_526_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (527 : Fin 791) = 1 + values13 (70 : Fin 264) by rfl]
    simp only [values15_special_526_rightCert, IntervalCert.expr, eval]
    rw [show values13 (70 : Fin 264) = Real.sqrt (values12 (70 : Fin 154)) by rfl]
    rw [show values12 (70 : Fin 154) = Real.sqrt (values11 (70 : Fin 91)) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_526_leftCert, values15_special_526_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_529_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (22763 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (319 / 250 : Rat) (15953 / 12500 : Rat) (IntervalCert.sqrt (16287 / 10000 : Rat) (162877 / 100000 : Rat) (IntervalCert.add (1658 / 625 : Rat) (26528917 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (165289 / 100000 : Rat) (82644583 / 50000000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (273205081 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (216506351 / 125000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_529_rightCert : IntervalCert :=
  IntervalCert.sqrt (22779 / 10000 : Rat) (100 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (519 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_529 :
    values15 (529 : Fin 791) < values15 (530 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_529_leftCert values15_special_529_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_529_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_529_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (529 : Fin 791) = 1 + values13 (72 : Fin 264) by rfl]
    simp only [values15_special_529_leftCert, IntervalCert.expr, eval]
    rw [show values13 (72 : Fin 264) = Real.sqrt (values12 (72 : Fin 154)) by rfl]
    rw [show values12 (72 : Fin 154) = Real.sqrt (values11 (72 : Fin 91)) by rfl]
    rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (530 : Fin 791) = Real.sqrt (values14 (449 : Fin 455)) by rfl]
    simp only [values15_special_529_rightCert, IntervalCert.expr, eval]
    rw [show values14 (449 : Fin 455) = 1 + values12 (148 : Fin 154) by rfl]
    rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by rfl]
    rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_529_leftCert, values15_special_529_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_530_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1139 / 500 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (518921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (523651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (3986509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

private def values15_special_530_rightCert : IntervalCert :=
  IntervalCert.add (22797 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_530 :
    values15 (530 : Fin 791) < values15 (531 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_530_leftCert values15_special_530_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_530_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_530_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (530 : Fin 791) = Real.sqrt (values14 (449 : Fin 455)) by rfl]
    simp only [values15_special_530_leftCert, IntervalCert.expr, eval]
    rw [show values14 (449 : Fin 455) = 1 + values12 (148 : Fin 154) by rfl]
    rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by rfl]
    rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (531 : Fin 791) = values5 (1 : Fin 5) + values9 (5 : Fin 33) by rfl]
    simp only [values15_special_530_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_530_leftCert, values15_special_530_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_531_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))))

private def values15_special_531_rightCert : IntervalCert :=
  IntervalCert.add (457 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (643 / 500 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_531 :
    values15 (531 : Fin 791) < values15 (532 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_531_leftCert values15_special_531_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_531_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_531_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (531 : Fin 791) = values5 (1 : Fin 5) + values9 (5 : Fin 33) by rfl]
    simp only [values15_special_531_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (532 : Fin 791) = 1 + values13 (73 : Fin 264) by rfl]
    simp only [values15_special_531_rightCert, IntervalCert.expr, eval]
    rw [show values13 (73 : Fin 264) = Real.sqrt (values12 (73 : Fin 154)) by rfl]
    rw [show values12 (73 : Fin 154) = Real.sqrt (values11 (73 : Fin 91)) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_531_leftCert, values15_special_531_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_534_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (23 / 10 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1299 / 1000 : Rat) (12991 / 10000 : Rat) (IntervalCert.sqrt (27 / 16 : Rat) (4219 / 2500 : Rat) (IntervalCert.add (28477 / 10000 : Rat) (14239 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7391 / 4000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (17071 / 5000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_534_rightCert : IntervalCert :=
  IntervalCert.add (461 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2791 / 2500 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_534 :
    values15 (534 : Fin 791) < values15 (535 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_534_leftCert values15_special_534_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_534_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_534_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (534 : Fin 791) = 1 + values13 (75 : Fin 264) by rfl]
    simp only [values15_special_534_leftCert, IntervalCert.expr, eval]
    rw [show values13 (75 : Fin 264) = Real.sqrt (values12 (75 : Fin 154)) by rfl]
    rw [show values12 (75 : Fin 154) = Real.sqrt (values11 (75 : Fin 91)) by rfl]
    rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (535 : Fin 791) = values5 (1 : Fin 5) + values9 (6 : Fin 33) by rfl]
    simp only [values15_special_534_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_534_leftCert, values15_special_534_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_535_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1153 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (279 / 250 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_535_rightCert : IntervalCert :=
  IntervalCert.add (579 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_535 :
    values15 (535 : Fin 791) < values15 (536 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_535_leftCert values15_special_535_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_535_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_535_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (535 : Fin 791) = values5 (1 : Fin 5) + values9 (6 : Fin 33) by rfl]
    simp only [values15_special_535_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (536 : Fin 791) = 1 + values13 (76 : Fin 264) by rfl]
    simp only [values15_special_535_rightCert, IntervalCert.expr, eval]
    rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
    rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_535_leftCert, values15_special_535_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_538_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1163 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (53 / 40 : Rat) (13259 / 10000 : Rat) (IntervalCert.sqrt (1757 / 1000 : Rat) (879 / 500 : Rat) (IntervalCert.add (309 / 100 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (4181 / 2000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_538_rightCert : IntervalCert :=
  IntervalCert.sqrt (5817 / 2500 : Rat) (100 : Rat) (IntervalCert.add (2707 / 500 : Rat) (1083 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_538 :
    values15 (538 : Fin 791) < values15 (539 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_538_leftCert values15_special_538_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_538_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_538_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (538 : Fin 791) = 1 + values13 (78 : Fin 264) by rfl]
    simp only [values15_special_538_leftCert, IntervalCert.expr, eval]
    rw [show values13 (78 : Fin 264) = Real.sqrt (values12 (78 : Fin 154)) by rfl]
    rw [show values12 (78 : Fin 154) = Real.sqrt (values11 (78 : Fin 91)) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (539 : Fin 791) = Real.sqrt (values14 (450 : Fin 455)) by rfl]
    simp only [values15_special_538_rightCert, IntervalCert.expr, eval]
    rw [show values14 (450 : Fin 455) = 1 + values12 (149 : Fin 154) by rfl]
    rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by rfl]
    rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_538_leftCert, values15_special_538_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_539_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2327 / 1000 : Rat) (IntervalCert.add (2707 / 500 : Rat) (54143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (220711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_539_rightCert : IntervalCert :=
  IntervalCert.add (2331 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (6659 / 5000 : Rat) (333 / 250 : Rat) (IntervalCert.sqrt (17737 / 10000 : Rat) (887 / 500 : Rat) (IntervalCert.add (15731 / 5000 : Rat) (3147 / 1000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_539 :
    values15 (539 : Fin 791) < values15 (540 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_539_leftCert values15_special_539_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_539_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_539_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (539 : Fin 791) = Real.sqrt (values14 (450 : Fin 455)) by rfl]
    simp only [values15_special_539_leftCert, IntervalCert.expr, eval]
    rw [show values14 (450 : Fin 455) = 1 + values12 (149 : Fin 154) by rfl]
    rw [show values12 (149 : Fin 154) = 1 + values10 (49 : Fin 54) by rfl]
    rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (540 : Fin 791) = 1 + values13 (79 : Fin 264) by rfl]
    simp only [values15_special_539_rightCert, IntervalCert.expr, eval]
    rw [show values13 (79 : Fin 264) = Real.sqrt (values12 (79 : Fin 154)) by rfl]
    rw [show values12 (79 : Fin 154) = Real.sqrt (values11 (79 : Fin 91)) by rfl]
    rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_539_leftCert, values15_special_539_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_541_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (58409 / 25000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (167 / 125 : Rat) (41761 / 31250 : Rat) (IntervalCert.sqrt (357 / 200 : Rat) (446459 / 250000 : Rat) (IntervalCert.add (3189 / 1000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (5473 / 2500 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_541_rightCert : IntervalCert :=
  IntervalCert.add (5841 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_541 :
    values15 (541 : Fin 791) < values15 (542 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_541_leftCert values15_special_541_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_541_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_541_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (541 : Fin 791) = 1 + values13 (80 : Fin 264) by rfl]
    simp only [values15_special_541_leftCert, IntervalCert.expr, eval]
    rw [show values13 (80 : Fin 264) = Real.sqrt (values12 (80 : Fin 154)) by rfl]
    rw [show values12 (80 : Fin 154) = Real.sqrt (values11 (80 : Fin 91)) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (542 : Fin 791) = values5 (1 : Fin 5) + values9 (7 : Fin 33) by rfl]
    simp only [values15_special_541_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_541_leftCert, values15_special_541_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_542_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4673 / 2000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1147 / 1000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_542_rightCert : IntervalCert :=
  IntervalCert.add (2337 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (155813 / 125000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (777 / 500 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_542 :
    values15 (542 : Fin 791) < values15 (543 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_542_leftCert values15_special_542_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_542_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_542_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (542 : Fin 791) = values5 (1 : Fin 5) + values9 (7 : Fin 33) by rfl]
    simp only [values15_special_542_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (543 : Fin 791) = values6 (1 : Fin 8) + values8 (6 : Fin 20) by rfl]
    simp only [values15_special_542_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_542_leftCert, values15_special_542_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_543_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1169 / 500 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (623 / 500 : Rat) (6233 / 5000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_543_rightCert : IntervalCert :=
  IntervalCert.add (2349 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (6747 / 5000 : Rat) (27 / 20 : Rat) (IntervalCert.sqrt (1821 / 1000 : Rat) (911 / 500 : Rat) (IntervalCert.add (331607 / 100000 : Rat) (3317 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_543 :
    values15 (543 : Fin 791) < values15 (544 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_543_leftCert values15_special_543_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_543_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_543_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (543 : Fin 791) = values6 (1 : Fin 8) + values8 (6 : Fin 20) by rfl]
    simp only [values15_special_543_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (544 : Fin 791) = 1 + values13 (81 : Fin 264) by rfl]
    simp only [values15_special_543_rightCert, IntervalCert.expr, eval]
    rw [show values13 (81 : Fin 264) = Real.sqrt (values12 (81 : Fin 154)) by rfl]
    rw [show values12 (81 : Fin 154) = Real.sqrt (values11 (81 : Fin 91)) by rfl]
    rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_543_leftCert, values15_special_543_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_545_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (11797 / 5000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_545_rightCert : IntervalCert :=
  IntervalCert.add (23603 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_545 :
    values15 (545 : Fin 791) < values15 (546 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_545_leftCert values15_special_545_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_545_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_545_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (545 : Fin 791) = 1 + values13 (82 : Fin 264) by rfl]
    simp only [values15_special_545_leftCert, IntervalCert.expr, eval]
    rw [show values13 (82 : Fin 264) = Real.sqrt (values12 (82 : Fin 154)) by rfl]
    rw [show values12 (82 : Fin 154) = Real.sqrt (values11 (82 : Fin 91)) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (546 : Fin 791) = values7 (1 : Fin 13) + values7 (4 : Fin 13) by rfl]
    simp only [values15_special_545_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_545_leftCert, values15_special_545_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_546_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2361 / 1000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values15_special_546_rightCert : IntervalCert :=
  IntervalCert.add (2373 / 1000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (686503 / 500000 : Rat) (687 / 500 : Rat) (IntervalCert.sqrt (147277 / 78125 : Rat) (943 / 500 : Rat) (IntervalCert.add (355377397 / 100000000 : Rat) (1777 / 500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1276886987 / 500000000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377397403 / 100000000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213562373 / 1000000000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999999999 / 100000000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421356237309 / 100000000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999999999999 / 100000000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999999999999 / 1000000000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999999999999 / 1000000000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_546 :
    values15 (546 : Fin 791) < values15 (547 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_546_leftCert values15_special_546_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_546_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_546_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (546 : Fin 791) = values7 (1 : Fin 13) + values7 (4 : Fin 13) by rfl]
    simp only [values15_special_546_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (547 : Fin 791) = 1 + values13 (83 : Fin 264) by rfl]
    simp only [values15_special_546_rightCert, IntervalCert.expr, eval]
    rw [show values13 (83 : Fin 264) = Real.sqrt (values12 (83 : Fin 154)) by rfl]
    rw [show values12 (83 : Fin 154) = Real.sqrt (values11 (83 : Fin 91)) by rfl]
    rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_546_leftCert, values15_special_546_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_547_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1187 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1373 / 1000 : Rat) (13731 / 10000 : Rat) (IntervalCert.sqrt (94257 / 50000 : Rat) (4713 / 2500 : Rat) (IntervalCert.add (355377 / 100000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2553773 / 1000000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (15537739 / 10000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (4828427 / 2000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_547_rightCert : IntervalCert :=
  IntervalCert.add (1189 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_547 :
    values15 (547 : Fin 791) < values15 (548 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_547_leftCert values15_special_547_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_547_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_547_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (547 : Fin 791) = 1 + values13 (83 : Fin 264) by rfl]
    simp only [values15_special_547_leftCert, IntervalCert.expr, eval]
    rw [show values13 (83 : Fin 264) = Real.sqrt (values12 (83 : Fin 154)) by rfl]
    rw [show values12 (83 : Fin 154) = Real.sqrt (values11 (83 : Fin 91)) by rfl]
    rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (548 : Fin 791) = values5 (1 : Fin 5) + values9 (8 : Fin 33) by rfl]
    simp only [values15_special_547_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_547_leftCert, values15_special_547_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_548_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2379 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))))

private def values15_special_548_rightCert : IntervalCert :=
  IntervalCert.add (2389 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13899 / 10000 : Rat) (139 / 100 : Rat) (IntervalCert.sqrt (38637 / 20000 : Rat) (483 / 250 : Rat) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_548 :
    values15 (548 : Fin 791) < values15 (549 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_548_leftCert values15_special_548_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_548_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_548_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (548 : Fin 791) = values5 (1 : Fin 5) + values9 (8 : Fin 33) by rfl]
    simp only [values15_special_548_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (549 : Fin 791) = 1 + values13 (84 : Fin 264) by rfl]
    simp only [values15_special_548_rightCert, IntervalCert.expr, eval]
    rw [show values13 (84 : Fin 264) = Real.sqrt (values12 (84 : Fin 154)) by rfl]
    rw [show values12 (84 : Fin 154) = Real.sqrt (values11 (84 : Fin 91)) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_548_leftCert, values15_special_548_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_549_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (239 / 100 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1389 / 1000 : Rat) (8687 / 6250 : Rat) (IntervalCert.sqrt (1931 / 1000 : Rat) (96593 / 50000 : Rat) (IntervalCert.add (933 / 250 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_549_rightCert : IntervalCert :=
  IntervalCert.sqrt (1197 / 500 : Rat) (100 : Rat) (IntervalCert.add (1433 / 250 : Rat) (5733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (94641 / 20000 : Rat) (47321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (9330127 / 2500000 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2732050807 / 1000000000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (692820323 / 400000000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (29999999999 / 10000000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (199999999999 / 100000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (999999999999 / 1000000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (999999999999 / 1000000000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_549 :
    values15 (549 : Fin 791) < values15 (550 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_549_leftCert values15_special_549_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_549_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_549_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (549 : Fin 791) = 1 + values13 (84 : Fin 264) by rfl]
    simp only [values15_special_549_leftCert, IntervalCert.expr, eval]
    rw [show values13 (84 : Fin 264) = Real.sqrt (values12 (84 : Fin 154)) by rfl]
    rw [show values12 (84 : Fin 154) = Real.sqrt (values11 (84 : Fin 91)) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (550 : Fin 791) = Real.sqrt (values14 (451 : Fin 455)) by rfl]
    simp only [values15_special_549_rightCert, IntervalCert.expr, eval]
    rw [show values14 (451 : Fin 455) = 1 + values12 (150 : Fin 154) by rfl]
    rw [show values12 (150 : Fin 154) = 1 + values10 (50 : Fin 54) by rfl]
    rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_549_leftCert, values15_special_549_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_550_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (479 / 200 : Rat) (IntervalCert.add (1433 / 250 : Rat) (5733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (94641 / 20000 : Rat) (47321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (9330127 / 2500000 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2732050807 / 1000000000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (692820323 / 400000000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (29999999999 / 10000000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (199999999999 / 100000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (999999999999 / 1000000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (999999999999 / 1000000000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

private def values15_special_550_rightCert : IntervalCert :=
  IntervalCert.add (1199 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13987 / 10000 : Rat) (1399 / 1000 : Rat) (IntervalCert.sqrt (9783 / 5000 : Rat) (1957 / 1000 : Rat) (IntervalCert.add (9571 / 2500 : Rat) (3829 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (5657 / 2000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_550 :
    values15 (550 : Fin 791) < values15 (551 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_550_leftCert values15_special_550_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_550_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_550_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (550 : Fin 791) = Real.sqrt (values14 (451 : Fin 455)) by rfl]
    simp only [values15_special_550_leftCert, IntervalCert.expr, eval]
    rw [show values14 (451 : Fin 455) = 1 + values12 (150 : Fin 154) by rfl]
    rw [show values12 (150 : Fin 154) = 1 + values10 (50 : Fin 54) by rfl]
    rw [show values10 (50 : Fin 54) = 1 + values8 (16 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (551 : Fin 791) = 1 + values13 (85 : Fin 264) by rfl]
    simp only [values15_special_550_rightCert, IntervalCert.expr, eval]
    rw [show values13 (85 : Fin 264) = Real.sqrt (values12 (85 : Fin 154)) by rfl]
    rw [show values12 (85 : Fin 154) = Real.sqrt (values11 (85 : Fin 91)) by rfl]
    rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_550_leftCert, values15_special_550_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_551_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2399 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (699 / 500 : Rat) (3497 / 2500 : Rat) (IntervalCert.sqrt (489 / 250 : Rat) (12229 / 6250 : Rat) (IntervalCert.add (957 / 250 : Rat) (382843 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (7071 / 2500 : Rat) (707107 / 250000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))

private def values15_special_551_rightCert : IntervalCert :=
  IntervalCert.add (481 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_551 :
    values15 (551 : Fin 791) < values15 (552 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_551_leftCert values15_special_551_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_551_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_551_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (551 : Fin 791) = 1 + values13 (85 : Fin 264) by rfl]
    simp only [values15_special_551_leftCert, IntervalCert.expr, eval]
    rw [show values13 (85 : Fin 264) = Real.sqrt (values12 (85 : Fin 154)) by rfl]
    rw [show values12 (85 : Fin 154) = Real.sqrt (values11 (85 : Fin 91)) by rfl]
    rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (552 : Fin 791) = values5 (1 : Fin 5) + values9 (9 : Fin 33) by rfl]
    simp only [values15_special_551_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_551_leftCert, values15_special_551_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_552_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3007 / 1250 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (152 / 125 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (1479 / 1000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values15_special_552_rightCert : IntervalCert :=
  IntervalCert.add (4813 / 2000 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_552 :
    values15 (552 : Fin 791) < values15 (553 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_552_leftCert values15_special_552_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_552_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_552_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (552 : Fin 791) = values5 (1 : Fin 5) + values9 (9 : Fin 33) by rfl]
    simp only [values15_special_552_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (553 : Fin 791) = values6 (1 : Fin 8) + values8 (7 : Fin 20) by rfl]
    simp only [values15_special_552_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_552_leftCert, values15_special_552_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_553_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2407 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_553_rightCert : IntervalCert :=
  IntervalCert.add (1207 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_553 :
    values15 (553 : Fin 791) < values15 (554 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_553_leftCert values15_special_553_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_553_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_553_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (553 : Fin 791) = values6 (1 : Fin 8) + values8 (7 : Fin 20) by rfl]
    simp only [values15_special_553_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (554 : Fin 791) = 1 + values13 (86 : Fin 264) by rfl]
    simp only [values15_special_553_rightCert, IntervalCert.expr, eval]
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_553_leftCert, values15_special_553_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_556_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (24181 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (709 / 500 : Rat) (70903 / 50000 : Rat) (IntervalCert.add (5027 / 2500 : Rat) (201089 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (3159 / 3125 : Rat) (10108893 / 10000000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (20437943 / 20000000 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (1044273783 / 1000000000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1090507733 / 1000000000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (11892071151 / 10000000000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767766953 / 1250000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat))))))))))))

private def values15_special_556_rightCert : IntervalCert :=
  IntervalCert.add (6049 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (50271 / 50000 : Rat) (503 / 500 : Rat) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_556 :
    values15 (556 : Fin 791) < values15 (557 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_556_leftCert values15_special_556_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_556_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_556_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (556 : Fin 791) = 1 + values13 (88 : Fin 264) by rfl]
    simp only [values15_special_556_leftCert, IntervalCert.expr, eval]
    rw [show values13 (88 : Fin 264) = Real.sqrt (values12 (88 : Fin 154)) by rfl]
    rw [show values12 (88 : Fin 154) = 1 + values10 (2 : Fin 54) by rfl]
    rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (557 : Fin 791) = Real.sqrt 2 + values10 (1 : Fin 54) by rfl]
    simp only [values15_special_556_rightCert, IntervalCert.expr, eval]
    rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_556_leftCert, values15_special_556_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_557_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (121 / 50 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (201 / 200 : Rat) (2011 / 2000 : Rat) (IntervalCert.sqrt (2527 / 2500 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (5109 / 5000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values15_special_557_rightCert : IntervalCert :=
  IntervalCert.add (24219 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (142193 / 100000 : Rat) (711 / 500 : Rat) (IntervalCert.add (202189 / 100000 : Rat) (1011 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1021897 / 1000000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_557 :
    values15 (557 : Fin 791) < values15 (558 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_557_leftCert values15_special_557_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_557_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_557_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (557 : Fin 791) = Real.sqrt 2 + values10 (1 : Fin 54) by rfl]
    simp only [values15_special_557_leftCert, IntervalCert.expr, eval]
    rw [show values10 (1 : Fin 54) = Real.sqrt (values9 (1 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (558 : Fin 791) = 1 + values13 (89 : Fin 264) by rfl]
    simp only [values15_special_557_rightCert, IntervalCert.expr, eval]
    rw [show values13 (89 : Fin 264) = Real.sqrt (values12 (89 : Fin 154)) by rfl]
    rw [show values12 (89 : Fin 154) = 1 + values10 (3 : Fin 54) by rfl]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_557_leftCert, values15_special_557_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_558_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1211 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1421 / 1000 : Rat) (71097 / 50000 : Rat) (IntervalCert.add (2021 / 1000 : Rat) (20219 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (5109 / 5000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))))))

private def values15_special_558_rightCert : IntervalCert :=
  IntervalCert.add (97 / 40 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_558 :
    values15 (558 : Fin 791) < values15 (559 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_558_leftCert values15_special_558_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_558_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_558_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (558 : Fin 791) = 1 + values13 (89 : Fin 264) by rfl]
    simp only [values15_special_558_leftCert, IntervalCert.expr, eval]
    rw [show values13 (89 : Fin 264) = Real.sqrt (values12 (89 : Fin 154)) by rfl]
    rw [show values12 (89 : Fin 154) = 1 + values10 (3 : Fin 54) by rfl]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (559 : Fin 791) = Real.sqrt 2 + values10 (2 : Fin 54) by rfl]
    simp only [values15_special_558_rightCert, IntervalCert.expr, eval]
    rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_558_leftCert, values15_special_558_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_559_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (6063 / 2500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (101 / 100 : Rat) (10109 / 10000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values15_special_559_rightCert : IntervalCert :=
  IntervalCert.add (4853 / 2000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (356627 / 250000 : Rat) (1427 / 1000 : Rat) (IntervalCert.add (2034927 / 1000000 : Rat) (407 / 200 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10349277 / 10000000 : Rat) (103493 / 100000 : Rat) (IntervalCert.sqrt (5355377 / 5000000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (5736013 / 5000000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_559 :
    values15 (559 : Fin 791) < values15 (560 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_559_leftCert values15_special_559_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_559_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_559_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (559 : Fin 791) = Real.sqrt 2 + values10 (2 : Fin 54) by rfl]
    simp only [values15_special_559_leftCert, IntervalCert.expr, eval]
    rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (560 : Fin 791) = 1 + values13 (90 : Fin 264) by rfl]
    simp only [values15_special_559_rightCert, IntervalCert.expr, eval]
    rw [show values13 (90 : Fin 264) = Real.sqrt (values12 (90 : Fin 154)) by rfl]
    rw [show values12 (90 : Fin 154) = 1 + values10 (4 : Fin 54) by rfl]
    rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_559_leftCert, values15_special_559_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_563_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (24341 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (717 / 500 : Rat) (89631 / 62500 : Rat) (IntervalCert.add (10283 / 5000 : Rat) (205663133 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (105663 / 100000 : Rat) (528315661 / 500000000 : Rat) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (11164697501 / 10000000000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (3116261757 / 2500000000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (15537739741 / 10000000000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (3017766953 / 1250000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70710678119 / 50000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)))))))))))

private def values15_special_563_rightCert : IntervalCert :=
  IntervalCert.add (24357 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (155813 / 125000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (777 / 500 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_563 :
    values15 (563 : Fin 791) < values15 (564 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_563_leftCert values15_special_563_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_563_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_563_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (563 : Fin 791) = 1 + values13 (93 : Fin 264) by rfl]
    simp only [values15_special_563_leftCert, IntervalCert.expr, eval]
    rw [show values13 (93 : Fin 264) = Real.sqrt (values12 (93 : Fin 154)) by rfl]
    rw [show values12 (93 : Fin 154) = 1 + values10 (6 : Fin 54) by rfl]
    rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (564 : Fin 791) = values5 (1 : Fin 5) + values9 (10 : Fin 33) by rfl]
    simp only [values15_special_563_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_563_leftCert, values15_special_563_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_564_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (12179 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_564_rightCert : IntervalCert :=
  IntervalCert.add (609 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_564 :
    values15 (564 : Fin 791) < values15 (565 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_564_leftCert values15_special_564_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_564_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_564_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (564 : Fin 791) = values5 (1 : Fin 5) + values9 (10 : Fin 33) by rfl]
    simp only [values15_special_564_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (565 : Fin 791) = Real.sqrt 2 + values10 (3 : Fin 54) by rfl]
    simp only [values15_special_564_rightCert, IntervalCert.expr, eval]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_564_leftCert, values15_special_564_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_565_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2437 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values15_special_565_rightCert : IntervalCert :=
  IntervalCert.add (2439 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14391 / 10000 : Rat) (36 / 25 : Rat) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_565 :
    values15 (565 : Fin 791) < values15 (566 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_565_leftCert values15_special_565_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_565_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_565_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (565 : Fin 791) = Real.sqrt 2 + values10 (3 : Fin 54) by rfl]
    simp only [values15_special_565_leftCert, IntervalCert.expr, eval]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (566 : Fin 791) = 1 + values13 (94 : Fin 264) by rfl]
    simp only [values15_special_565_rightCert, IntervalCert.expr, eval]
    rw [show values13 (94 : Fin 264) = Real.sqrt (values12 (94 : Fin 154)) by rfl]
    rw [show values12 (94 : Fin 154) = 1 + values10 (7 : Fin 54) by rfl]
    rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_565_leftCert, values15_special_565_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_567_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1223 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (289 / 200 : Rat) (14459 / 10000 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values15_special_567_rightCert : IntervalCert :=
  IntervalCert.add (2449 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (10349 / 10000 : Rat) (207 / 200 : Rat) (IntervalCert.sqrt (107107 / 100000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_567 :
    values15 (567 : Fin 791) < values15 (568 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_567_leftCert values15_special_567_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_567_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_567_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (567 : Fin 791) = 1 + values13 (95 : Fin 264) by rfl]
    simp only [values15_special_567_leftCert, IntervalCert.expr, eval]
    rw [show values13 (95 : Fin 264) = Real.sqrt (values12 (95 : Fin 154)) by rfl]
    rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (568 : Fin 791) = Real.sqrt 2 + values10 (4 : Fin 54) by rfl]
    simp only [values15_special_567_rightCert, IntervalCert.expr, eval]
    rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_567_leftCert, values15_special_567_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_568_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (6123 / 2500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (517 / 500 : Rat) (103493 / 100000 : Rat) (IntervalCert.sqrt (1071 / 1000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_568_rightCert : IntervalCert :=
  IntervalCert.add (12247 / 5000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (36237 / 25000 : Rat) (29 / 20 : Rat) (IntervalCert.sqrt (2101 / 1000 : Rat) (1051 / 500 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (883 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_568 :
    values15 (568 : Fin 791) < values15 (569 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_568_leftCert values15_special_568_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_568_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_568_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (568 : Fin 791) = Real.sqrt 2 + values10 (4 : Fin 54) by rfl]
    simp only [values15_special_568_leftCert, IntervalCert.expr, eval]
    rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (569 : Fin 791) = 1 + values13 (96 : Fin 264) by rfl]
    simp only [values15_special_568_rightCert, IntervalCert.expr, eval]
    rw [show values13 (96 : Fin 264) = Real.sqrt (values12 (96 : Fin 154)) by rfl]
    rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_568_leftCert, values15_special_568_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_569_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (612371 / 250000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1449 / 1000 : Rat) (14494837 / 10000000 : Rat) (IntervalCert.sqrt (2101 / 1000 : Rat) (210100299 / 100000000 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (4414213563 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (4267766953 / 1250000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120710678119 / 50000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707106781187 / 500000000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000000000001 / 1000000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat))))))))))

private def values15_special_569_rightCert : IntervalCert :=
  IntervalCert.sqrt (2449489 / 1000000 : Rat) (100 : Rat) (IntervalCert.add (5999999 / 1000000 : Rat) (6001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (49999999 / 10000000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999999 / 100000000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999999 / 1000000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_569 :
    values15 (569 : Fin 791) < values15 (570 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_569_leftCert values15_special_569_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_569_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_569_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (569 : Fin 791) = 1 + values13 (96 : Fin 264) by rfl]
    simp only [values15_special_569_leftCert, IntervalCert.expr, eval]
    rw [show values13 (96 : Fin 264) = Real.sqrt (values12 (96 : Fin 154)) by rfl]
    rw [show values12 (96 : Fin 154) = Real.sqrt (values11 (88 : Fin 91)) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (570 : Fin 791) = Real.sqrt (values14 (452 : Fin 455)) by rfl]
    simp only [values15_special_569_rightCert, IntervalCert.expr, eval]
    rw [show values14 (452 : Fin 455) = 1 + values12 (151 : Fin 154) by rfl]
    rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_569_leftCert, values15_special_569_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_570_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (4899 / 2000 : Rat) (IntervalCert.add (5999 / 1000 : Rat) (600001 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (49999 / 10000 : Rat) (5000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

private def values15_special_570_rightCert : IntervalCert :=
  IntervalCert.add (49 / 20 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14501 / 10000 : Rat) (1451 / 1000 : Rat) (IntervalCert.add (5257 / 2500 : Rat) (2103 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (110289 / 100000 : Rat) (11029 / 10000 : Rat) (IntervalCert.sqrt (60819 / 50000 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_570 :
    values15 (570 : Fin 791) < values15 (571 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_570_leftCert values15_special_570_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_570_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_570_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (570 : Fin 791) = Real.sqrt (values14 (452 : Fin 455)) by rfl]
    simp only [values15_special_570_leftCert, IntervalCert.expr, eval]
    rw [show values14 (452 : Fin 455) = 1 + values12 (151 : Fin 154) by rfl]
    rw [show values12 (151 : Fin 154) = 1 + values10 (51 : Fin 54) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (571 : Fin 791) = 1 + values13 (97 : Fin 264) by rfl]
    simp only [values15_special_570_rightCert, IntervalCert.expr, eval]
    rw [show values13 (97 : Fin 264) = Real.sqrt (values12 (97 : Fin 154)) by rfl]
    rw [show values12 (97 : Fin 154) = 1 + values10 (9 : Fin 54) by rfl]
    rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_570_leftCert, values15_special_570_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_572_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (491 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (727 / 500 : Rat) (145481 / 100000 : Rat) (IntervalCert.add (529 / 250 : Rat) (211647 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (5582349 / 5000000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1558131 / 1250000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_572_rightCert : IntervalCert :=
  IntervalCert.add (1229 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_572 :
    values15 (572 : Fin 791) < values15 (573 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_572_leftCert values15_special_572_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_572_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_572_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (572 : Fin 791) = 1 + values13 (98 : Fin 264) by rfl]
    simp only [values15_special_572_leftCert, IntervalCert.expr, eval]
    rw [show values13 (98 : Fin 264) = Real.sqrt (values12 (98 : Fin 154)) by rfl]
    rw [show values12 (98 : Fin 154) = 1 + values10 (10 : Fin 54) by rfl]
    rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (573 : Fin 791) = Real.sqrt 2 + values10 (5 : Fin 54) by rfl]
    simp only [values15_special_572_rightCert, IntervalCert.expr, eval]
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_572_leftCert, values15_special_572_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_573_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2459 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values15_special_573_rightCert : IntervalCert :=
  IntervalCert.add (493 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14653 / 10000 : Rat) (733 / 500 : Rat) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_573 :
    values15 (573 : Fin 791) < values15 (574 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_573_leftCert values15_special_573_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_573_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_573_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (573 : Fin 791) = Real.sqrt 2 + values10 (5 : Fin 54) by rfl]
    simp only [values15_special_573_leftCert, IntervalCert.expr, eval]
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (574 : Fin 791) = 1 + values13 (99 : Fin 264) by rfl]
    simp only [values15_special_573_rightCert, IntervalCert.expr, eval]
    rw [show values13 (99 : Fin 264) = Real.sqrt (values12 (99 : Fin 154)) by rfl]
    rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by rfl]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_573_leftCert, values15_special_573_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_574_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1233 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (293 / 200 : Rat) (7327 / 5000 : Rat) (IntervalCert.add (2147 / 1000 : Rat) (21473 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_574_rightCert : IntervalCert :=
  IntervalCert.add (247 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (5283 / 5000 : Rat) (1057 / 1000 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_574 :
    values15 (574 : Fin 791) < values15 (575 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_574_leftCert values15_special_574_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_574_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_574_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (574 : Fin 791) = 1 + values13 (99 : Fin 264) by rfl]
    simp only [values15_special_574_leftCert, IntervalCert.expr, eval]
    rw [show values13 (99 : Fin 264) = Real.sqrt (values12 (99 : Fin 154)) by rfl]
    rw [show values12 (99 : Fin 154) = 1 + values10 (11 : Fin 54) by rfl]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (575 : Fin 791) = Real.sqrt 2 + values10 (6 : Fin 54) by rfl]
    simp only [values15_special_574_rightCert, IntervalCert.expr, eval]
    rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_574_leftCert, values15_special_574_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_575_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2471 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (132 / 125 : Rat) (3302 / 3125 : Rat) (IntervalCert.sqrt (279 / 250 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_575_rightCert : IntervalCert :=
  IntervalCert.add (2479 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_575 :
    values15 (575 : Fin 791) < values15 (576 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_575_leftCert values15_special_575_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_575_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_575_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (575 : Fin 791) = Real.sqrt 2 + values10 (6 : Fin 54) by rfl]
    simp only [values15_special_575_leftCert, IntervalCert.expr, eval]
    rw [show values10 (6 : Fin 54) = Real.sqrt (values9 (6 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (576 : Fin 791) = 1 + values13 (100 : Fin 264) by rfl]
    simp only [values15_special_575_rightCert, IntervalCert.expr, eval]
    rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
    rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_575_leftCert, values15_special_575_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_577_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (24841 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (371 / 250 : Rat) (148407 / 100000 : Rat) (IntervalCert.add (2753 / 1250 : Rat) (55061 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (120243 / 100000 : Rat) (1202439 / 1000000 : Rat) (IntervalCert.sqrt (28917 / 20000 : Rat) (1445859 / 1000000 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_577_rightCert : IntervalCert :=
  IntervalCert.add (497 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (134 / 125 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_577 :
    values15 (577 : Fin 791) < values15 (578 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_577_leftCert values15_special_577_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_577_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_577_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (577 : Fin 791) = 1 + values13 (101 : Fin 264) by rfl]
    simp only [values15_special_577_leftCert, IntervalCert.expr, eval]
    rw [show values13 (101 : Fin 264) = Real.sqrt (values12 (101 : Fin 154)) by rfl]
    rw [show values12 (101 : Fin 154) = 1 + values10 (13 : Fin 54) by rfl]
    rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (578 : Fin 791) = Real.sqrt 2 + values10 (7 : Fin 54) by rfl]
    simp only [values15_special_577_rightCert, IntervalCert.expr, eval]
    rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_577_leftCert, values15_special_577_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_578_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1243 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_578_rightCert : IntervalCert :=
  IntervalCert.add (311 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14887 / 10000 : Rat) (1489 / 1000 : Rat) (IntervalCert.add (22163 / 10000 : Rat) (2217 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_578 :
    values15 (578 : Fin 791) < values15 (579 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_578_leftCert values15_special_578_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_578_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_578_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (578 : Fin 791) = Real.sqrt 2 + values10 (7 : Fin 54) by rfl]
    simp only [values15_special_578_leftCert, IntervalCert.expr, eval]
    rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (579 : Fin 791) = 1 + values13 (102 : Fin 264) by rfl]
    simp only [values15_special_578_rightCert, IntervalCert.expr, eval]
    rw [show values13 (102 : Fin 264) = Real.sqrt (values12 (102 : Fin 154)) by rfl]
    rw [show values12 (102 : Fin 154) = 1 + values10 (14 : Fin 54) by rfl]
    rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_578_leftCert, values15_special_578_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_581_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2499 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (749 / 500 : Rat) (37471 / 25000 : Rat) (IntervalCert.add (1123 / 500 : Rat) (224651 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_581_rightCert : IntervalCert :=
  IntervalCert.add (313 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_581 :
    values15 (581 : Fin 791) < values15 (582 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_581_leftCert values15_special_581_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_581_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_581_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (581 : Fin 791) = 1 + values13 (104 : Fin 264) by rfl]
    simp only [values15_special_581_leftCert, IntervalCert.expr, eval]
    rw [show values13 (104 : Fin 264) = Real.sqrt (values12 (104 : Fin 154)) by rfl]
    rw [show values12 (104 : Fin 154) = 1 + values10 (15 : Fin 54) by rfl]
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (582 : Fin 791) = Real.sqrt 2 + values10 (8 : Fin 54) by rfl]
    simp only [values15_special_581_rightCert, IntervalCert.expr, eval]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_581_leftCert, values15_special_581_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_582_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3131 / 1250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values15_special_582_rightCert : IntervalCert :=
  IntervalCert.add (6263 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_582 :
    values15 (582 : Fin 791) < values15 (583 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_582_leftCert values15_special_582_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_582_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_582_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (582 : Fin 791) = Real.sqrt 2 + values10 (8 : Fin 54) by rfl]
    simp only [values15_special_582_leftCert, IntervalCert.expr, eval]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (583 : Fin 791) = values5 (1 : Fin 5) + values9 (11 : Fin 33) by rfl]
    simp only [values15_special_582_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_582_leftCert, values15_special_582_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_583_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1253 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_583_rightCert : IntervalCert :=
  IntervalCert.add (2509 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7549 / 5000 : Rat) (151 / 100 : Rat) (IntervalCert.add (22797 / 10000 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_583 :
    values15 (583 : Fin 791) < values15 (584 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_583_leftCert values15_special_583_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_583_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_583_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (583 : Fin 791) = values5 (1 : Fin 5) + values9 (11 : Fin 33) by rfl]
    simp only [values15_special_583_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (584 : Fin 791) = 1 + values13 (105 : Fin 264) by rfl]
    simp only [values15_special_583_rightCert, IntervalCert.expr, eval]
    rw [show values13 (105 : Fin 264) = Real.sqrt (values12 (105 : Fin 154)) by rfl]
    rw [show values12 (105 : Fin 154) = values5 (1 : Fin 5) + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_583_leftCert, values15_special_583_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_585_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (314 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1511 / 1000 : Rat) (9449 / 6250 : Rat) (IntervalCert.add (457 / 200 : Rat) (45713 / 20000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (3214121 / 2500000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (16528917 / 10000000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27320509 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_585_rightCert : IntervalCert :=
  IntervalCert.add (2517 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (110289 / 100000 : Rat) (1103 / 1000 : Rat) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_585 :
    values15 (585 : Fin 791) < values15 (586 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_585_leftCert values15_special_585_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_585_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_585_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (585 : Fin 791) = 1 + values13 (106 : Fin 264) by rfl]
    simp only [values15_special_585_leftCert, IntervalCert.expr, eval]
    rw [show values13 (106 : Fin 264) = Real.sqrt (values12 (106 : Fin 154)) by rfl]
    rw [show values12 (106 : Fin 154) = 1 + values10 (16 : Fin 54) by rfl]
    rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (586 : Fin 791) = Real.sqrt 2 + values10 (9 : Fin 54) by rfl]
    simp only [values15_special_585_rightCert, IntervalCert.expr, eval]
    rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_585_leftCert, values15_special_585_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_586_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1259 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (551 / 500 : Rat) (1103 / 1000 : Rat) (IntervalCert.sqrt (152 / 125 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_586_rightCert : IntervalCert :=
  IntervalCert.add (2521 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7609 / 5000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_586 :
    values15 (586 : Fin 791) < values15 (587 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_586_leftCert values15_special_586_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_586_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_586_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (586 : Fin 791) = Real.sqrt 2 + values10 (9 : Fin 54) by rfl]
    simp only [values15_special_586_leftCert, IntervalCert.expr, eval]
    rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (587 : Fin 791) = 1 + values13 (107 : Fin 264) by rfl]
    simp only [values15_special_586_rightCert, IntervalCert.expr, eval]
    rw [show values13 (107 : Fin 264) = Real.sqrt (values12 (107 : Fin 154)) by rfl]
    rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_586_leftCert, values15_special_586_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_587_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1261 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1521 / 1000 : Rat) (15219 / 10000 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_587_rightCert : IntervalCert :=
  IntervalCert.add (253 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2791 / 2500 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_587 :
    values15 (587 : Fin 791) < values15 (588 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_587_leftCert values15_special_587_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_587_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_587_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (587 : Fin 791) = 1 + values13 (107 : Fin 264) by rfl]
    simp only [values15_special_587_leftCert, IntervalCert.expr, eval]
    rw [show values13 (107 : Fin 264) = Real.sqrt (values12 (107 : Fin 154)) by rfl]
    rw [show values12 (107 : Fin 154) = 1 + values10 (17 : Fin 54) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (588 : Fin 791) = Real.sqrt 2 + values10 (10 : Fin 54) by rfl]
    simp only [values15_special_587_rightCert, IntervalCert.expr, eval]
    rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_587_leftCert, values15_special_587_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_588_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2531 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (279 / 250 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_588_rightCert : IntervalCert :=
  IntervalCert.sqrt (633 / 250 : Rat) (100 : Rat) (IntervalCert.add (3207 / 500 : Rat) (1283 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (27071 / 5000 : Rat) (54143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (441421 / 100000 : Rat) (220711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_588 :
    values15 (588 : Fin 791) < values15 (589 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_588_leftCert values15_special_588_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_588_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_588_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (588 : Fin 791) = Real.sqrt 2 + values10 (10 : Fin 54) by rfl]
    simp only [values15_special_588_leftCert, IntervalCert.expr, eval]
    rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (589 : Fin 791) = Real.sqrt (values14 (453 : Fin 455)) by rfl]
    simp only [values15_special_588_rightCert, IntervalCert.expr, eval]
    rw [show values14 (453 : Fin 455) = 1 + values12 (152 : Fin 154) by rfl]
    rw [show values12 (152 : Fin 154) = 1 + values10 (52 : Fin 54) by rfl]
    rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_588_leftCert, values15_special_588_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_589_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2533 / 1000 : Rat) (IntervalCert.add (3207 / 500 : Rat) (1283 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (27071 / 5000 : Rat) (54143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (441421 / 100000 : Rat) (220711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_589_rightCert : IntervalCert :=
  IntervalCert.add (317 / 125 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (192001 / 125000 : Rat) (1537 / 1000 : Rat) (IntervalCert.add (2359323 / 1000000 : Rat) (59 / 25 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1359323017 / 1000000000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (369551813 / 200000000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (34142135623 / 10000000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (241421356237 / 100000000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999999999 / 1000000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213562373 / 1000000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999999999 / 10000000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999999999 / 100000000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999999999 / 100000000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_589 :
    values15 (589 : Fin 791) < values15 (590 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_589_leftCert values15_special_589_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_589_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_589_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (589 : Fin 791) = Real.sqrt (values14 (453 : Fin 455)) by rfl]
    simp only [values15_special_589_leftCert, IntervalCert.expr, eval]
    rw [show values14 (453 : Fin 455) = 1 + values12 (152 : Fin 154) by rfl]
    rw [show values12 (152 : Fin 154) = 1 + values10 (52 : Fin 54) by rfl]
    rw [show values10 (52 : Fin 54) = 1 + values8 (18 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (590 : Fin 791) = 1 + values13 (108 : Fin 264) by rfl]
    simp only [values15_special_589_rightCert, IntervalCert.expr, eval]
    rw [show values13 (108 : Fin 264) = Real.sqrt (values12 (108 : Fin 154)) by rfl]
    rw [show values12 (108 : Fin 154) = 1 + values10 (18 : Fin 54) by rfl]
    rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_589_leftCert, values15_special_589_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_593_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2559 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (779 / 500 : Rat) (3897 / 2500 : Rat) (IntervalCert.add (2429 / 1000 : Rat) (12149 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (14297 / 10000 : Rat) (714891 / 500000 : Rat) (IntervalCert.add (10221 / 5000 : Rat) (1022137 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_593_rightCert : IntervalCert :=
  IntervalCert.add (2561 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_593 :
    values15 (593 : Fin 791) < values15 (594 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_593_leftCert values15_special_593_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_593_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_593_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (593 : Fin 791) = 1 + values13 (111 : Fin 264) by rfl]
    simp only [values15_special_593_leftCert, IntervalCert.expr, eval]
    rw [show values13 (111 : Fin 264) = Real.sqrt (values12 (111 : Fin 154)) by rfl]
    rw [show values12 (111 : Fin 154) = 1 + values10 (20 : Fin 54) by rfl]
    rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (594 : Fin 791) = Real.sqrt 2 + values10 (11 : Fin 54) by rfl]
    simp only [values15_special_593_rightCert, IntervalCert.expr, eval]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_593_leftCert, values15_special_593_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_594_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1281 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_594_rightCert : IntervalCert :=
  IntervalCert.add (25639 / 10000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19549 / 12500 : Rat) (391 / 250 : Rat) (IntervalCert.add (48917 / 20000 : Rat) (1223 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (722929 / 500000 : Rat) (14459 / 10000 : Rat) (IntervalCert.add (2090507 / 1000000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_594 :
    values15 (594 : Fin 791) < values15 (595 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_594_leftCert values15_special_594_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_594_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_594_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (594 : Fin 791) = Real.sqrt 2 + values10 (11 : Fin 54) by rfl]
    simp only [values15_special_594_leftCert, IntervalCert.expr, eval]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (595 : Fin 791) = 1 + values13 (112 : Fin 264) by rfl]
    simp only [values15_special_594_rightCert, IntervalCert.expr, eval]
    rw [show values13 (112 : Fin 264) = Real.sqrt (values12 (112 : Fin 154)) by rfl]
    rw [show values12 (112 : Fin 154) = 1 + values10 (21 : Fin 54) by rfl]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_594_leftCert, values15_special_594_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_597_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (321 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1567 / 1000 : Rat) (39199 / 25000 : Rat) (IntervalCert.add (1229 / 500 : Rat) (245849 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values15_special_597_rightCert : IntervalCert :=
  IntervalCert.add (257 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (147959 / 100000 : Rat) (37 / 25 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (219 / 100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_597 :
    values15 (597 : Fin 791) < values15 (598 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_597_leftCert values15_special_597_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_597_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_597_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (597 : Fin 791) = 1 + values13 (114 : Fin 264) by rfl]
    simp only [values15_special_597_leftCert, IntervalCert.expr, eval]
    rw [show values13 (114 : Fin 264) = Real.sqrt (values12 (114 : Fin 154)) by rfl]
    rw [show values12 (114 : Fin 154) = Real.sqrt 2 + values7 (1 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (598 : Fin 791) = values6 (1 : Fin 8) + values8 (9 : Fin 20) by rfl]
    simp only [values15_special_597_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_597_leftCert, values15_special_597_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_598_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2571 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_598_rightCert : IntervalCert :=
  IntervalCert.add (1287 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7873 / 5000 : Rat) (63 / 40 : Rat) (IntervalCert.add (4959 / 2000 : Rat) (62 / 25 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_598 :
    values15 (598 : Fin 791) < values15 (599 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_598_leftCert values15_special_598_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_598_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_598_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (598 : Fin 791) = values6 (1 : Fin 8) + values8 (9 : Fin 20) by rfl]
    simp only [values15_special_598_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (599 : Fin 791) = 1 + values13 (115 : Fin 264) by rfl]
    simp only [values15_special_598_rightCert, IntervalCert.expr, eval]
    rw [show values13 (115 : Fin 264) = Real.sqrt (values12 (115 : Fin 154)) by rfl]
    rw [show values12 (115 : Fin 154) = 1 + values10 (22 : Fin 54) by rfl]
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_598_leftCert, values15_special_598_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_601_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2589 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (397 / 250 : Rat) (15881 / 10000 : Rat) (IntervalCert.add (12609 / 5000 : Rat) (1261 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (76093 / 50000 : Rat) (15219 / 10000 : Rat) (IntervalCert.add (231607 / 100000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values15_special_601_rightCert : IntervalCert :=
  IntervalCert.add (1299 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_601 :
    values15 (601 : Fin 791) < values15 (602 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_601_leftCert values15_special_601_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_601_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_601_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (601 : Fin 791) = 1 + values13 (117 : Fin 264) by rfl]
    simp only [values15_special_601_leftCert, IntervalCert.expr, eval]
    rw [show values13 (117 : Fin 264) = Real.sqrt (values12 (117 : Fin 154)) by rfl]
    rw [show values12 (117 : Fin 154) = 1 + values10 (23 : Fin 54) by rfl]
    rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (602 : Fin 791) = values7 (1 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_601_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_601_leftCert, values15_special_601_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_602_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (81189 / 31250 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000000001 / 1000000000 : Rat))))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))

private def values15_special_602_rightCert : IntervalCert :=
  IntervalCert.add (2598053 / 1000000 : Rat) (100 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (79902659 / 50000000 : Rat) (1599 / 1000 : Rat) (IntervalCert.add (255377397 / 100000000 : Rat) (1277 / 500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (776886987 / 500000000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (24142135623 / 10000000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_602 :
    values15 (602 : Fin 791) < values15 (603 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_602_leftCert values15_special_602_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_602_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_602_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (602 : Fin 791) = values7 (1 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_602_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (603 : Fin 791) = 1 + values13 (118 : Fin 264) by rfl]
    simp only [values15_special_602_rightCert, IntervalCert.expr, eval]
    rw [show values13 (118 : Fin 264) = Real.sqrt (values12 (118 : Fin 154)) by rfl]
    rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_602_leftCert, values15_special_602_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_603_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2599 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (799 / 500 : Rat) (15981 / 10000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_603_rightCert : IntervalCert :=
  IntervalCert.add (2603 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_603 :
    values15 (603 : Fin 791) < values15 (604 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_603_leftCert values15_special_603_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_603_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_603_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (603 : Fin 791) = 1 + values13 (118 : Fin 264) by rfl]
    simp only [values15_special_603_leftCert, IntervalCert.expr, eval]
    rw [show values13 (118 : Fin 264) = Real.sqrt (values12 (118 : Fin 154)) by rfl]
    rw [show values12 (118 : Fin 154) = 1 + values10 (24 : Fin 54) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (604 : Fin 791) = Real.sqrt 2 + values10 (12 : Fin 54) by rfl]
    simp only [values15_special_603_rightCert, IntervalCert.expr, eval]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_603_leftCert, values15_special_603_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_604_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_604_rightCert : IntervalCert :=
  IntervalCert.add (2611 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (8059 / 5000 : Rat) (403 / 250 : Rat) (IntervalCert.add (1299 / 500 : Rat) (25981 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (31961 / 20000 : Rat) (79903 / 50000 : Rat) (IntervalCert.add (255377 / 100000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_604 :
    values15 (604 : Fin 791) < values15 (605 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_604_leftCert values15_special_604_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_604_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_604_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (604 : Fin 791) = Real.sqrt 2 + values10 (12 : Fin 54) by rfl]
    simp only [values15_special_604_leftCert, IntervalCert.expr, eval]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (605 : Fin 791) = 1 + values13 (119 : Fin 264) by rfl]
    simp only [values15_special_604_rightCert, IntervalCert.expr, eval]
    rw [show values13 (119 : Fin 264) = Real.sqrt (values12 (119 : Fin 154)) by rfl]
    rw [show values12 (119 : Fin 154) = 1 + values10 (25 : Fin 54) by rfl]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_604_leftCert, values15_special_604_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_606_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1307 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1613 / 1000 : Rat) (2017 / 1250 : Rat) (IntervalCert.add (2603 / 1000 : Rat) (5207 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_606_rightCert : IntervalCert :=
  IntervalCert.add (327 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (1503 / 1250 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (7229 / 5000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_606 :
    values15 (606 : Fin 791) < values15 (607 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_606_leftCert values15_special_606_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_606_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_606_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (606 : Fin 791) = 1 + values13 (120 : Fin 264) by rfl]
    simp only [values15_special_606_leftCert, IntervalCert.expr, eval]
    rw [show values13 (120 : Fin 264) = Real.sqrt (values12 (120 : Fin 154)) by rfl]
    rw [show values12 (120 : Fin 154) = Real.sqrt 2 + values7 (3 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (607 : Fin 791) = Real.sqrt 2 + values10 (13 : Fin 54) by rfl]
    simp only [values15_special_606_rightCert, IntervalCert.expr, eval]
    rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_606_leftCert, values15_special_606_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_607_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2617 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (601 / 500 : Rat) (481 / 400 : Rat) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_607_rightCert : IntervalCert :=
  IntervalCert.add (657 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (16287 / 10000 : Rat) (1629 / 1000 : Rat) (IntervalCert.add (1658 / 625 : Rat) (2653 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (165289 / 100000 : Rat) (16529 / 10000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_607 :
    values15 (607 : Fin 791) < values15 (608 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_607_leftCert values15_special_607_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_607_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_607_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (607 : Fin 791) = Real.sqrt 2 + values10 (13 : Fin 54) by rfl]
    simp only [values15_special_607_leftCert, IntervalCert.expr, eval]
    rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (608 : Fin 791) = 1 + values13 (121 : Fin 264) by rfl]
    simp only [values15_special_607_rightCert, IntervalCert.expr, eval]
    rw [show values13 (121 : Fin 264) = Real.sqrt (values12 (121 : Fin 154)) by rfl]
    rw [show values12 (121 : Fin 154) = 1 + values10 (26 : Fin 54) by rfl]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_607_leftCert, values15_special_607_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_608_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2629 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (407 / 250 : Rat) (1018 / 625 : Rat) (IntervalCert.add (663 / 250 : Rat) (26529 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1033 / 625 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_608_rightCert : IntervalCert :=
  IntervalCert.add (263 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_608 :
    values15 (608 : Fin 791) < values15 (609 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_608_leftCert values15_special_608_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_608_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_608_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (608 : Fin 791) = 1 + values13 (121 : Fin 264) by rfl]
    simp only [values15_special_608_leftCert, IntervalCert.expr, eval]
    rw [show values13 (121 : Fin 264) = Real.sqrt (values12 (121 : Fin 154)) by rfl]
    rw [show values12 (121 : Fin 154) = 1 + values10 (26 : Fin 54) by rfl]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (609 : Fin 791) = Real.sqrt 2 + values10 (14 : Fin 54) by rfl]
    simp only [values15_special_608_rightCert, IntervalCert.expr, eval]
    rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_608_leftCert, values15_special_608_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_609_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2631 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (152 / 125 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_609_rightCert : IntervalCert :=
  IntervalCert.add (329 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_609 :
    values15 (609 : Fin 791) < values15 (610 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_609_leftCert values15_special_609_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_609_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_609_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (609 : Fin 791) = Real.sqrt 2 + values10 (14 : Fin 54) by rfl]
    simp only [values15_special_609_leftCert, IntervalCert.expr, eval]
    rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (610 : Fin 791) = values7 (4 : Fin 13) + values7 (4 : Fin 13) by rfl]
    simp only [values15_special_609_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_609_leftCert, values15_special_609_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_610_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2633 / 1000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values15_special_610_rightCert : IntervalCert :=
  IntervalCert.add (527 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_610 :
    values15 (610 : Fin 791) < values15 (611 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_610_leftCert values15_special_610_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_610_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_610_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (610 : Fin 791) = values7 (4 : Fin 13) + values7 (4 : Fin 13) by rfl]
    simp only [values15_special_610_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (611 : Fin 791) = values5 (1 : Fin 5) + values9 (13 : Fin 33) by rfl]
    simp only [values15_special_610_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_610_leftCert, values15_special_610_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_611_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (26351 / 10000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (289 / 200 : Rat) (72293 / 50000 : Rat) (IntervalCert.add (209 / 100 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))

private def values15_special_611_rightCert : IntervalCert :=
  IntervalCert.add (2637 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2047 / 1250 : Rat) (819 / 500 : Rat) (IntervalCert.add (268179 / 100000 : Rat) (1341 / 500 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (26278 / 15625 : Rat) (8409 / 5000 : Rat) (IntervalCert.add (2828427 / 1000000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_611 :
    values15 (611 : Fin 791) < values15 (612 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_611_leftCert values15_special_611_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_611_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_611_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (611 : Fin 791) = values5 (1 : Fin 5) + values9 (13 : Fin 33) by rfl]
    simp only [values15_special_611_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (612 : Fin 791) = 1 + values13 (122 : Fin 264) by rfl]
    simp only [values15_special_611_rightCert, IntervalCert.expr, eval]
    rw [show values13 (122 : Fin 264) = Real.sqrt (values12 (122 : Fin 154)) by rfl]
    rw [show values12 (122 : Fin 154) = 1 + values10 (27 : Fin 54) by rfl]
    rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_611_leftCert, values15_special_611_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_612_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1319 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1637 / 1000 : Rat) (16377 / 10000 : Rat) (IntervalCert.add (2681 / 1000 : Rat) (1341 / 500 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (16817 / 10000 : Rat) (8409 / 5000 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_612_rightCert : IntervalCert :=
  IntervalCert.add (661 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_612 :
    values15 (612 : Fin 791) < values15 (613 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_612_leftCert values15_special_612_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_612_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_612_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (612 : Fin 791) = 1 + values13 (122 : Fin 264) by rfl]
    simp only [values15_special_612_leftCert, IntervalCert.expr, eval]
    rw [show values13 (122 : Fin 264) = Real.sqrt (values12 (122 : Fin 154)) by rfl]
    rw [show values12 (122 : Fin 154) = 1 + values10 (27 : Fin 54) by rfl]
    rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (613 : Fin 791) = values6 (1 : Fin 8) + values8 (10 : Fin 20) by rfl]
    simp only [values15_special_612_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_612_leftCert, values15_special_612_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_613_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (26443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_613_rightCert : IntervalCert :=
  IntervalCert.sqrt (26457 / 10000 : Rat) (100 : Rat) (IntervalCert.add (69999 / 10000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (599999 / 100000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4999999 / 1000000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (39999999 / 10000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_613 :
    values15 (613 : Fin 791) < values15 (614 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_613_leftCert values15_special_613_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_613_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_613_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (613 : Fin 791) = values6 (1 : Fin 8) + values8 (10 : Fin 20) by rfl]
    simp only [values15_special_613_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (614 : Fin 791) = Real.sqrt (values14 (454 : Fin 455)) by rfl]
    simp only [values15_special_613_rightCert, IntervalCert.expr, eval]
    rw [show values14 (454 : Fin 455) = 1 + values12 (153 : Fin 154) by rfl]
    rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by rfl]
    rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_613_leftCert, values15_special_613_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_614_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1323 / 500 : Rat) (IntervalCert.add (6999 / 1000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (59999 / 10000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (499999 / 100000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_614_rightCert : IntervalCert :=
  IntervalCert.add (663 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (16523 / 10000 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (13651 / 5000 : Rat) (2731 / 1000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (131607 / 100000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_614 :
    values15 (614 : Fin 791) < values15 (615 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_614_leftCert values15_special_614_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_614_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_614_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (614 : Fin 791) = Real.sqrt (values14 (454 : Fin 455)) by rfl]
    simp only [values15_special_614_leftCert, IntervalCert.expr, eval]
    rw [show values14 (454 : Fin 455) = 1 + values12 (153 : Fin 154) by rfl]
    rw [show values12 (153 : Fin 154) = 1 + values10 (53 : Fin 54) by rfl]
    rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (615 : Fin 791) = 1 + values13 (123 : Fin 264) by rfl]
    simp only [values15_special_614_rightCert, IntervalCert.expr, eval]
    rw [show values13 (123 : Fin 264) = Real.sqrt (values12 (123 : Fin 154)) by rfl]
    rw [show values12 (123 : Fin 154) = Real.sqrt 2 + values7 (4 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_614_leftCert, values15_special_614_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_616_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2653 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (413 / 250 : Rat) (16529 / 10000 : Rat) (IntervalCert.add (683 / 250 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_616_rightCert : IntervalCert :=
  IntervalCert.add (133 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_616 :
    values15 (616 : Fin 791) < values15 (617 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_616_leftCert values15_special_616_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_616_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_616_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (616 : Fin 791) = 1 + values13 (124 : Fin 264) by rfl]
    simp only [values15_special_616_leftCert, IntervalCert.expr, eval]
    rw [show values13 (124 : Fin 264) = Real.sqrt (values12 (124 : Fin 154)) by rfl]
    rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (617 : Fin 791) = Real.sqrt 2 + values10 (15 : Fin 54) by rfl]
    simp only [values15_special_616_rightCert, IntervalCert.expr, eval]
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_616_leftCert, values15_special_616_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_617_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2661 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_617_rightCert : IntervalCert :=
  IntervalCert.add (667 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_617 :
    values15 (617 : Fin 791) < values15 (618 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_617_leftCert values15_special_617_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_617_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_617_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (617 : Fin 791) = Real.sqrt 2 + values10 (15 : Fin 54) by rfl]
    simp only [values15_special_617_leftCert, IntervalCert.expr, eval]
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (618 : Fin 791) = values5 (1 : Fin 5) + values9 (14 : Fin 33) by rfl]
    simp only [values15_special_617_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_617_leftCert, values15_special_617_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_618_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (266881 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (1479 / 1000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values15_special_618_rightCert : IntervalCert :=
  IntervalCert.add (2669 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (41727 / 25000 : Rat) (167 / 100 : Rat) (IntervalCert.add (278583 / 100000 : Rat) (1393 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (357167 / 200000 : Rat) (22323 / 12500 : Rat) (IntervalCert.add (3189207 / 1000000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_618 :
    values15 (618 : Fin 791) < values15 (619 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_618_leftCert values15_special_618_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_618_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_618_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (618 : Fin 791) = values5 (1 : Fin 5) + values9 (14 : Fin 33) by rfl]
    simp only [values15_special_618_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (619 : Fin 791) = 1 + values13 (125 : Fin 264) by rfl]
    simp only [values15_special_618_rightCert, IntervalCert.expr, eval]
    rw [show values13 (125 : Fin 264) = Real.sqrt (values12 (125 : Fin 154)) by rfl]
    rw [show values12 (125 : Fin 154) = 1 + values10 (29 : Fin 54) by rfl]
    rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_618_leftCert, values15_special_618_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_621_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (336 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1687 / 1000 : Rat) (4219 / 2500 : Rat) (IntervalCert.add (2847 / 1000 : Rat) (14239 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_621_rightCert : IntervalCert :=
  IntervalCert.add (2699 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (1607 / 1250 : Rat) (643 / 500 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_621 :
    values15 (621 : Fin 791) < values15 (622 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_621_leftCert values15_special_621_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_621_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_621_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (621 : Fin 791) = 1 + values13 (127 : Fin 264) by rfl]
    simp only [values15_special_621_leftCert, IntervalCert.expr, eval]
    rw [show values13 (127 : Fin 264) = Real.sqrt (values12 (127 : Fin 154)) by rfl]
    rw [show values12 (127 : Fin 154) = 1 + values10 (30 : Fin 54) by rfl]
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (622 : Fin 791) = Real.sqrt 2 + values10 (16 : Fin 54) by rfl]
    simp only [values15_special_621_rightCert, IntervalCert.expr, eval]
    rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_621_leftCert, values15_special_621_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_622_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (27 / 10 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (257 / 200 : Rat) (25713 / 20000 : Rat) (IntervalCert.sqrt (413 / 250 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))

private def values15_special_622_rightCert : IntervalCert :=
  IntervalCert.add (2709 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (42729 / 25000 : Rat) (171 / 100 : Rat) (IntervalCert.add (2337 / 800 : Rat) (1461 / 500 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_622 :
    values15 (622 : Fin 791) < values15 (623 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_622_leftCert values15_special_622_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_622_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_622_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (622 : Fin 791) = Real.sqrt 2 + values10 (16 : Fin 54) by rfl]
    simp only [values15_special_622_leftCert, IntervalCert.expr, eval]
    rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (623 : Fin 791) = 1 + values13 (128 : Fin 264) by rfl]
    simp only [values15_special_622_rightCert, IntervalCert.expr, eval]
    rw [show values13 (128 : Fin 264) = Real.sqrt (values12 (128 : Fin 154)) by rfl]
    rw [show values12 (128 : Fin 154) = values5 (1 : Fin 5) + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_622_leftCert, values15_special_622_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_624_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2723 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (861 / 500 : Rat) (4307 / 2500 : Rat) (IntervalCert.add (2967 / 1000 : Rat) (371 / 125 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (15537 / 10000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values15_special_624_rightCert : IntervalCert :=
  IntervalCert.add (273 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_624 :
    values15 (624 : Fin 791) < values15 (625 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_624_leftCert values15_special_624_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_624_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_624_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (624 : Fin 791) = 1 + values13 (129 : Fin 264) by rfl]
    simp only [values15_special_624_leftCert, IntervalCert.expr, eval]
    rw [show values13 (129 : Fin 264) = Real.sqrt (values12 (129 : Fin 154)) by rfl]
    rw [show values12 (129 : Fin 154) = Real.sqrt 2 + values7 (6 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (625 : Fin 791) = Real.sqrt 2 + values10 (17 : Fin 54) by rfl]
    simp only [values15_special_624_rightCert, IntervalCert.expr, eval]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_624_leftCert, values15_special_624_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_625_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (27303 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_625_rightCert : IntervalCert :=
  IntervalCert.add (683 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_625 :
    values15 (625 : Fin 791) < values15 (626 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_625_leftCert values15_special_625_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_625_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_625_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (625 : Fin 791) = Real.sqrt 2 + values10 (17 : Fin 54) by rfl]
    simp only [values15_special_625_leftCert, IntervalCert.expr, eval]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (626 : Fin 791) = 1 + values13 (130 : Fin 264) by rfl]
    simp only [values15_special_625_rightCert, IntervalCert.expr, eval]
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_625_leftCert, values15_special_625_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_627_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2739 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (869 / 500 : Rat) (2173 / 1250 : Rat) (IntervalCert.add (3021 / 1000 : Rat) (1511 / 500 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (10109 / 5000 : Rat) (20219 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (102189 / 100000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_627_rightCert : IntervalCert :=
  IntervalCert.add (1371 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_627 :
    values15 (627 : Fin 791) < values15 (628 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_627_leftCert values15_special_627_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_627_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_627_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (627 : Fin 791) = 1 + values13 (131 : Fin 264) by rfl]
    simp only [values15_special_627_leftCert, IntervalCert.expr, eval]
    rw [show values13 (131 : Fin 264) = Real.sqrt (values12 (131 : Fin 154)) by rfl]
    rw [show values12 (131 : Fin 154) = 1 + values10 (32 : Fin 54) by rfl]
    rw [show values10 (32 : Fin 54) = 1 + values8 (1 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (628 : Fin 791) = values5 (1 : Fin 5) + values9 (15 : Fin 33) by rfl]
    simp only [values15_special_627_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_627_leftCert, values15_special_627_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_628_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2743 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_628_rightCert : IntervalCert :=
  IntervalCert.add (27447 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (87239 / 50000 : Rat) (349 / 200 : Rat) (IntervalCert.add (304427 / 100000 : Rat) (609 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_628 :
    values15 (628 : Fin 791) < values15 (629 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_628_leftCert values15_special_628_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_628_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_628_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (628 : Fin 791) = values5 (1 : Fin 5) + values9 (15 : Fin 33) by rfl]
    simp only [values15_special_628_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (629 : Fin 791) = 1 + values13 (132 : Fin 264) by rfl]
    simp only [values15_special_628_rightCert, IntervalCert.expr, eval]
    rw [show values13 (132 : Fin 264) = Real.sqrt (values12 (132 : Fin 154)) by rfl]
    rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
    rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_628_leftCert, values15_special_628_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_629_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (549 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (218 / 125 : Rat) (2181 / 1250 : Rat) (IntervalCert.add (761 / 250 : Rat) (30443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (10221 / 5000 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_629_rightCert : IntervalCert :=
  IntervalCert.add (2753 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (5109 / 5000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_629 :
    values15 (629 : Fin 791) < values15 (630 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_629_leftCert values15_special_629_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_629_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_629_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (629 : Fin 791) = 1 + values13 (132 : Fin 264) by rfl]
    simp only [values15_special_629_leftCert, IntervalCert.expr, eval]
    rw [show values13 (132 : Fin 264) = Real.sqrt (values12 (132 : Fin 154)) by rfl]
    rw [show values12 (132 : Fin 154) = 1 + values10 (33 : Fin 54) by rfl]
    rw [show values10 (33 : Fin 54) = 1 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (630 : Fin 791) = values6 (4 : Fin 8) + values8 (1 : Fin 20) by rfl]
    simp only [values15_special_629_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_629_leftCert, values15_special_629_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_630_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1377 / 500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (1021 / 1000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat))))))))

private def values15_special_630_rightCert : IntervalCert :=
  IntervalCert.add (2757 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (17579 / 10000 : Rat) (879 / 500 : Rat) (IntervalCert.add (6181 / 2000 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2090507 / 1000000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_630 :
    values15 (630 : Fin 791) < values15 (631 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_630_leftCert values15_special_630_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_630_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_630_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (630 : Fin 791) = values6 (4 : Fin 8) + values8 (1 : Fin 20) by rfl]
    simp only [values15_special_630_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (631 : Fin 791) = 1 + values13 (133 : Fin 264) by rfl]
    simp only [values15_special_630_rightCert, IntervalCert.expr, eval]
    rw [show values13 (133 : Fin 264) = Real.sqrt (values12 (133 : Fin 154)) by rfl]
    rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
    rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_630_leftCert, values15_special_630_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_631_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1379 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1757 / 1000 : Rat) (54937 / 31250 : Rat) (IntervalCert.add (309 / 100 : Rat) (154525387 / 50000000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (4181 / 2000 : Rat) (2090507733 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (10905077327 / 10000000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118920711501 / 100000000000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70710678119 / 50000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)))))))))))

private def values15_special_631_rightCert : IntervalCert :=
  IntervalCert.add (2773 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (13593 / 10000 : Rat) (34 / 25 : Rat) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_631 :
    values15 (631 : Fin 791) < values15 (632 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_631_leftCert values15_special_631_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_631_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_631_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (631 : Fin 791) = 1 + values13 (133 : Fin 264) by rfl]
    simp only [values15_special_631_leftCert, IntervalCert.expr, eval]
    rw [show values13 (133 : Fin 264) = Real.sqrt (values12 (133 : Fin 154)) by rfl]
    rw [show values12 (133 : Fin 154) = 1 + values10 (34 : Fin 54) by rfl]
    rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (632 : Fin 791) = Real.sqrt 2 + values10 (18 : Fin 54) by rfl]
    simp only [values15_special_631_rightCert, IntervalCert.expr, eval]
    rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_631_leftCert, values15_special_631_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_632_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3467 / 1250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values15_special_632_rightCert : IntervalCert :=
  IntervalCert.add (27737 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (177377 / 100000 : Rat) (887 / 500 : Rat) (IntervalCert.add (393283 / 125000 : Rat) (3147 / 1000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_632 :
    values15 (632 : Fin 791) < values15 (633 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_632_leftCert values15_special_632_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_632_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_632_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (632 : Fin 791) = Real.sqrt 2 + values10 (18 : Fin 54) by rfl]
    simp only [values15_special_632_leftCert, IntervalCert.expr, eval]
    rw [show values10 (18 : Fin 54) = Real.sqrt (values9 (18 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (633 : Fin 791) = 1 + values13 (134 : Fin 264) by rfl]
    simp only [values15_special_632_rightCert, IntervalCert.expr, eval]
    rw [show values13 (134 : Fin 264) = Real.sqrt (values12 (134 : Fin 154)) by rfl]
    rw [show values12 (134 : Fin 154) = Real.sqrt 2 + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_632_leftCert, values15_special_632_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_634_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (27741 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (887 / 500 : Rat) (44351 / 25000 : Rat) (IntervalCert.add (1967 / 625 : Rat) (314721 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1073601 / 500000 : Rat) (2147203 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (5736013 / 5000000 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_634_rightCert : IntervalCert :=
  IntervalCert.add (347 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_634 :
    values15 (634 : Fin 791) < values15 (635 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_634_leftCert values15_special_634_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_634_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_634_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (634 : Fin 791) = 1 + values13 (135 : Fin 264) by rfl]
    simp only [values15_special_634_leftCert, IntervalCert.expr, eval]
    rw [show values13 (135 : Fin 264) = Real.sqrt (values12 (135 : Fin 154)) by rfl]
    rw [show values12 (135 : Fin 154) = 1 + values10 (35 : Fin 54) by rfl]
    rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (635 : Fin 791) = values6 (4 : Fin 8) + values8 (2 : Fin 20) by rfl]
    simp only [values15_special_634_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_634_leftCert, values15_special_634_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_635_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2777 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_635_rightCert : IntervalCert :=
  IntervalCert.add (557 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (8929 / 5000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_635 :
    values15 (635 : Fin 791) < values15 (636 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_635_leftCert values15_special_635_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_635_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_635_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (635 : Fin 791) = values6 (4 : Fin 8) + values8 (2 : Fin 20) by rfl]
    simp only [values15_special_635_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (636 : Fin 791) = 1 + values13 (136 : Fin 264) by rfl]
    simp only [values15_special_635_rightCert, IntervalCert.expr, eval]
    rw [show values13 (136 : Fin 264) = Real.sqrt (values12 (136 : Fin 154)) by rfl]
    rw [show values12 (136 : Fin 154) = 1 + values10 (36 : Fin 54) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_635_leftCert, values15_special_635_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_639_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (28211 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1821 / 1000 : Rat) (182101 / 100000 : Rat) (IntervalCert.add (331607 / 100000 : Rat) (132643 / 40000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (23160741 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_639_rightCert : IntervalCert :=
  IntervalCert.add (1129 / 400 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_639 :
    values15 (639 : Fin 791) < values15 (640 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_639_leftCert values15_special_639_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_639_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_639_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (639 : Fin 791) = 1 + values13 (139 : Fin 264) by rfl]
    simp only [values15_special_639_leftCert, IntervalCert.expr, eval]
    rw [show values13 (139 : Fin 264) = Real.sqrt (values12 (139 : Fin 154)) by rfl]
    rw [show values12 (139 : Fin 154) = 1 + values10 (39 : Fin 54) by rfl]
    rw [show values10 (39 : Fin 54) = 1 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (640 : Fin 791) = values6 (1 : Fin 8) + values8 (11 : Fin 20) by rfl]
    simp only [values15_special_639_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_639_leftCert, values15_special_639_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_640_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2823 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_640_rightCert : IntervalCert :=
  IntervalCert.add (707 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_640 :
    values15 (640 : Fin 791) < values15 (641 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_640_leftCert values15_special_640_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_640_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_640_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (640 : Fin 791) = values6 (1 : Fin 8) + values8 (11 : Fin 20) by rfl]
    simp only [values15_special_640_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (641 : Fin 791) = Real.sqrt 2 + values10 (19 : Fin 54) by rfl]
    simp only [values15_special_640_rightCert, IntervalCert.expr, eval]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_640_leftCert, values15_special_640_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_641_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_641_rightCert : IntervalCert :=
  IntervalCert.add (1421 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (165289 / 100000 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_641 :
    values15 (641 : Fin 791) < values15 (642 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_641_leftCert values15_special_641_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_641_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_641_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (641 : Fin 791) = Real.sqrt 2 + values10 (19 : Fin 54) by rfl]
    simp only [values15_special_641_leftCert, IntervalCert.expr, eval]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (642 : Fin 791) = values5 (1 : Fin 5) + values9 (16 : Fin 33) by rfl]
    simp only [values15_special_641_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_641_leftCert, values15_special_641_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_642_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (28421 / 10000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat))))) (IntervalCert.sqrt (413 / 250 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))

private def values15_special_642_rightCert : IntervalCert :=
  IntervalCert.add (28439 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (71489 / 50000 : Rat) (143 / 100 : Rat) (IntervalCert.add (2044273 / 1000000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_642 :
    values15 (642 : Fin 791) < values15 (643 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_642_leftCert values15_special_642_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_642_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_642_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (642 : Fin 791) = values5 (1 : Fin 5) + values9 (16 : Fin 33) by rfl]
    simp only [values15_special_642_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (643 : Fin 791) = Real.sqrt 2 + values10 (20 : Fin 54) by rfl]
    simp only [values15_special_642_rightCert, IntervalCert.expr, eval]
    rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_642_leftCert, values15_special_642_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_643_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (711 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1429 / 1000 : Rat) (714891 / 500000 : Rat) (IntervalCert.add (511 / 250 : Rat) (1022137 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_643_rightCert : IntervalCert :=
  IntervalCert.add (2847 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_643 :
    values15 (643 : Fin 791) < values15 (644 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_643_leftCert values15_special_643_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_643_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_643_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (643 : Fin 791) = Real.sqrt 2 + values10 (20 : Fin 54) by rfl]
    simp only [values15_special_643_leftCert, IntervalCert.expr, eval]
    rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (644 : Fin 791) = 1 + values13 (140 : Fin 264) by rfl]
    simp only [values15_special_643_rightCert, IntervalCert.expr, eval]
    rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
    rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_643_leftCert, values15_special_643_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_644_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (356 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1847 / 1000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (1707 / 500 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_644_rightCert : IntervalCert :=
  IntervalCert.add (143 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_644 :
    values15 (644 : Fin 791) < values15 (645 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_644_leftCert values15_special_644_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_644_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_644_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (644 : Fin 791) = 1 + values13 (140 : Fin 264) by rfl]
    simp only [values15_special_644_leftCert, IntervalCert.expr, eval]
    rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
    rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (645 : Fin 791) = Real.sqrt 2 + values10 (21 : Fin 54) by rfl]
    simp only [values15_special_644_rightCert, IntervalCert.expr, eval]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_644_leftCert, values15_special_644_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_645_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2861 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values15_special_645_rightCert : IntervalCert :=
  IntervalCert.add (573 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18653 / 10000 : Rat) (933 / 500 : Rat) (IntervalCert.add (6959 / 2000 : Rat) (87 / 25 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (247959 / 100000 : Rat) (6199 / 2500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (369899 / 250000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_645 :
    values15 (645 : Fin 791) < values15 (646 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_645_leftCert values15_special_645_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_645_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_645_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (645 : Fin 791) = Real.sqrt 2 + values10 (21 : Fin 54) by rfl]
    simp only [values15_special_645_leftCert, IntervalCert.expr, eval]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (646 : Fin 791) = 1 + values13 (141 : Fin 264) by rfl]
    simp only [values15_special_645_rightCert, IntervalCert.expr, eval]
    rw [show values13 (141 : Fin 264) = Real.sqrt (values12 (141 : Fin 154)) by rfl]
    rw [show values12 (141 : Fin 154) = 1 + values10 (41 : Fin 54) by rfl]
    rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_645_leftCert, values15_special_645_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_646_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1433 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (373 / 200 : Rat) (9327 / 5000 : Rat) (IntervalCert.add (3479 / 1000 : Rat) (8699 / 2500 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (4959 / 2000 : Rat) (2479597 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (147959 / 100000 : Rat) (29591939 / 20000000 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat))))))))))

private def values15_special_646_rightCert : IntervalCert :=
  IntervalCert.add (2869 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_646 :
    values15 (646 : Fin 791) < values15 (647 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_646_leftCert values15_special_646_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_646_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_646_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (646 : Fin 791) = 1 + values13 (141 : Fin 264) by rfl]
    simp only [values15_special_646_leftCert, IntervalCert.expr, eval]
    rw [show values13 (141 : Fin 264) = Real.sqrt (values12 (141 : Fin 154)) by rfl]
    rw [show values12 (141 : Fin 154) = 1 + values10 (41 : Fin 54) by rfl]
    rw [show values10 (41 : Fin 54) = 1 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (647 : Fin 791) = values7 (4 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_646_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_646_leftCert, values15_special_646_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_647_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (287 / 100 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values15_special_647_rightCert : IntervalCert :=
  IntervalCert.add (2879 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_647 :
    values15 (647 : Fin 791) < values15 (648 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_647_leftCert values15_special_647_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_647_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_647_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (647 : Fin 791) = values7 (4 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_647_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (648 : Fin 791) = values6 (4 : Fin 8) + values8 (4 : Fin 20) by rfl]
    simp only [values15_special_647_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_647_leftCert, values15_special_647_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_648_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (72 / 25 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_648_rightCert : IntervalCert :=
  IntervalCert.add (577 / 200 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18851 / 10000 : Rat) (943 / 500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (1777 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_648 :
    values15 (648 : Fin 791) < values15 (649 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_648_leftCert values15_special_648_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_648_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_648_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (648 : Fin 791) = values6 (4 : Fin 8) + values8 (4 : Fin 20) by rfl]
    simp only [values15_special_648_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (649 : Fin 791) = 1 + values13 (142 : Fin 264) by rfl]
    simp only [values15_special_648_rightCert, IntervalCert.expr, eval]
    rw [show values13 (142 : Fin 264) = Real.sqrt (values12 (142 : Fin 154)) by rfl]
    rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
    rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_648_leftCert, values15_special_648_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_649_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1443 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (377 / 200 : Rat) (4713 / 2500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_649_rightCert : IntervalCert :=
  IntervalCert.add (2893 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_649 :
    values15 (649 : Fin 791) < values15 (650 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_649_leftCert values15_special_649_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_649_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_649_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (649 : Fin 791) = 1 + values13 (142 : Fin 264) by rfl]
    simp only [values15_special_649_leftCert, IntervalCert.expr, eval]
    rw [show values13 (142 : Fin 264) = Real.sqrt (values12 (142 : Fin 154)) by rfl]
    rw [show values12 (142 : Fin 154) = 1 + values10 (42 : Fin 54) by rfl]
    rw [show values10 (42 : Fin 54) = 1 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (650 : Fin 791) = Real.sqrt 2 + values10 (22 : Fin 54) by rfl]
    simp only [values15_special_649_rightCert, IntervalCert.expr, eval]
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_649_leftCert, values15_special_649_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_650_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1447 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_650_rightCert : IntervalCert :=
  IntervalCert.add (1449 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (9491 / 5000 : Rat) (1899 / 1000 : Rat) (IntervalCert.add (18017 / 5000 : Rat) (901 / 250 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (130171 / 50000 : Rat) (5207 / 2000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_650 :
    values15 (650 : Fin 791) < values15 (651 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_650_leftCert values15_special_650_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_650_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_650_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (650 : Fin 791) = Real.sqrt 2 + values10 (22 : Fin 54) by rfl]
    simp only [values15_special_650_leftCert, IntervalCert.expr, eval]
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (651 : Fin 791) = 1 + values13 (143 : Fin 264) by rfl]
    simp only [values15_special_650_rightCert, IntervalCert.expr, eval]
    rw [show values13 (143 : Fin 264) = Real.sqrt (values12 (143 : Fin 154)) by rfl]
    rw [show values12 (143 : Fin 154) = 1 + values10 (43 : Fin 54) by rfl]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_650_leftCert, values15_special_650_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_651_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2899 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (949 / 500 : Rat) (18983 / 10000 : Rat) (IntervalCert.add (3603 / 1000 : Rat) (7207 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (13017 / 5000 : Rat) (260343 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_651_rightCert : IntervalCert :=
  IntervalCert.add (2921 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_651 :
    values15 (651 : Fin 791) < values15 (652 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_651_leftCert values15_special_651_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_651_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_651_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (651 : Fin 791) = 1 + values13 (143 : Fin 264) by rfl]
    simp only [values15_special_651_leftCert, IntervalCert.expr, eval]
    rw [show values13 (143 : Fin 264) = Real.sqrt (values12 (143 : Fin 154)) by rfl]
    rw [show values12 (143 : Fin 154) = 1 + values10 (43 : Fin 54) by rfl]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (652 : Fin 791) = values5 (1 : Fin 5) + values9 (17 : Fin 33) by rfl]
    simp only [values15_special_651_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_651_leftCert, values15_special_651_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_652_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1461 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_652_rightCert : IntervalCert :=
  IntervalCert.add (2931 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (9659 / 5000 : Rat) (483 / 250 : Rat) (IntervalCert.add (933 / 250 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_652 :
    values15 (652 : Fin 791) < values15 (653 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_652_leftCert values15_special_652_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_652_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_652_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (652 : Fin 791) = values5 (1 : Fin 5) + values9 (17 : Fin 33) by rfl]
    simp only [values15_special_652_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (653 : Fin 791) = 1 + values13 (144 : Fin 264) by rfl]
    simp only [values15_special_652_rightCert, IntervalCert.expr, eval]
    rw [show values13 (144 : Fin 264) = Real.sqrt (values12 (144 : Fin 154)) by rfl]
    rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_652_leftCert, values15_special_652_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_653_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (733 / 250 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1931 / 1000 : Rat) (19319 / 10000 : Rat) (IntervalCert.add (933 / 250 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values15_special_653_rightCert : IntervalCert :=
  IntervalCert.add (367 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (76093 / 50000 : Rat) (761 / 500 : Rat) (IntervalCert.add (231607 / 100000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_653 :
    values15 (653 : Fin 791) < values15 (654 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_653_leftCert values15_special_653_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_653_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_653_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (653 : Fin 791) = 1 + values13 (144 : Fin 264) by rfl]
    simp only [values15_special_653_leftCert, IntervalCert.expr, eval]
    rw [show values13 (144 : Fin 264) = Real.sqrt (values12 (144 : Fin 154)) by rfl]
    rw [show values12 (144 : Fin 154) = 1 + values10 (44 : Fin 54) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (654 : Fin 791) = Real.sqrt 2 + values10 (23 : Fin 54) by rfl]
    simp only [values15_special_653_rightCert, IntervalCert.expr, eval]
    rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_653_leftCert, values15_special_653_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_654_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2937 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1521 / 1000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_654_rightCert : IntervalCert :=
  IntervalCert.add (739 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (9783 / 5000 : Rat) (1957 / 1000 : Rat) (IntervalCert.add (9571 / 2500 : Rat) (3829 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (5657 / 2000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_654 :
    values15 (654 : Fin 791) < values15 (655 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_654_leftCert values15_special_654_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_654_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_654_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (654 : Fin 791) = Real.sqrt 2 + values10 (23 : Fin 54) by rfl]
    simp only [values15_special_654_leftCert, IntervalCert.expr, eval]
    rw [show values10 (23 : Fin 54) = Real.sqrt (values9 (23 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (655 : Fin 791) = 1 + values13 (145 : Fin 264) by rfl]
    simp only [values15_special_654_rightCert, IntervalCert.expr, eval]
    rw [show values13 (145 : Fin 264) = Real.sqrt (values12 (145 : Fin 154)) by rfl]
    rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_654_leftCert, values15_special_654_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_655_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2957 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (489 / 250 : Rat) (19567 / 10000 : Rat) (IntervalCert.add (957 / 250 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7071 / 2500 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_655_rightCert : IntervalCert :=
  IntervalCert.add (2967 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_655 :
    values15 (655 : Fin 791) < values15 (656 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_655_leftCert values15_special_655_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_655_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_655_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (655 : Fin 791) = 1 + values13 (145 : Fin 264) by rfl]
    simp only [values15_special_655_leftCert, IntervalCert.expr, eval]
    rw [show values13 (145 : Fin 264) = Real.sqrt (values12 (145 : Fin 154)) by rfl]
    rw [show values12 (145 : Fin 154) = 1 + values10 (45 : Fin 54) by rfl]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (656 : Fin 791) = Real.sqrt 2 + values10 (24 : Fin 54) by rfl]
    simp only [values15_special_655_rightCert, IntervalCert.expr, eval]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_655_leftCert, values15_special_655_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_656_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (371 / 125 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values15_special_656_rightCert : IntervalCert :=
  IntervalCert.add (1489 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_656 :
    values15 (656 : Fin 791) < values15 (657 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_656_leftCert values15_special_656_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_656_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_656_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (656 : Fin 791) = Real.sqrt 2 + values10 (24 : Fin 54) by rfl]
    simp only [values15_special_656_leftCert, IntervalCert.expr, eval]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (657 : Fin 791) = values6 (4 : Fin 8) + values8 (6 : Fin 20) by rfl]
    simp only [values15_special_656_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_656_leftCert, values15_special_656_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_657_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2979 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (623 / 500 : Rat) (6233 / 5000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values15_special_657_rightCert : IntervalCert :=
  IntervalCert.add (2999 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (3999999 / 1000000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_657 :
    values15 (657 : Fin 791) < values15 (658 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_657_leftCert values15_special_657_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_657_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_657_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (657 : Fin 791) = values6 (4 : Fin 8) + values8 (6 : Fin 20) by rfl]
    simp only [values15_special_657_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (658 : Fin 791) = 1 + values13 (146 : Fin 264) by rfl]
    simp only [values15_special_657_rightCert, IntervalCert.expr, eval]
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_657_leftCert, values15_special_657_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_661_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3011 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (201 / 100 : Rat) (20109 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2527 / 2500 : Rat) (101089 / 100000 : Rat) (IntervalCert.sqrt (5109 / 5000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))))))

private def values15_special_661_rightCert : IntervalCert :=
  IntervalCert.add (753 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (799 / 500 : Rat) (1599 / 1000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (1277 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_661 :
    values15 (661 : Fin 791) < values15 (662 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_661_leftCert values15_special_661_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_661_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_661_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (661 : Fin 791) = 1 + values13 (149 : Fin 264) by rfl]
    simp only [values15_special_661_leftCert, IntervalCert.expr, eval]
    rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
    rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (662 : Fin 791) = Real.sqrt 2 + values10 (25 : Fin 54) by rfl]
    simp only [values15_special_661_rightCert, IntervalCert.expr, eval]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_661_leftCert, values15_special_661_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_662_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3013 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (799 / 500 : Rat) (15981 / 10000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_662_rightCert : IntervalCert :=
  IntervalCert.add (3017 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (20173 / 10000 : Rat) (1009 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (101731 / 100000 : Rat) (5087 / 5000 : Rat) (IntervalCert.sqrt (25873 / 25000 : Rat) (207 / 200 : Rat) (IntervalCert.sqrt (107107 / 100000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_662 :
    values15 (662 : Fin 791) < values15 (663 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_662_leftCert values15_special_662_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_662_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_662_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (662 : Fin 791) = Real.sqrt 2 + values10 (25 : Fin 54) by rfl]
    simp only [values15_special_662_leftCert, IntervalCert.expr, eval]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (663 : Fin 791) = 1 + values13 (150 : Fin 264) by rfl]
    simp only [values15_special_662_rightCert, IntervalCert.expr, eval]
    rw [show values13 (150 : Fin 264) = 1 + values11 (4 : Fin 91) by rfl]
    rw [show values11 (4 : Fin 91) = Real.sqrt (values10 (4 : Fin 54)) by rfl]
    rw [show values10 (4 : Fin 54) = Real.sqrt (values9 (4 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_662_leftCert, values15_special_662_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_667_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (607 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1017 / 500 : Rat) (203493 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (10349 / 10000 : Rat) (64683 / 62500 : Rat) (IntervalCert.sqrt (107107 / 100000 : Rat) (2142151 / 2000000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))))

private def values15_special_667_rightCert : IntervalCert :=
  IntervalCert.add (30369 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (7391 / 4000 : Rat) (231 / 125 : Rat) (IntervalCert.add (17071 / 5000 : Rat) (683 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_667 :
    values15 (667 : Fin 791) < values15 (668 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_667_leftCert values15_special_667_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_667_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_667_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (667 : Fin 791) = 1 + values13 (154 : Fin 264) by rfl]
    simp only [values15_special_667_leftCert, IntervalCert.expr, eval]
    rw [show values13 (154 : Fin 264) = 1 + values11 (7 : Fin 91) by rfl]
    rw [show values11 (7 : Fin 91) = Real.sqrt (values10 (7 : Fin 54)) by rfl]
    rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (668 : Fin 791) = values5 (1 : Fin 5) + values9 (18 : Fin 33) by rfl]
    simp only [values15_special_667_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_667_leftCert, values15_special_667_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_668_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3037 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))

private def values15_special_668_rightCert : IntervalCert :=
  IntervalCert.add (761 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (10221 / 5000 : Rat) (409 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values15_special_668 :
    values15 (668 : Fin 791) < values15 (669 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_668_leftCert values15_special_668_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_668_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_668_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (668 : Fin 791) = values5 (1 : Fin 5) + values9 (18 : Fin 33) by rfl]
    simp only [values15_special_668_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (669 : Fin 791) = 1 + values13 (155 : Fin 264) by rfl]
    simp only [values15_special_668_rightCert, IntervalCert.expr, eval]
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_668_leftCert, values15_special_668_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_670_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3047 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1023 / 500 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values15_special_670_rightCert : IntervalCert :=
  IntervalCert.add (381 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_670 :
    values15 (670 : Fin 791) < values15 (671 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_670_leftCert values15_special_670_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_670_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_670_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (670 : Fin 791) = 1 + values13 (156 : Fin 264) by rfl]
    simp only [values15_special_670_leftCert, IntervalCert.expr, eval]
    rw [show values13 (156 : Fin 264) = Real.sqrt (values12 (148 : Fin 154)) by rfl]
    rw [show values12 (148 : Fin 154) = 1 + values10 (48 : Fin 54) by rfl]
    rw [show values10 (48 : Fin 54) = 1 + values8 (14 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (671 : Fin 791) = values6 (4 : Fin 8) + values8 (7 : Fin 20) by rfl]
    simp only [values15_special_670_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_670_leftCert, values15_special_670_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_671_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (15241 / 5000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_671_rightCert : IntervalCert :=
  IntervalCert.add (61 / 20 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (205019 / 100000 : Rat) (2051 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (10501901 / 10000000 : Rat) (5251 / 5000 : Rat) (IntervalCert.sqrt (13786241 / 12500000 : Rat) (11029 / 10000 : Rat) (IntervalCert.sqrt (121638683 / 100000000 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (73979847 / 50000000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (218920711 / 100000000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_671 :
    values15 (671 : Fin 791) < values15 (672 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_671_leftCert values15_special_671_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_671_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_671_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (671 : Fin 791) = values6 (4 : Fin 8) + values8 (7 : Fin 20) by rfl]
    simp only [values15_special_671_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (672 : Fin 791) = 1 + values13 (157 : Fin 264) by rfl]
    simp only [values15_special_671_rightCert, IntervalCert.expr, eval]
    rw [show values13 (157 : Fin 264) = 1 + values11 (9 : Fin 91) by rfl]
    rw [show values11 (9 : Fin 91) = Real.sqrt (values10 (9 : Fin 54)) by rfl]
    rw [show values10 (9 : Fin 54) = Real.sqrt (values9 (9 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_671_leftCert, values15_special_671_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_673_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3057 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (257 / 125 : Rat) (20567 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (5283 / 5000 : Rat) (3302 / 3125 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

private def values15_special_673_rightCert : IntervalCert :=
  IntervalCert.add (3067 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (165289 / 100000 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_673 :
    values15 (673 : Fin 791) < values15 (674 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_673_leftCert values15_special_673_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_673_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_673_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (673 : Fin 791) = 1 + values13 (158 : Fin 264) by rfl]
    simp only [values15_special_673_leftCert, IntervalCert.expr, eval]
    rw [show values13 (158 : Fin 264) = 1 + values11 (10 : Fin 91) by rfl]
    rw [show values11 (10 : Fin 91) = Real.sqrt (values10 (10 : Fin 54)) by rfl]
    rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (674 : Fin 791) = Real.sqrt 2 + values10 (26 : Fin 54) by rfl]
    simp only [values15_special_673_rightCert, IntervalCert.expr, eval]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_673_leftCert, values15_special_673_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_674_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (767 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (413 / 250 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values15_special_674_rightCert : IntervalCert :=
  IntervalCert.add (3071 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_674 :
    values15 (674 : Fin 791) < values15 (675 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_674_leftCert values15_special_674_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_674_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_674_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (674 : Fin 791) = Real.sqrt 2 + values10 (26 : Fin 54) by rfl]
    simp only [values15_special_674_leftCert, IntervalCert.expr, eval]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (675 : Fin 791) = 1 + values13 (159 : Fin 264) by rfl]
    simp only [values15_special_674_rightCert, IntervalCert.expr, eval]
    rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
    rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_674_leftCert, values15_special_674_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_676_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3091 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values15_special_676_rightCert : IntervalCert :=
  IntervalCert.add (387 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (26278 / 15625 : Rat) (841 / 500 : Rat) (IntervalCert.add (2828427 / 1000000 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_676 :
    values15 (676 : Fin 791) < values15 (677 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_676_leftCert values15_special_676_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_676_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_676_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (676 : Fin 791) = 1 + values13 (160 : Fin 264) by rfl]
    simp only [values15_special_676_leftCert, IntervalCert.expr, eval]
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (677 : Fin 791) = Real.sqrt 2 + values10 (27 : Fin 54) by rfl]
    simp only [values15_special_676_rightCert, IntervalCert.expr, eval]
    rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_676_leftCert, values15_special_676_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_677_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (30961 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1681 / 1000 : Rat) (8409 / 5000 : Rat) (IntervalCert.add (707 / 250 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values15_special_677_rightCert : IntervalCert :=
  IntervalCert.add (6193 / 2000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (41931 / 20000 : Rat) (2097 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1096557 / 1000000 : Rat) (5483 / 5000 : Rat) (IntervalCert.sqrt (601219 / 500000 : Rat) (481 / 400 : Rat) (IntervalCert.sqrt (722929 / 500000 : Rat) (723 / 500 : Rat) (IntervalCert.add (2090507 / 1000000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_677 :
    values15 (677 : Fin 791) < values15 (678 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_677_leftCert values15_special_677_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_677_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_677_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (677 : Fin 791) = Real.sqrt 2 + values10 (27 : Fin 54) by rfl]
    simp only [values15_special_677_leftCert, IntervalCert.expr, eval]
    rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (678 : Fin 791) = 1 + values13 (161 : Fin 264) by rfl]
    simp only [values15_special_677_rightCert, IntervalCert.expr, eval]
    rw [show values13 (161 : Fin 264) = 1 + values11 (13 : Fin 91) by rfl]
    rw [show values11 (13 : Fin 91) = Real.sqrt (values10 (13 : Fin 54)) by rfl]
    rw [show values10 (13 : Fin 54) = Real.sqrt (values9 (13 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_677_leftCert, values15_special_677_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_680_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3103 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1051 / 500 : Rat) (21029 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2757 / 2500 : Rat) (11028993 / 10000000 : Rat) (IntervalCert.sqrt (12163 / 10000 : Rat) (30409671 / 25000000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (92474809 / 62500000 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (547301779 / 250000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11892071151 / 10000000000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767766953 / 1250000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)))))))))))

private def values15_special_680_rightCert : IntervalCert :=
  IntervalCert.add (3107 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_680 :
    values15 (680 : Fin 791) < values15 (681 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_680_leftCert values15_special_680_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_680_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_680_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (680 : Fin 791) = 1 + values13 (163 : Fin 264) by rfl]
    simp only [values15_special_680_leftCert, IntervalCert.expr, eval]
    rw [show values13 (163 : Fin 264) = 1 + values11 (14 : Fin 91) by rfl]
    rw [show values11 (14 : Fin 91) = Real.sqrt (values10 (14 : Fin 54)) by rfl]
    rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (681 : Fin 791) = values7 (6 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_680_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_680_leftCert, values15_special_680_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_681_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (777 / 250 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values15_special_681_rightCert : IntervalCert :=
  IntervalCert.add (779 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (5291 / 2500 : Rat) (2117 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (55823 / 50000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_681 :
    values15 (681 : Fin 791) < values15 (682 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_681_leftCert values15_special_681_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_681_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_681_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (681 : Fin 791) = values7 (6 : Fin 13) + values7 (6 : Fin 13) by rfl]
    simp only [values15_special_681_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (682 : Fin 791) = 1 + values13 (164 : Fin 264) by rfl]
    simp only [values15_special_681_rightCert, IntervalCert.expr, eval]
    rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
    rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_681_leftCert, values15_special_681_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_683_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1567 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2133 / 1000 : Rat) (21339 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (5669 / 5000 : Rat) (113387 / 100000 : Rat) (IntervalCert.sqrt (1607 / 1250 : Rat) (25713 / 20000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_683_rightCert : IntervalCert :=
  IntervalCert.add (1573 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values15_special_683 :
    values15 (683 : Fin 791) < values15 (684 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_683_leftCert values15_special_683_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_683_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_683_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (683 : Fin 791) = 1 + values13 (165 : Fin 264) by rfl]
    simp only [values15_special_683_leftCert, IntervalCert.expr, eval]
    rw [show values13 (165 : Fin 264) = 1 + values11 (16 : Fin 91) by rfl]
    rw [show values11 (16 : Fin 91) = Real.sqrt (values10 (16 : Fin 54)) by rfl]
    rw [show values10 (16 : Fin 54) = Real.sqrt (values9 (16 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (684 : Fin 791) = Real.sqrt 2 + values10 (28 : Fin 54) by rfl]
    simp only [values15_special_683_rightCert, IntervalCert.expr, eval]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_683_leftCert, values15_special_683_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_684_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))

private def values15_special_684_rightCert : IntervalCert :=
  IntervalCert.add (3147 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_684 :
    values15 (684 : Fin 791) < values15 (685 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_684_leftCert values15_special_684_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_684_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_684_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (684 : Fin 791) = Real.sqrt 2 + values10 (28 : Fin 54) by rfl]
    simp only [values15_special_684_leftCert, IntervalCert.expr, eval]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (685 : Fin 791) = 1 + values13 (166 : Fin 264) by rfl]
    simp only [values15_special_684_rightCert, IntervalCert.expr, eval]
    rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
    rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_684_leftCert, values15_special_684_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_690_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (799 / 250 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (439 / 200 : Rat) (10979 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (11957 / 10000 : Rat) (59787 / 50000 : Rat) (IntervalCert.sqrt (14297 / 10000 : Rat) (142979 / 100000 : Rat) (IntervalCert.add (10221 / 5000 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_690_rightCert : IntervalCert :=
  IntervalCert.add (16 / 5 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (178583 / 100000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_690 :
    values15 (690 : Fin 791) < values15 (691 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_690_leftCert values15_special_690_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_690_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_690_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (690 : Fin 791) = 1 + values13 (171 : Fin 264) by rfl]
    simp only [values15_special_690_leftCert, IntervalCert.expr, eval]
    rw [show values13 (171 : Fin 264) = 1 + values11 (20 : Fin 91) by rfl]
    rw [show values11 (20 : Fin 91) = Real.sqrt (values10 (20 : Fin 54)) by rfl]
    rw [show values10 (20 : Fin 54) = Real.sqrt (values9 (20 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (691 : Fin 791) = Real.sqrt 2 + values10 (29 : Fin 54) by rfl]
    simp only [values15_special_690_rightCert, IntervalCert.expr, eval]
    rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_690_leftCert, values15_special_690_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_691_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (32001 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (357 / 200 : Rat) (22323 / 12500 : Rat) (IntervalCert.add (3189 / 1000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (5473 / 2500 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))

private def values15_special_691_rightCert : IntervalCert :=
  IntervalCert.add (1601 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (2753 / 1250 : Rat) (2203 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (120243 / 100000 : Rat) (481 / 400 : Rat) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_691 :
    values15 (691 : Fin 791) < values15 (692 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_691_leftCert values15_special_691_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_691_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_691_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (691 : Fin 791) = Real.sqrt 2 + values10 (29 : Fin 54) by rfl]
    simp only [values15_special_691_leftCert, IntervalCert.expr, eval]
    rw [show values10 (29 : Fin 54) = Real.sqrt (values9 (29 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (692 : Fin 791) = 1 + values13 (172 : Fin 264) by rfl]
    simp only [values15_special_691_rightCert, IntervalCert.expr, eval]
    rw [show values13 (172 : Fin 264) = 1 + values11 (21 : Fin 91) by rfl]
    rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_691_leftCert, values15_special_691_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_692_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3203 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1101 / 500 : Rat) (881 / 400 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1503 / 1250 : Rat) (30061 / 25000 : Rat) (IntervalCert.sqrt (7229 / 5000 : Rat) (72293 / 50000 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values15_special_692_rightCert : IntervalCert :=
  IntervalCert.add (3211 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_692 :
    values15 (692 : Fin 791) < values15 (693 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_692_leftCert values15_special_692_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_692_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_692_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (692 : Fin 791) = 1 + values13 (172 : Fin 264) by rfl]
    simp only [values15_special_692_leftCert, IntervalCert.expr, eval]
    rw [show values13 (172 : Fin 264) = 1 + values11 (21 : Fin 91) by rfl]
    rw [show values11 (21 : Fin 91) = Real.sqrt (values10 (21 : Fin 54)) by rfl]
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (693 : Fin 791) = values6 (4 : Fin 8) + values8 (9 : Fin 20) by rfl]
    simp only [values15_special_692_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_692_leftCert, values15_special_692_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_693_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (803 / 250 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_693_rightCert : IntervalCert :=
  IntervalCert.add (402 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (22163 / 10000 : Rat) (2217 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_693 :
    values15 (693 : Fin 791) < values15 (694 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_693_leftCert values15_special_693_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_693_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_693_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (693 : Fin 791) = values6 (4 : Fin 8) + values8 (9 : Fin 20) by rfl]
    simp only [values15_special_693_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (694 : Fin 791) = 1 + values13 (173 : Fin 264) by rfl]
    simp only [values15_special_693_rightCert, IntervalCert.expr, eval]
    rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
    rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_693_leftCert, values15_special_693_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_698_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1123 / 500 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values15_special_698_rightCert : IntervalCert :=
  IntervalCert.add (3261 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_698 :
    values15 (698 : Fin 791) < values15 (699 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_698_leftCert values15_special_698_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_698_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_698_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (698 : Fin 791) = 1 + values13 (177 : Fin 264) by rfl]
    simp only [values15_special_698_leftCert, IntervalCert.expr, eval]
    rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
    rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (699 : Fin 791) = Real.sqrt 2 + values10 (30 : Fin 54) by rfl]
    simp only [values15_special_698_rightCert, IntervalCert.expr, eval]
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_698_leftCert, values15_special_698_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_699_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1631 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values15_special_699_rightCert : IntervalCert :=
  IntervalCert.add (408 / 125 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (22641 / 10000 : Rat) (453 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (63207 / 50000 : Rat) (6321 / 5000 : Rat) (IntervalCert.sqrt (31961 / 20000 : Rat) (15981 / 10000 : Rat) (IntervalCert.add (255377 / 100000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_699 :
    values15 (699 : Fin 791) < values15 (700 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_699_leftCert values15_special_699_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_699_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_699_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (699 : Fin 791) = Real.sqrt 2 + values10 (30 : Fin 54) by rfl]
    simp only [values15_special_699_leftCert, IntervalCert.expr, eval]
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (700 : Fin 791) = 1 + values13 (178 : Fin 264) by rfl]
    simp only [values15_special_699_rightCert, IntervalCert.expr, eval]
    rw [show values13 (178 : Fin 264) = 1 + values11 (25 : Fin 91) by rfl]
    rw [show values11 (25 : Fin 91) = Real.sqrt (values10 (25 : Fin 54)) by rfl]
    rw [show values10 (25 : Fin 54) = Real.sqrt (values9 (25 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_699_leftCert, values15_special_699_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_702_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (32857 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (457 / 200 : Rat) (45713 / 20000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (3214121 / 2500000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (16528917 / 10000000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27320509 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values15_special_702_rightCert : IntervalCert :=
  IntervalCert.add (16429 / 5000 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_702 :
    values15 (702 : Fin 791) < values15 (703 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_702_leftCert values15_special_702_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_702_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_702_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (702 : Fin 791) = 1 + values13 (180 : Fin 264) by rfl]
    simp only [values15_special_702_leftCert, IntervalCert.expr, eval]
    rw [show values13 (180 : Fin 264) = 1 + values11 (26 : Fin 91) by rfl]
    rw [show values11 (26 : Fin 91) = Real.sqrt (values10 (26 : Fin 54)) by rfl]
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (703 : Fin 791) = values6 (4 : Fin 8) + values8 (10 : Fin 20) by rfl]
    simp only [values15_special_702_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_702_leftCert, values15_special_702_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_703_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1643 / 500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_703_rightCert : IntervalCert :=
  IntervalCert.add (412 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (2871 / 1250 : Rat) (2297 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (129683 / 100000 : Rat) (32421 / 25000 : Rat) (IntervalCert.sqrt (168179 / 100000 : Rat) (1681793 / 1000000 : Rat) (IntervalCert.add (141421 / 50000 : Rat) (1767767 / 625000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values15_special_703 :
    values15 (703 : Fin 791) < values15 (704 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_703_leftCert values15_special_703_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_703_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_703_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (703 : Fin 791) = values6 (4 : Fin 8) + values8 (10 : Fin 20) by rfl]
    simp only [values15_special_703_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (704 : Fin 791) = 1 + values13 (181 : Fin 264) by rfl]
    simp only [values15_special_703_rightCert, IntervalCert.expr, eval]
    rw [show values13 (181 : Fin 264) = 1 + values11 (27 : Fin 91) by rfl]
    rw [show values11 (27 : Fin 91) = Real.sqrt (values10 (27 : Fin 54)) by rfl]
    rw [show values10 (27 : Fin 54) = Real.sqrt (values9 (27 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_703_leftCert, values15_special_703_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_716_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3459 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1229 / 500 : Rat) (4917 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values15_special_716_rightCert : IntervalCert :=
  IntervalCert.add (433 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_716 :
    values15 (716 : Fin 791) < values15 (717 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_716_leftCert values15_special_716_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_716_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_716_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (716 : Fin 791) = 1 + values13 (193 : Fin 264) by rfl]
    simp only [values15_special_716_leftCert, IntervalCert.expr, eval]
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (717 : Fin 791) = values6 (4 : Fin 8) + values8 (11 : Fin 20) by rfl]
    simp only [values15_special_716_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_716_leftCert, values15_special_716_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_717_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (17321 / 5000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values15_special_717_rightCert : IntervalCert :=
  IntervalCert.add (693 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (24653 / 10000 : Rat) (1233 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (146533 / 100000 : Rat) (7327 / 5000 : Rat) (IntervalCert.add (1342 / 625 : Rat) (21473 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_717 :
    values15 (717 : Fin 791) < values15 (718 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_717_leftCert values15_special_717_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_717_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_717_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (717 : Fin 791) = values6 (4 : Fin 8) + values8 (11 : Fin 20) by rfl]
    simp only [values15_special_717_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (718 : Fin 791) = 1 + values13 (194 : Fin 264) by rfl]
    simp only [values15_special_717_rightCert, IntervalCert.expr, eval]
    rw [show values13 (194 : Fin 264) = 1 + values11 (35 : Fin 91) by rfl]
    rw [show values11 (35 : Fin 91) = Real.sqrt (values10 (35 : Fin 54)) by rfl]
    rw [show values10 (35 : Fin 54) = 1 + values8 (4 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_717_leftCert, values15_special_717_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_730_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1807 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2613 / 1000 : Rat) (3267 / 1250 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (3227 / 2000 : Rat) (20169 / 12500 : Rat) (IntervalCert.add (13017 / 5000 : Rat) (260343 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values15_special_730_rightCert : IntervalCert :=
  IntervalCert.add (73 / 20 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (559 / 250 : Rat) (2237 / 1000 : Rat) (IntervalCert.add (49999 / 10000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values15_special_730 :
    values15 (730 : Fin 791) < values15 (731 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_730_leftCert values15_special_730_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_730_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_730_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (730 : Fin 791) = 1 + values13 (206 : Fin 264) by rfl]
    simp only [values15_special_730_leftCert, IntervalCert.expr, eval]
    rw [show values13 (206 : Fin 264) = 1 + values11 (43 : Fin 91) by rfl]
    rw [show values11 (43 : Fin 91) = Real.sqrt (values10 (43 : Fin 54)) by rfl]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (731 : Fin 791) = Real.sqrt 2 + values10 (37 : Fin 54) by rfl]
    simp only [values15_special_730_rightCert, IntervalCert.expr, eval]
    rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_730_leftCert, values15_special_730_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_731_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3651 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (559 / 250 : Rat) (22361 / 10000 : Rat) (IntervalCert.add (49999 / 10000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))

private def values15_special_731_rightCert : IntervalCert :=
  IntervalCert.add (2283 / 625 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (265289 / 100000 : Rat) (2653 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (4132229 / 2500000 : Rat) (16529 / 10000 : Rat) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_731 :
    values15 (731 : Fin 791) < values15 (732 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_731_leftCert values15_special_731_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_731_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_731_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (731 : Fin 791) = Real.sqrt 2 + values10 (37 : Fin 54) by rfl]
    simp only [values15_special_731_leftCert, IntervalCert.expr, eval]
    rw [show values10 (37 : Fin 54) = Real.sqrt (values9 (32 : Fin 33)) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (732 : Fin 791) = 1 + values13 (207 : Fin 264) by rfl]
    simp only [values15_special_731_rightCert, IntervalCert.expr, eval]
    rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
    rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_731_leftCert, values15_special_731_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_748_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4011 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (301 / 100 : Rat) (30109 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (5027 / 2500 : Rat) (201089 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (3159 / 3125 : Rat) (10108893 / 10000000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (20437943 / 20000000 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (1044273783 / 1000000000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1090507733 / 1000000000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (11892071151 / 10000000000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767766953 / 1250000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000000001 / 100000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000000001 / 1000000000000 : Rat)))))))))))

private def values15_special_748_rightCert : IntervalCert :=
  IntervalCert.add (4017 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.add (13017 / 5000 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_748 :
    values15 (748 : Fin 791) < values15 (749 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_748_leftCert values15_special_748_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_748_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_748_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (748 : Fin 791) = 1 + values13 (223 : Fin 264) by rfl]
    simp only [values15_special_748_leftCert, IntervalCert.expr, eval]
    rw [show values13 (223 : Fin 264) = 1 + values11 (52 : Fin 91) by rfl]
    rw [show values11 (52 : Fin 91) = 1 + values9 (1 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (749 : Fin 791) = Real.sqrt 2 + values10 (43 : Fin 54) by rfl]
    simp only [values15_special_748_rightCert, IntervalCert.expr, eval]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_748_leftCert, values15_special_748_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_749_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2009 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.add (2603 / 1000 : Rat) (5207 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values15_special_749_rightCert : IntervalCert :=
  IntervalCert.add (4021 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (15109 / 5000 : Rat) (1511 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (202189 / 100000 : Rat) (20219 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1021897 / 1000000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values15_special_749 :
    values15 (749 : Fin 791) < values15 (750 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_749_leftCert values15_special_749_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_749_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_749_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (749 : Fin 791) = Real.sqrt 2 + values10 (43 : Fin 54) by rfl]
    simp only [values15_special_749_leftCert, IntervalCert.expr, eval]
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (750 : Fin 791) = 1 + values13 (224 : Fin 264) by rfl]
    simp only [values15_special_749_rightCert, IntervalCert.expr, eval]
    rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
    rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_749_leftCert, values15_special_749_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_760_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4237 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (809 / 250 : Rat) (32361 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (111803 / 50000 : Rat) (223607 / 100000 : Rat) (IntervalCert.add (499999 / 100000 : Rat) (5000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.sqrt (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))

private def values15_special_760_rightCert : IntervalCert :=
  IntervalCert.add (2121 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values15_special_760 :
    values15 (760 : Fin 791) < values15 (761 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_760_leftCert values15_special_760_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_760_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_760_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (760 : Fin 791) = 1 + values13 (234 : Fin 264) by rfl]
    simp only [values15_special_760_leftCert, IntervalCert.expr, eval]
    rw [show values13 (234 : Fin 264) = 1 + values11 (62 : Fin 91) by rfl]
    rw [show values11 (62 : Fin 91) = Real.sqrt (values10 (53 : Fin 54)) by rfl]
    rw [show values10 (53 : Fin 54) = 1 + values8 (19 : Fin 20) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (761 : Fin 791) = Real.sqrt 2 + values10 (45 : Fin 54) by rfl]
    simp only [values15_special_760_rightCert, IntervalCert.expr, eval]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_760_leftCert, values15_special_760_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values15_special_761_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4243 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.add (707 / 250 : Rat) (5657 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values15_special_761_rightCert : IntervalCert :=
  IntervalCert.add (2123 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (6493 / 2000 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (280813 / 125000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (12465047 / 10000000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values15_special_761 :
    values15 (761 : Fin 791) < values15 (762 : Fin 791) := by
  refine IntervalCert.lt_of_gap values15_special_761_leftCert values15_special_761_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values15_special_761_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values15_special_761_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values15 (761 : Fin 791) = Real.sqrt 2 + values10 (45 : Fin 54) by rfl]
    simp only [values15_special_761_leftCert, IntervalCert.expr, eval]
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values15 (762 : Fin 791) = 1 + values13 (235 : Fin 264) by rfl]
    simp only [values15_special_761_rightCert, IntervalCert.expr, eval]
    rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
    rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values15_special_761_leftCert, values15_special_761_rightCert, IntervalCert.upper, IntervalCert.lower]

end Expr
end A158415
end LeanProofs
