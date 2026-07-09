import LeanProofs.A158415FourteenTable
import LeanProofs.A158415IntervalCert

/-!
# Size-fourteen interval order certificates for OEIS A158415

This generated module replaces the large hand-expanded rational-bound
ladders for the exceptional adjacent comparisons in `values14` with
compact interval certificates checked by one soundness theorem.
-/

namespace LeanProofs
namespace A158415
namespace Expr

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def values14_special_249_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (3999 / 1000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_249_rightCert : IntervalCert :=
  IntervalCert.add (2001 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (10013 / 10000 : Rat) (501 / 500 : Rat) (IntervalCert.sqrt (10027 / 10000 : Rat) (1003 / 1000 : Rat) (IntervalCert.sqrt (50271 / 50000 : Rat) (503 / 500 : Rat) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

set_option linter.unusedTactic false in
theorem values14_special_249 :
    values14 (249 : Fin 455) < values14 (250 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_249_leftCert values14_special_249_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_249_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_249_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (249 : Fin 455) = Real.sqrt (values13 (249 : Fin 264)) by rfl]
    simp only [values14_special_249_leftCert, IntervalCert.expr, eval]
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (250 : Fin 455) = 1 + values12 (1 : Fin 154) by rfl]
    simp only [values14_special_249_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_249_leftCert, values14_special_249_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_254_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (20109 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (101 / 100 : Rat) (101089 / 100000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat))))))))))))

private def values14_special_254_rightCert : IntervalCert :=
  IntervalCert.sqrt (2011 / 1000 : Rat) (100 : Rat) (IntervalCert.add (20221 / 5000 : Rat) (809 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (304427 / 100000 : Rat) (30443 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_254 :
    values14 (254 : Fin 455) < values14 (255 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_254_leftCert values14_special_254_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_254_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_254_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (254 : Fin 455) = 1 + values12 (5 : Fin 154) by rfl]
    simp only [values14_special_254_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    simp only [values14_special_254_rightCert, IntervalCert.expr, eval]
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_254_leftCert, values14_special_254_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_255_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (20111 / 10000 : Rat) (IntervalCert.add (1011 / 250 : Rat) (40443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (15221 / 5000 : Rat) (76107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (204427 / 100000 : Rat) (1022137 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1044273 / 1000000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_255_rightCert : IntervalCert :=
  IntervalCert.add (2013 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (5069 / 5000 : Rat) (507 / 500 : Rat) (IntervalCert.sqrt (10279 / 10000 : Rat) (257 / 250 : Rat) (IntervalCert.sqrt (5283 / 5000 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_255 :
    values14 (255 : Fin 455) < values14 (256 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_255_leftCert values14_special_255_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_255_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_255_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    simp only [values14_special_255_leftCert, IntervalCert.expr, eval]
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (256 : Fin 455) = 1 + values12 (6 : Fin 154) by rfl]
    simp only [values14_special_255_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_255_leftCert, values14_special_255_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_258_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1011 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1021 / 1000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat))))))))))))

private def values14_special_258_rightCert : IntervalCert :=
  IntervalCert.sqrt (809 / 400 : Rat) (100 : Rat) (IntervalCert.add (4090507 / 1000000 : Rat) (4091 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (30905077 / 10000000 : Rat) (15453 / 5000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (209050773 / 100000000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (272626933 / 250000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_258 :
    values14 (258 : Fin 455) < values14 (259 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_258_leftCert values14_special_258_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_258_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_258_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (258 : Fin 455) = 1 + values12 (8 : Fin 154) by rfl]
    simp only [values14_special_258_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    simp only [values14_special_258_rightCert, IntervalCert.expr, eval]
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_258_leftCert, values14_special_258_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_259_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2023 / 1000 : Rat) (IntervalCert.add (409 / 100 : Rat) (4091 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (6181 / 2000 : Rat) (15453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2090507 / 1000000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_259_rightCert : IntervalCert :=
  IntervalCert.add (20247 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (51239 / 50000 : Rat) (41 / 40 : Rat) (IntervalCert.sqrt (105019 / 100000 : Rat) (5251 / 5000 : Rat) (IntervalCert.sqrt (86164 / 78125 : Rat) (11029 / 10000 : Rat) (IntervalCert.sqrt (3040967 / 2500000 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (14795969 / 10000000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_259 :
    values14 (259 : Fin 455) < values14 (260 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_259_leftCert values14_special_259_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_259_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_259_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    simp only [values14_special_259_leftCert, IntervalCert.expr, eval]
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (260 : Fin 455) = 1 + values12 (9 : Fin 154) by rfl]
    simp only [values14_special_259_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_259_leftCert, values14_special_259_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_262_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (407 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (517 / 500 : Rat) (103493 / 100000 : Rat) (IntervalCert.sqrt (1071 / 1000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14_special_262_rightCert : IntervalCert :=
  IntervalCert.sqrt (509 / 250 : Rat) (100 : Rat) (IntervalCert.add (2073 / 500 : Rat) (4147 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (15731 / 5000 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_262 :
    values14 (262 : Fin 455) < values14 (263 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_262_leftCert values14_special_262_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_262_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_262_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (262 : Fin 455) = 1 + values12 (11 : Fin 154) by rfl]
    simp only [values14_special_262_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    simp only [values14_special_262_rightCert, IntervalCert.expr, eval]
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_262_leftCert, values14_special_262_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_263_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2037 / 1000 : Rat) (IntervalCert.add (2073 / 500 : Rat) (4147 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (15731 / 5000 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_263_rightCert : IntervalCert :=
  IntervalCert.add (511 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_263 :
    values14 (263 : Fin 455) < values14 (264 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_263_leftCert values14_special_263_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_263_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_263_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    simp only [values14_special_263_leftCert, IntervalCert.expr, eval]
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    simp only [values14_special_263_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_263_leftCert, values14_special_263_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_264_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (409 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_264_rightCert : IntervalCert :=
  IntervalCert.sqrt (1023 / 500 : Rat) (100 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (419 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_264 :
    values14 (264 : Fin 455) < values14 (265 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_264_leftCert values14_special_264_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_264_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_264_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    simp only [values14_special_264_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    simp only [values14_special_264_rightCert, IntervalCert.expr, eval]
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_264_leftCert, values14_special_264_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_265_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_265_rightCert : IntervalCert :=
  IntervalCert.add (20471 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (26179 / 25000 : Rat) (131 / 125 : Rat) (IntervalCert.sqrt (21931 / 20000 : Rat) (1097 / 1000 : Rat) (IntervalCert.sqrt (120243 / 100000 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_265 :
    values14 (265 : Fin 455) < values14 (266 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_265_leftCert values14_special_265_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_265_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_265_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    simp only [values14_special_265_leftCert, IntervalCert.expr, eval]
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (266 : Fin 455) = 1 + values12 (13 : Fin 154) by rfl]
    simp only [values14_special_265_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_265_leftCert, values14_special_265_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_270_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (259 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14_special_270_rightCert : IntervalCert :=
  IntervalCert.sqrt (2077 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_270 :
    values14 (270 : Fin 455) < values14 (271 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_270_leftCert values14_special_270_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_270_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_270_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (270 : Fin 455) = 1 + values12 (17 : Fin 154) by rfl]
    simp only [values14_special_270_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    simp only [values14_special_270_rightCert, IntervalCert.expr, eval]
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_270_leftCert, values14_special_270_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_271_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1039 / 500 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_271_rightCert : IntervalCert :=
  IntervalCert.add (20797 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13497 / 12500 : Rat) (27 / 25 : Rat) (IntervalCert.sqrt (11659 / 10000 : Rat) (583 / 500 : Rat) (IntervalCert.sqrt (1359323 / 1000000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (92387953 / 50000000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (85355339 / 25000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1207106781 / 500000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (14142135623 / 10000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999999 / 10000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_271 :
    values14 (271 : Fin 455) < values14 (272 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_271_leftCert values14_special_271_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_271_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_271_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    simp only [values14_special_271_leftCert, IntervalCert.expr, eval]
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (272 : Fin 455) = 1 + values12 (18 : Fin 154) by rfl]
    simp only [values14_special_271_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_271_leftCert, values14_special_271_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_275_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2097 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (137 / 125 : Rat) (5483 / 5000 : Rat) (IntervalCert.sqrt (601 / 500 : Rat) (481 / 400 : Rat) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14_special_275_rightCert : IntervalCert :=
  IntervalCert.sqrt (2101 / 1000 : Rat) (100 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (883 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_275 :
    values14 (275 : Fin 455) < values14 (276 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_275_leftCert values14_special_275_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_275_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_275_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (275 : Fin 455) = 1 + values12 (21 : Fin 154) by rfl]
    simp only [values14_special_275_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    simp only [values14_special_275_rightCert, IntervalCert.expr, eval]
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_275_leftCert, values14_special_275_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_276_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (21011 / 10000 : Rat) (IntervalCert.add (2207 / 500 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (17071 / 5000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (241421 / 100000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_276_rightCert : IntervalCert :=
  IntervalCert.add (5257 / 2500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (110289 / 100000 : Rat) (1103 / 1000 : Rat) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_276 :
    values14 (276 : Fin 455) < values14 (277 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_276_leftCert values14_special_276_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_276_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_276_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    simp only [values14_special_276_leftCert, IntervalCert.expr, eval]
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (277 : Fin 455) = 1 + values12 (22 : Fin 154) by rfl]
    simp only [values14_special_276_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_276_leftCert, values14_special_276_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_281_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (213387 / 100000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1133 / 1000 : Rat) (226773 / 200000 : Rat) (IntervalCert.sqrt (257 / 200 : Rat) (1285649 / 1000000 : Rat) (IntervalCert.sqrt (413 / 250 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values14_special_281_rightCert : IntervalCert :=
  IntervalCert.sqrt (42679 / 20000 : Rat) (100 : Rat) (IntervalCert.add (455377 / 100000 : Rat) (2277 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3553773 / 1000000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (25537739 / 10000000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_281 :
    values14 (281 : Fin 455) < values14 (282 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_281_leftCert values14_special_281_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_281_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_281_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (281 : Fin 455) = 1 + values12 (26 : Fin 154) by rfl]
    simp only [values14_special_281_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    simp only [values14_special_281_rightCert, IntervalCert.expr, eval]
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_281_leftCert, values14_special_281_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_282_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1067 / 500 : Rat) (IntervalCert.add (4553 / 1000 : Rat) (22769 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (35537 / 10000 : Rat) (177689 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (1276887 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77688699 / 50000000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (241421357 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))

private def values14_special_282_rightCert : IntervalCert :=
  IntervalCert.add (21347 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (104427 / 100000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_282 :
    values14 (282 : Fin 455) < values14 (283 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_282_leftCert values14_special_282_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_282_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_282_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    simp only [values14_special_282_leftCert, IntervalCert.expr, eval]
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14_special_282_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_282_leftCert, values14_special_282_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_283_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (427 / 200 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14_special_283_rightCert : IntervalCert :=
  IntervalCert.add (1069 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (11387 / 10000 : Rat) (1139 / 1000 : Rat) (IntervalCert.sqrt (1621 / 1250 : Rat) (1297 / 1000 : Rat) (IntervalCert.sqrt (16817 / 10000 : Rat) (841 / 500 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_283 :
    values14 (283 : Fin 455) < values14 (284 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_283_leftCert values14_special_283_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_283_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_283_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14_special_283_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (284 : Fin 455) = 1 + values12 (27 : Fin 154) by rfl]
    simp only [values14_special_283_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_283_leftCert, values14_special_283_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_287_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1083 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (233 / 200 : Rat) (116591 / 100000 : Rat) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_287_rightCert : IntervalCert :=
  IntervalCert.sqrt (87 / 40 : Rat) (100 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_287 :
    values14 (287 : Fin 455) < values14 (288 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_287_leftCert values14_special_287_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_287_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_287_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (287 : Fin 455) = 1 + values12 (30 : Fin 154) by rfl]
    simp only [values14_special_287_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    simp only [values14_special_287_rightCert, IntervalCert.expr, eval]
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_287_leftCert, values14_special_287_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_288_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (272 / 125 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_288_rightCert : IntervalCert :=
  IntervalCert.add (2181 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_288 :
    values14 (288 : Fin 455) < values14 (289 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_288_leftCert values14_special_288_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_288_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_288_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    simp only [values14_special_288_leftCert, IntervalCert.expr, eval]
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    simp only [values14_special_288_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_288_leftCert, values14_special_288_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_289_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1091 / 500 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))

private def values14_special_289_rightCert : IntervalCert :=
  IntervalCert.add (2189 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_289 :
    values14 (289 : Fin 455) < values14 (290 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_289_leftCert values14_special_289_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_289_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_289_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    simp only [values14_special_289_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (290 : Fin 455) = 1 + values12 (31 : Fin 154) by rfl]
    simp only [values14_special_289_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_289_leftCert, values14_special_289_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_292_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (549 / 250 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (239 / 200 : Rat) (5979 / 5000 : Rat) (IntervalCert.sqrt (1429 / 1000 : Rat) (7149 / 5000 : Rat) (IntervalCert.add (511 / 250 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14_special_292_rightCert : IntervalCert :=
  IntervalCert.sqrt (2197 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_292 :
    values14 (292 : Fin 455) < values14 (293 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_292_leftCert values14_special_292_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_292_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_292_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (292 : Fin 455) = 1 + values12 (33 : Fin 154) by rfl]
    simp only [values14_special_292_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    simp only [values14_special_292_rightCert, IntervalCert.expr, eval]
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_292_leftCert, values14_special_292_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_293_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1099 / 500 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_293_rightCert : IntervalCert :=
  IntervalCert.add (1101 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1503 / 1250 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (7229 / 5000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_293 :
    values14 (293 : Fin 455) < values14 (294 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_293_leftCert values14_special_293_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_293_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_293_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    simp only [values14_special_293_leftCert, IntervalCert.expr, eval]
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (294 : Fin 455) = 1 + values12 (34 : Fin 154) by rfl]
    simp only [values14_special_293_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_293_leftCert, values14_special_293_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_295_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (11053 / 5000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (121 / 100 : Rat) (121051 / 100000 : Rat) (IntervalCert.sqrt (293 / 200 : Rat) (732667 / 500000 : Rat) (IntervalCert.add (2147 / 1000 : Rat) (2147203 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (717 / 625 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))))

private def values14_special_295_rightCert : IntervalCert :=
  IntervalCert.add (2211 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_295 :
    values14 (295 : Fin 455) < values14 (296 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_295_leftCert values14_special_295_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_295_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_295_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (295 : Fin 455) = 1 + values12 (35 : Fin 154) by rfl]
    simp only [values14_special_295_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    simp only [values14_special_295_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_295_leftCert, values14_special_295_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_296_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (553 / 250 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14_special_296_rightCert : IntervalCert :=
  IntervalCert.add (277 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_296 :
    values14 (296 : Fin 455) < values14 (297 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_296_leftCert values14_special_296_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_296_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_296_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    simp only [values14_special_296_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (297 : Fin 455) = 1 + values12 (36 : Fin 154) by rfl]
    simp only [values14_special_296_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_296_leftCert, values14_special_296_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_299_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (89 / 40 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (153 / 125 : Rat) (12243 / 10000 : Rat) (IntervalCert.sqrt (3747 / 2500 : Rat) (14989 / 10000 : Rat) (IntervalCert.add (4493 / 2000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_299_rightCert : IntervalCert :=
  IntervalCert.add (2233 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_299 :
    values14 (299 : Fin 455) < values14 (300 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_299_leftCert values14_special_299_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_299_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_299_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (299 : Fin 455) = 1 + values12 (38 : Fin 154) by rfl]
    simp only [values14_special_299_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    simp only [values14_special_299_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_299_leftCert, values14_special_299_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_300_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4467 / 2000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14_special_300_rightCert : IntervalCert :=
  IntervalCert.add (1396 / 625 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (123363 / 100000 : Rat) (617 / 500 : Rat) (IntervalCert.sqrt (76093 / 50000 : Rat) (761 / 500 : Rat) (IntervalCert.add (231607 / 100000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_300 :
    values14 (300 : Fin 455) < values14 (301 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_300_leftCert values14_special_300_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_300_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_300_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    simp only [values14_special_300_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    simp only [values14_special_300_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_300_leftCert, values14_special_300_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_301_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1117 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1233 / 1000 : Rat) (12337 / 10000 : Rat) (IntervalCert.sqrt (1521 / 1000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_301_rightCert : IntervalCert :=
  IntervalCert.sqrt (559 / 250 : Rat) (100 : Rat) (IntervalCert.add (49999 / 10000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_301 :
    values14 (301 : Fin 455) < values14 (302 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_301_leftCert values14_special_301_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_301_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_301_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    simp only [values14_special_301_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    simp only [values14_special_301_rightCert, IntervalCert.expr, eval]
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_301_leftCert, values14_special_301_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_302_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2237 / 1000 : Rat) (IntervalCert.add (4999 / 1000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_302_rightCert : IntervalCert :=
  IntervalCert.add (1123 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_302 :
    values14 (302 : Fin 455) < values14 (303 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_302_leftCert values14_special_302_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_302_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_302_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    simp only [values14_special_302_leftCert, IntervalCert.expr, eval]
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (303 : Fin 455) = 1 + values12 (40 : Fin 154) by rfl]
    simp only [values14_special_302_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_302_leftCert, values14_special_302_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_306_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2271 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (127 / 100 : Rat) (12703 / 10000 : Rat) (IntervalCert.sqrt (1613 / 1000 : Rat) (2017 / 1250 : Rat) (IntervalCert.add (2603 / 1000 : Rat) (5207 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14_special_306_rightCert : IntervalCert :=
  IntervalCert.sqrt (2277 / 1000 : Rat) (100 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (519 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_306 :
    values14 (306 : Fin 455) < values14 (307 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_306_leftCert values14_special_306_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_306_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_306_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (306 : Fin 455) = 1 + values12 (43 : Fin 154) by rfl]
    simp only [values14_special_306_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    simp only [values14_special_306_rightCert, IntervalCert.expr, eval]
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_306_leftCert, values14_special_306_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_307_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1139 / 500 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (518921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (523651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (3986509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat)))))))))

private def values14_special_307_rightCert : IntervalCert :=
  IntervalCert.add (22797 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_307 :
    values14 (307 : Fin 455) < values14 (308 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_307_leftCert values14_special_307_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_307_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_307_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    simp only [values14_special_307_leftCert, IntervalCert.expr, eval]
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    simp only [values14_special_307_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_307_leftCert, values14_special_307_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_308_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))))))

private def values14_special_308_rightCert : IntervalCert :=
  IntervalCert.add (457 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (643 / 500 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_308 :
    values14 (308 : Fin 455) < values14 (309 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_308_leftCert values14_special_308_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_308_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_308_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    simp only [values14_special_308_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (309 : Fin 455) = 1 + values12 (44 : Fin 154) by rfl]
    simp only [values14_special_308_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_308_leftCert, values14_special_308_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_312_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1163 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (53 / 40 : Rat) (13259 / 10000 : Rat) (IntervalCert.sqrt (1757 / 1000 : Rat) (879 / 500 : Rat) (IntervalCert.add (309 / 100 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (4181 / 2000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_312_rightCert : IntervalCert :=
  IntervalCert.sqrt (5817 / 2500 : Rat) (100 : Rat) (IntervalCert.add (2707 / 500 : Rat) (1083 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_312 :
    values14 (312 : Fin 455) < values14 (313 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_312_leftCert values14_special_312_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_312_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_312_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (312 : Fin 455) = 1 + values12 (47 : Fin 154) by rfl]
    simp only [values14_special_312_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    simp only [values14_special_312_rightCert, IntervalCert.expr, eval]
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_312_leftCert, values14_special_312_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_313_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (2327 / 1000 : Rat) (IntervalCert.add (2707 / 500 : Rat) (54143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (220711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_313_rightCert : IntervalCert :=
  IntervalCert.add (292 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13363 / 10000 : Rat) (1337 / 1000 : Rat) (IntervalCert.sqrt (8929 / 5000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_313 :
    values14 (313 : Fin 455) < values14 (314 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_313_leftCert values14_special_313_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_313_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_313_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    simp only [values14_special_313_leftCert, IntervalCert.expr, eval]
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    simp only [values14_special_313_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_313_leftCert, values14_special_313_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_314_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (58409 / 25000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (167 / 125 : Rat) (41761 / 31250 : Rat) (IntervalCert.sqrt (357 / 200 : Rat) (446459 / 250000 : Rat) (IntervalCert.add (3189 / 1000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (5473 / 2500 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14_special_314_rightCert : IntervalCert :=
  IntervalCert.add (5841 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_314 :
    values14 (314 : Fin 455) < values14 (315 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_314_leftCert values14_special_314_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_314_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_314_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    simp only [values14_special_314_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    simp only [values14_special_314_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_314_leftCert, values14_special_314_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_315_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2337 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14_special_315_rightCert : IntervalCert :=
  IntervalCert.add (2359 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13593 / 10000 : Rat) (34 / 25 : Rat) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_315 :
    values14 (315 : Fin 455) < values14 (316 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_315_leftCert values14_special_315_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_315_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_315_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    simp only [values14_special_315_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    simp only [values14_special_315_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_315_leftCert, values14_special_315_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_316_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (59 / 25 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1359 / 1000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (1707 / 500 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_316_rightCert : IntervalCert :=
  IntervalCert.add (1189 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_316 :
    values14 (316 : Fin 455) < values14 (317 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_316_leftCert values14_special_316_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_316_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_316_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    simp only [values14_special_316_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    simp only [values14_special_316_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_316_leftCert, values14_special_316_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_317_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2379 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))))))

private def values14_special_317_rightCert : IntervalCert :=
  IntervalCert.add (2389 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13899 / 10000 : Rat) (139 / 100 : Rat) (IntervalCert.sqrt (38637 / 20000 : Rat) (483 / 250 : Rat) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_317 :
    values14 (317 : Fin 455) < values14 (318 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_317_leftCert values14_special_317_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_317_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_317_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    simp only [values14_special_317_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    simp only [values14_special_317_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_317_leftCert, values14_special_317_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_318_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (239 / 100 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1389 / 1000 : Rat) (8687 / 6250 : Rat) (IntervalCert.sqrt (1931 / 1000 : Rat) (96593 / 50000 : Rat) (IntervalCert.add (933 / 250 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

private def values14_special_318_rightCert : IntervalCert :=
  IntervalCert.add (1203 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_318 :
    values14 (318 : Fin 455) < values14 (319 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_318_leftCert values14_special_318_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_318_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_318_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    simp only [values14_special_318_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14_special_318_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_318_leftCert, values14_special_318_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_319_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2407 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values14_special_319_rightCert : IntervalCert :=
  IntervalCert.add (1207 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_319 :
    values14 (319 : Fin 455) < values14 (320 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_319_leftCert values14_special_319_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_319_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_319_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14_special_319_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (320 : Fin 455) = 1 + values12 (51 : Fin 154) by rfl]
    simp only [values14_special_319_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_319_leftCert, values14_special_319_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_322_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1211 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1421 / 1000 : Rat) (71097 / 50000 : Rat) (IntervalCert.add (2021 / 1000 : Rat) (20219 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (5109 / 5000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values14_special_322_rightCert : IntervalCert :=
  IntervalCert.add (97 / 40 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_322 :
    values14 (322 : Fin 455) < values14 (323 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_322_leftCert values14_special_322_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_322_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_322_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (322 : Fin 455) = 1 + values12 (53 : Fin 154) by rfl]
    simp only [values14_special_322_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    simp only [values14_special_322_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_322_leftCert, values14_special_322_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_323_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1213 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (101 / 100 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14_special_323_rightCert : IntervalCert :=
  IntervalCert.add (2429 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14297 / 10000 : Rat) (143 / 100 : Rat) (IntervalCert.add (10221 / 5000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

set_option linter.unusedTactic false in
theorem values14_special_323 :
    values14 (323 : Fin 455) < values14 (324 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_323_leftCert values14_special_323_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_323_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_323_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    simp only [values14_special_323_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    simp only [values14_special_323_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_323_leftCert, values14_special_323_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_324_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (243 / 100 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1429 / 1000 : Rat) (7149 / 5000 : Rat) (IntervalCert.add (511 / 250 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14_special_324_rightCert : IntervalCert :=
  IntervalCert.add (487 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_324 :
    values14 (324 : Fin 455) < values14 (325 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_324_leftCert values14_special_324_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_324_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_324_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    simp only [values14_special_324_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    simp only [values14_special_324_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_324_leftCert, values14_special_324_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_325_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (12179 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_325_rightCert : IntervalCert :=
  IntervalCert.add (609 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_325 :
    values14 (325 : Fin 455) < values14 (326 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_325_leftCert values14_special_325_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_325_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_325_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    simp only [values14_special_325_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    simp only [values14_special_325_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_325_leftCert, values14_special_325_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_326_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2437 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14_special_326_rightCert : IntervalCert :=
  IntervalCert.add (2439 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14391 / 10000 : Rat) (36 / 25 : Rat) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_326 :
    values14 (326 : Fin 455) < values14 (327 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_326_leftCert values14_special_326_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_326_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_326_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    simp only [values14_special_326_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (327 : Fin 455) = 1 + values12 (55 : Fin 154) by rfl]
    simp only [values14_special_326_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_326_leftCert, values14_special_326_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_329_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (612371 / 250000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1449 / 1000 : Rat) (14494837 / 10000000 : Rat) (IntervalCert.sqrt (2101 / 1000 : Rat) (210100299 / 100000000 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (4414213563 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (4267766953 / 1250000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120710678119 / 50000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707106781187 / 500000000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000000000001 / 1000000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat)))))))))

private def values14_special_329_rightCert : IntervalCert :=
  IntervalCert.sqrt (2449489 / 1000000 : Rat) (100 : Rat) (IntervalCert.add (5999999 / 1000000 : Rat) (6001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (49999999 / 10000000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999999 / 100000000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999999 / 1000000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_329 :
    values14 (329 : Fin 455) < values14 (330 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_329_leftCert values14_special_329_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_329_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_329_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (329 : Fin 455) = 1 + values12 (57 : Fin 154) by rfl]
    simp only [values14_special_329_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    simp only [values14_special_329_rightCert, IntervalCert.expr, eval]
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_329_leftCert, values14_special_329_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_330_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (49 / 20 : Rat) (IntervalCert.add (5999 / 1000 : Rat) (6001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (49999 / 10000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values14_special_330_rightCert : IntervalCert :=
  IntervalCert.add (1227 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (3637 / 2500 : Rat) (291 / 200 : Rat) (IntervalCert.add (105823 / 50000 : Rat) (2117 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_330 :
    values14 (330 : Fin 455) < values14 (331 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_330_leftCert values14_special_330_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_330_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_330_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    simp only [values14_special_330_leftCert, IntervalCert.expr, eval]
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    simp only [values14_special_330_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_330_leftCert, values14_special_330_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_331_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (491 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (727 / 500 : Rat) (145481 / 100000 : Rat) (IntervalCert.add (529 / 250 : Rat) (211647 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (5582349 / 5000000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1558131 / 1250000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_331_rightCert : IntervalCert :=
  IntervalCert.add (1229 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_331 :
    values14 (331 : Fin 455) < values14 (332 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_331_leftCert values14_special_331_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_331_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_331_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    simp only [values14_special_331_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    simp only [values14_special_331_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_331_leftCert, values14_special_331_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_332_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2459 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14_special_332_rightCert : IntervalCert :=
  IntervalCert.add (493 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14653 / 10000 : Rat) (733 / 500 : Rat) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_332 :
    values14 (332 : Fin 455) < values14 (333 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_332_leftCert values14_special_332_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_332_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_332_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    simp only [values14_special_332_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (333 : Fin 455) = 1 + values12 (59 : Fin 154) by rfl]
    simp only [values14_special_332_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_332_leftCert, values14_special_332_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_334_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (62 / 25 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14_special_334_rightCert : IntervalCert :=
  IntervalCert.add (497 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (134 / 125 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_334 :
    values14 (334 : Fin 455) < values14 (335 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_334_leftCert values14_special_334_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_334_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_334_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (334 : Fin 455) = 1 + values12 (60 : Fin 154) by rfl]
    simp only [values14_special_334_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    simp only [values14_special_334_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_334_leftCert, values14_special_334_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_335_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1243 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_335_rightCert : IntervalCert :=
  IntervalCert.add (311 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14887 / 10000 : Rat) (1489 / 1000 : Rat) (IntervalCert.add (22163 / 10000 : Rat) (2217 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_335 :
    values14 (335 : Fin 455) < values14 (336 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_335_leftCert values14_special_335_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_335_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_335_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    simp only [values14_special_335_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (336 : Fin 455) = 1 + values12 (61 : Fin 154) by rfl]
    simp only [values14_special_335_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_335_leftCert, values14_special_335_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_338_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2499 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (749 / 500 : Rat) (37471 / 25000 : Rat) (IntervalCert.add (1123 / 500 : Rat) (224651 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_338_rightCert : IntervalCert :=
  IntervalCert.add (313 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_338 :
    values14 (338 : Fin 455) < values14 (339 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_338_leftCert values14_special_338_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_338_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_338_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (338 : Fin 455) = 1 + values12 (63 : Fin 154) by rfl]
    simp only [values14_special_338_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    simp only [values14_special_338_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_338_leftCert, values14_special_338_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_339_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3131 / 1250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14_special_339_rightCert : IntervalCert :=
  IntervalCert.add (6263 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_339 :
    values14 (339 : Fin 455) < values14 (340 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_339_leftCert values14_special_339_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_339_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_339_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    simp only [values14_special_339_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    simp only [values14_special_339_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_339_leftCert, values14_special_339_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_340_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1253 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14_special_340_rightCert : IntervalCert :=
  IntervalCert.add (2521 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7609 / 5000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_340 :
    values14 (340 : Fin 455) < values14 (341 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_340_leftCert values14_special_340_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_340_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_340_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    simp only [values14_special_340_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    simp only [values14_special_340_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_340_leftCert, values14_special_340_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_341_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1261 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1521 / 1000 : Rat) (15219 / 10000 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_341_rightCert : IntervalCert :=
  IntervalCert.add (253 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2791 / 2500 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_341 :
    values14 (341 : Fin 455) < values14 (342 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_341_leftCert values14_special_341_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_341_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_341_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    simp only [values14_special_341_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    simp only [values14_special_341_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_341_leftCert, values14_special_341_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_342_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2531 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (279 / 250 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_342_rightCert : IntervalCert :=
  IntervalCert.add (1271 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7711 / 5000 : Rat) (1543 / 1000 : Rat) (IntervalCert.add (2973 / 1250 : Rat) (2379 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_342 :
    values14 (342 : Fin 455) < values14 (343 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_342_leftCert values14_special_342_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_342_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_342_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    simp only [values14_special_342_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (343 : Fin 455) = 1 + values12 (65 : Fin 154) by rfl]
    simp only [values14_special_342_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_342_leftCert, values14_special_342_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_344_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1277 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_344_rightCert : IntervalCert :=
  IntervalCert.add (2561 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_344 :
    values14 (344 : Fin 455) < values14 (345 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_344_leftCert values14_special_344_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_344_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_344_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (344 : Fin 455) = 1 + values12 (66 : Fin 154) by rfl]
    simp only [values14_special_344_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    simp only [values14_special_344_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_344_leftCert, values14_special_344_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_345_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1281 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14_special_345_rightCert : IntervalCert :=
  IntervalCert.add (25639 / 10000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19549 / 12500 : Rat) (391 / 250 : Rat) (IntervalCert.add (48917 / 20000 : Rat) (1223 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (722929 / 500000 : Rat) (14459 / 10000 : Rat) (IntervalCert.add (2090507 / 1000000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_345 :
    values14 (345 : Fin 455) < values14 (346 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_345_leftCert values14_special_345_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_345_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_345_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    simp only [values14_special_345_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (346 : Fin 455) = 1 + values12 (67 : Fin 154) by rfl]
    simp only [values14_special_345_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_345_leftCert, values14_special_345_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_349_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2599 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (799 / 500 : Rat) (15981 / 10000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_349_rightCert : IntervalCert :=
  IntervalCert.add (2603 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_349 :
    values14 (349 : Fin 455) < values14 (350 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_349_leftCert values14_special_349_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_349_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_349_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (349 : Fin 455) = 1 + values12 (70 : Fin 154) by rfl]
    simp only [values14_special_349_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    simp only [values14_special_349_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_349_leftCert, values14_special_349_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_350_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14_special_350_rightCert : IntervalCert :=
  IntervalCert.add (2613 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (3227 / 2000 : Rat) (807 / 500 : Rat) (IntervalCert.add (13017 / 5000 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_350 :
    values14 (350 : Fin 455) < values14 (351 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_350_leftCert values14_special_350_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_350_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_350_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    simp only [values14_special_350_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (351 : Fin 455) = 1 + values12 (71 : Fin 154) by rfl]
    simp only [values14_special_350_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_350_leftCert, values14_special_350_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_352_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2629 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (407 / 250 : Rat) (1018 / 625 : Rat) (IntervalCert.add (663 / 250 : Rat) (26529 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1033 / 625 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

private def values14_special_352_rightCert : IntervalCert :=
  IntervalCert.add (263 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_352 :
    values14 (352 : Fin 455) < values14 (353 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_352_leftCert values14_special_352_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_352_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_352_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (352 : Fin 455) = 1 + values12 (72 : Fin 154) by rfl]
    simp only [values14_special_352_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    simp only [values14_special_352_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_352_leftCert, values14_special_352_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_353_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2631 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (152 / 125 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_353_rightCert : IntervalCert :=
  IntervalCert.add (661 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_353 :
    values14 (353 : Fin 455) < values14 (354 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_353_leftCert values14_special_353_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_353_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_353_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    simp only [values14_special_353_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14_special_353_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_353_leftCert, values14_special_353_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_354_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (26443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values14_special_354_rightCert : IntervalCert :=
  IntervalCert.sqrt (26457 / 10000 : Rat) (100 : Rat) (IntervalCert.add (69999 / 10000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (599999 / 100000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4999999 / 1000000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (39999999 / 10000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_354 :
    values14 (354 : Fin 455) < values14 (355 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_354_leftCert values14_special_354_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_354_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_354_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14_special_354_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    simp only [values14_special_354_rightCert, IntervalCert.expr, eval]
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_354_leftCert, values14_special_354_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_355_leftCert : IntervalCert :=
  IntervalCert.sqrt (0 : Rat) (1323 / 500 : Rat) (IntervalCert.add (6999 / 1000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (59999 / 10000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (499999 / 100000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values14_special_355_rightCert : IntervalCert :=
  IntervalCert.add (663 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_355 :
    values14 (355 : Fin 455) < values14 (356 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_355_leftCert values14_special_355_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_355_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_355_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    simp only [values14_special_355_leftCert, IntervalCert.expr, eval]
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    simp only [values14_special_355_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_355_leftCert, values14_special_355_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_356_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2653 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (413 / 250 : Rat) (16529 / 10000 : Rat) (IntervalCert.add (683 / 250 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_356_rightCert : IntervalCert :=
  IntervalCert.add (133 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_356 :
    values14 (356 : Fin 455) < values14 (357 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_356_leftCert values14_special_356_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_356_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_356_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    simp only [values14_special_356_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    simp only [values14_special_356_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_356_leftCert, values14_special_356_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_357_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2661 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_357_rightCert : IntervalCert :=
  IntervalCert.add (667 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_357 :
    values14 (357 : Fin 455) < values14 (358 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_357_leftCert values14_special_357_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_357_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_357_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    simp only [values14_special_357_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    simp only [values14_special_357_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_357_leftCert, values14_special_357_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_358_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2669 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_358_rightCert : IntervalCert :=
  IntervalCert.add (2681 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (16817 / 10000 : Rat) (841 / 500 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_358 :
    values14 (358 : Fin 455) < values14 (359 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_358_leftCert values14_special_358_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_358_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_358_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    simp only [values14_special_358_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (359 : Fin 455) = 1 + values12 (74 : Fin 154) by rfl]
    simp only [values14_special_358_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_358_leftCert, values14_special_358_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_360_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (336 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1687 / 1000 : Rat) (4219 / 2500 : Rat) (IntervalCert.add (2847 / 1000 : Rat) (14239 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_360_rightCert : IntervalCert :=
  IntervalCert.add (273 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_360 :
    values14 (360 : Fin 455) < values14 (361 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_360_leftCert values14_special_360_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_360_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_360_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (360 : Fin 455) = 1 + values12 (75 : Fin 154) by rfl]
    simp only [values14_special_360_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    simp only [values14_special_360_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_360_leftCert, values14_special_360_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_361_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (27303 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values14_special_361_rightCert : IntervalCert :=
  IntervalCert.add (683 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_361 :
    values14 (361 : Fin 455) < values14 (362 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_361_leftCert values14_special_361_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_361_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_361_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    simp only [values14_special_361_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    simp only [values14_special_361_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_361_leftCert, values14_special_361_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_362_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2733 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values14_special_362_rightCert : IntervalCert :=
  IntervalCert.add (1371 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_362 :
    values14 (362 : Fin 455) < values14 (363 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_362_leftCert values14_special_362_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_362_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_362_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    simp only [values14_special_362_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    simp only [values14_special_362_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_362_leftCert, values14_special_362_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_363_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2743 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_363_rightCert : IntervalCert :=
  IntervalCert.add (27447 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (87239 / 50000 : Rat) (349 / 200 : Rat) (IntervalCert.add (304427 / 100000 : Rat) (609 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_363 :
    values14 (363 : Fin 455) < values14 (364 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_363_leftCert values14_special_363_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_363_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_363_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    simp only [values14_special_363_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (364 : Fin 455) = 1 + values12 (77 : Fin 154) by rfl]
    simp only [values14_special_363_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_363_leftCert, values14_special_363_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_366_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1387 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1773 / 1000 : Rat) (8869 / 5000 : Rat) (IntervalCert.add (1573 / 500 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_366_rightCert : IntervalCert :=
  IntervalCert.add (347 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_366 :
    values14 (366 : Fin 455) < values14 (367 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_366_leftCert values14_special_366_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_366_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_366_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (366 : Fin 455) = 1 + values12 (79 : Fin 154) by rfl]
    simp only [values14_special_366_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14_special_366_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_366_leftCert, values14_special_366_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_367_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2777 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14_special_367_rightCert : IntervalCert :=
  IntervalCert.add (557 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (8929 / 5000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_367 :
    values14 (367 : Fin 455) < values14 (368 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_367_leftCert values14_special_367_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_367_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_367_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14_special_367_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (368 : Fin 455) = 1 + values12 (80 : Fin 154) by rfl]
    simp only [values14_special_367_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_367_leftCert, values14_special_367_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_369_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (28211 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1821 / 1000 : Rat) (182101 / 100000 : Rat) (IntervalCert.add (331607 / 100000 : Rat) (132643 / 40000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (23160741 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

private def values14_special_369_rightCert : IntervalCert :=
  IntervalCert.add (1129 / 400 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_369 :
    values14 (369 : Fin 455) < values14 (370 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_369_leftCert values14_special_369_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_369_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_369_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (369 : Fin 455) = 1 + values12 (81 : Fin 154) by rfl]
    simp only [values14_special_369_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14_special_369_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_369_leftCert, values14_special_369_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_370_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2823 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values14_special_370_rightCert : IntervalCert :=
  IntervalCert.add (707 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_370 :
    values14 (370 : Fin 455) < values14 (371 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_370_leftCert values14_special_370_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_370_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_370_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14_special_370_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    simp only [values14_special_370_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_370_leftCert, values14_special_370_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_371_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_371_rightCert : IntervalCert :=
  IntervalCert.add (2847 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_371 :
    values14 (371 : Fin 455) < values14 (372 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_371_leftCert values14_special_371_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_371_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_371_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    simp only [values14_special_371_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    simp only [values14_special_371_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_371_leftCert, values14_special_371_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_372_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (356 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1847 / 1000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (1707 / 500 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_372_rightCert : IntervalCert :=
  IntervalCert.add (143 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_372 :
    values14 (372 : Fin 455) < values14 (373 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_372_leftCert values14_special_372_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_372_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_372_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    simp only [values14_special_372_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    simp only [values14_special_372_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_372_leftCert, values14_special_372_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_373_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2861 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14_special_373_rightCert : IntervalCert :=
  IntervalCert.add (577 / 200 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18851 / 10000 : Rat) (943 / 500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (1777 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_373 :
    values14 (373 : Fin 455) < values14 (374 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_373_leftCert values14_special_373_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_373_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_373_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    simp only [values14_special_373_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    simp only [values14_special_373_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_373_leftCert, values14_special_373_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_374_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1443 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (377 / 200 : Rat) (4713 / 2500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14_special_374_rightCert : IntervalCert :=
  IntervalCert.add (2893 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_374 :
    values14 (374 : Fin 455) < values14 (375 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_374_leftCert values14_special_374_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_374_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_374_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    simp only [values14_special_374_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    simp only [values14_special_374_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_374_leftCert, values14_special_374_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_375_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1447 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_375_rightCert : IntervalCert :=
  IntervalCert.add (2921 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_375 :
    values14 (375 : Fin 455) < values14 (376 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_375_leftCert values14_special_375_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_375_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_375_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    simp only [values14_special_375_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    simp only [values14_special_375_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_375_leftCert, values14_special_375_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_376_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1461 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14_special_376_rightCert : IntervalCert :=
  IntervalCert.add (2931 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (9659 / 5000 : Rat) (483 / 250 : Rat) (IntervalCert.add (933 / 250 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_376 :
    values14 (376 : Fin 455) < values14 (377 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_376_leftCert values14_special_376_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_376_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_376_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    simp only [values14_special_376_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (377 : Fin 455) = 1 + values12 (84 : Fin 154) by rfl]
    simp only [values14_special_376_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_376_leftCert, values14_special_376_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_378_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (2957 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (489 / 250 : Rat) (19567 / 10000 : Rat) (IntervalCert.add (957 / 250 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7071 / 2500 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_378_rightCert : IntervalCert :=
  IntervalCert.add (2967 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_378 :
    values14 (378 : Fin 455) < values14 (379 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_378_leftCert values14_special_378_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_378_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_378_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (378 : Fin 455) = 1 + values12 (85 : Fin 154) by rfl]
    simp only [values14_special_378_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    simp only [values14_special_378_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_378_leftCert, values14_special_378_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_379_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (371 / 125 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))

private def values14_special_379_rightCert : IntervalCert :=
  IntervalCert.add (2999 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_379 :
    values14 (379 : Fin 455) < values14 (380 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_379_leftCert values14_special_379_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_379_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_379_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    simp only [values14_special_379_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (380 : Fin 455) = 1 + values12 (86 : Fin 154) by rfl]
    simp only [values14_special_379_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_379_leftCert, values14_special_379_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_386_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3047 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1023 / 500 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))

private def values14_special_386_rightCert : IntervalCert :=
  IntervalCert.add (381 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_386 :
    values14 (386 : Fin 455) < values14 (387 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_386_leftCert values14_special_386_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_386_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_386_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (386 : Fin 455) = 1 + values12 (92 : Fin 154) by rfl]
    simp only [values14_special_386_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14_special_386_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_386_leftCert, values14_special_386_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_387_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3049 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values14_special_387_rightCert : IntervalCert :=
  IntervalCert.add (382 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (10283 / 5000 : Rat) (2057 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (105663 / 100000 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_387 :
    values14 (387 : Fin 455) < values14 (388 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_387_leftCert values14_special_387_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_387_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_387_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14_special_387_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    simp only [values14_special_387_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_387_leftCert, values14_special_387_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_388_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3057 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (257 / 125 : Rat) (20567 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (5283 / 5000 : Rat) (3302 / 3125 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_388_rightCert : IntervalCert :=
  IntervalCert.add (3067 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (165289 / 100000 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_388 :
    values14 (388 : Fin 455) < values14 (389 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_388_leftCert values14_special_388_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_388_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_388_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    simp only [values14_special_388_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    simp only [values14_special_388_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_388_leftCert, values14_special_388_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_389_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (767 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (413 / 250 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))

private def values14_special_389_rightCert : IntervalCert :=
  IntervalCert.add (3071 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_389 :
    values14 (389 : Fin 455) < values14 (390 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_389_leftCert values14_special_389_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_389_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_389_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    simp only [values14_special_389_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (390 : Fin 455) = 1 + values12 (94 : Fin 154) by rfl]
    simp only [values14_special_389_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_389_leftCert, values14_special_389_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_394_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3117 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (529 / 250 : Rat) (4233 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14_special_394_rightCert : IntervalCert :=
  IntervalCert.add (1573 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

set_option linter.unusedTactic false in
theorem values14_special_394 :
    values14 (394 : Fin 455) < values14 (395 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_394_leftCert values14_special_394_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_394_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_394_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (394 : Fin 455) = 1 + values12 (98 : Fin 154) by rfl]
    simp only [values14_special_394_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    simp only [values14_special_394_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_394_leftCert, values14_special_394_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_395_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14_special_395_rightCert : IntervalCert :=
  IntervalCert.add (3147 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_395 :
    values14 (395 : Fin 455) < values14 (396 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_395_leftCert values14_special_395_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_395_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_395_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    simp only [values14_special_395_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (396 : Fin 455) = 1 + values12 (99 : Fin 154) by rfl]
    simp only [values14_special_395_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_395_leftCert, values14_special_395_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_401_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1123 / 500 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14_special_401_rightCert : IntervalCert :=
  IntervalCert.add (3261 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_401 :
    values14 (401 : Fin 455) < values14 (402 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_401_leftCert values14_special_401_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_401_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_401_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (401 : Fin 455) = 1 + values12 (104 : Fin 154) by rfl]
    simp only [values14_special_401_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    simp only [values14_special_401_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_401_leftCert, values14_special_401_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_402_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1631 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))

private def values14_special_402_rightCert : IntervalCert :=
  IntervalCert.add (3279 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (22797 / 10000 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

set_option linter.unusedTactic false in
theorem values14_special_402 :
    values14 (402 : Fin 455) < values14 (403 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_402_leftCert values14_special_402_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_402_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_402_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    simp only [values14_special_402_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (403 : Fin 455) = 1 + values12 (105 : Fin 154) by rfl]
    simp only [values14_special_402_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_402_leftCert, values14_special_402_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_404_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (32857 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (457 / 200 : Rat) (45713 / 20000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (3214121 / 2500000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (16528917 / 10000000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27320509 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))

private def values14_special_404_rightCert : IntervalCert :=
  IntervalCert.add (16429 / 5000 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_404 :
    values14 (404 : Fin 455) < values14 (405 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_404_leftCert values14_special_404_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_404_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_404_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (404 : Fin 455) = 1 + values12 (106 : Fin 154) by rfl]
    simp only [values14_special_404_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14_special_404_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_404_leftCert, values14_special_404_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_405_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (1643 / 500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))

private def values14_special_405_rightCert : IntervalCert :=
  IntervalCert.add (829 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (231607 / 100000 : Rat) (2317 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_405 :
    values14 (405 : Fin 455) < values14 (406 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_405_leftCert values14_special_405_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_405_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_405_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14_special_405_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (406 : Fin 455) = 1 + values12 (107 : Fin 154) by rfl]
    simp only [values14_special_405_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_405_leftCert, values14_special_405_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_413_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (3459 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1229 / 500 : Rat) (4917 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))

private def values14_special_413_rightCert : IntervalCert :=
  IntervalCert.add (433 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))

set_option linter.unusedTactic false in
theorem values14_special_413 :
    values14 (413 : Fin 455) < values14 (414 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_413_leftCert values14_special_413_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_413_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_413_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (413 : Fin 455) = 1 + values12 (114 : Fin 154) by rfl]
    simp only [values14_special_413_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14_special_413_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_413_leftCert, values14_special_413_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_414_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (693 / 200 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))

private def values14_special_414_rightCert : IntervalCert :=
  IntervalCert.add (3479 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (4959 / 2000 : Rat) (62 / 25 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

set_option linter.unusedTactic false in
theorem values14_special_414 :
    values14 (414 : Fin 455) < values14 (415 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_414_leftCert values14_special_414_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_414_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_414_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14_special_414_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (415 : Fin 455) = 1 + values12 (115 : Fin 154) by rfl]
    simp only [values14_special_414_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_414_leftCert, values14_special_414_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_437_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4237 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (809 / 250 : Rat) (32361 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (111803 / 50000 : Rat) (223607 / 100000 : Rat) (IntervalCert.add (499999 / 100000 : Rat) (5000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat))))))))

private def values14_special_437_rightCert : IntervalCert :=
  IntervalCert.add (2121 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))

set_option linter.unusedTactic false in
theorem values14_special_437 :
    values14 (437 : Fin 455) < values14 (438 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_437_leftCert values14_special_437_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_437_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_437_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (437 : Fin 455) = 1 + values12 (137 : Fin 154) by rfl]
    simp only [values14_special_437_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    simp only [values14_special_437_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_437_leftCert, values14_special_437_rightCert, IntervalCert.upper, IntervalCert.lower]

private def values14_special_438_leftCert : IntervalCert :=
  IntervalCert.add (0 : Rat) (4243 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.add (707 / 250 : Rat) (5657 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))

private def values14_special_438_rightCert : IntervalCert :=
  IntervalCert.add (2123 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (6493 / 2000 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (280813 / 125000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (12465047 / 10000000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))

set_option linter.unusedTactic false in
theorem values14_special_438 :
    values14 (438 : Fin 455) < values14 (439 : Fin 455) := by
  refine IntervalCert.lt_of_gap values14_special_438_leftCert values14_special_438_rightCert ?_ ?_ ?_ ?_ ?_
  · norm_num [values14_special_438_leftCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · norm_num [values14_special_438_rightCert, IntervalCert.Valid, IntervalCert.lower, IntervalCert.upper]
  · rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    simp only [values14_special_438_leftCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (439 : Fin 455) = 1 + values12 (138 : Fin 154) by rfl]
    simp only [values14_special_438_rightCert, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · norm_num [values14_special_438_leftCert, values14_special_438_rightCert, IntervalCert.upper, IntervalCert.lower]

end Expr
end A158415
end LeanProofs
