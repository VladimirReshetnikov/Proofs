import A158415.Certificates.N14.Table
import A158415.IntervalCert

/-!
# Size-fourteen interval order certificates for OEIS A158415

This generated module replaces the large hand-expanded rational-bound
ladders for the exceptional adjacent comparisons in `values14` with
compact interval certificates checked by one soundness theorem.  All
rational side conditions are discharged by one batched native decision.
-/

namespace LeanProofs
namespace A158415
namespace Expr

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def values14SpecialCert_0 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (3999 / 1000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (2001 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (10013 / 10000 : Rat) (501 / 500 : Rat) (IntervalCert.sqrt (10027 / 10000 : Rat) (1003 / 1000 : Rat) (IntervalCert.sqrt (50271 / 50000 : Rat) (503 / 500 : Rat) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))))

private def values14SpecialCert_1 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (20109 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (101 / 100 : Rat) (101089 / 100000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)))))))))))),
    IntervalCert.sqrt (2011 / 1000 : Rat) (100 : Rat) (IntervalCert.add (20221 / 5000 : Rat) (809 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (304427 / 100000 : Rat) (30443 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (51107 / 25000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values14SpecialCert_2 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (20111 / 10000 : Rat) (IntervalCert.add (1011 / 250 : Rat) (40443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (15221 / 5000 : Rat) (76107 / 25000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (204427 / 100000 : Rat) (1022137 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1044273 / 1000000 : Rat) (5221369 / 5000000 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (54525387 / 50000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (2013 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (5069 / 5000 : Rat) (507 / 500 : Rat) (IntervalCert.sqrt (10279 / 10000 : Rat) (257 / 250 : Rat) (IntervalCert.sqrt (5283 / 5000 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

private def values14SpecialCert_3 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1011 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1021 / 1000 : Rat) (10219 / 10000 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)))))))))))),
    IntervalCert.sqrt (809 / 400 : Rat) (100 : Rat) (IntervalCert.add (4090507 / 1000000 : Rat) (4091 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (30905077 / 10000000 : Rat) (15453 / 5000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (209050773 / 100000000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (272626933 / 250000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)))))))))))

private def values14SpecialCert_4 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (2023 / 1000 : Rat) (IntervalCert.add (409 / 100 : Rat) (4091 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (6181 / 2000 : Rat) (15453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2090507 / 1000000 : Rat) (209051 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.add (20247 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (51239 / 50000 : Rat) (41 / 40 : Rat) (IntervalCert.sqrt (105019 / 100000 : Rat) (5251 / 5000 : Rat) (IntervalCert.sqrt (86164 / 78125 : Rat) (11029 / 10000 : Rat) (IntervalCert.sqrt (3040967 / 2500000 : Rat) (1216387 / 1000000 : Rat) (IntervalCert.sqrt (14795969 / 10000000 : Rat) (1479597 / 1000000 : Rat) (IntervalCert.add (2189207 / 1000000 : Rat) (2736509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (14865089 / 12500000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))))

private def values14SpecialCert_5 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (407 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (517 / 500 : Rat) (103493 / 100000 : Rat) (IntervalCert.sqrt (1071 / 1000 : Rat) (26777 / 25000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))),
    IntervalCert.sqrt (509 / 250 : Rat) (100 : Rat) (IntervalCert.add (2073 / 500 : Rat) (4147 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (15731 / 5000 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14SpecialCert_6 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (2037 / 1000 : Rat) (IntervalCert.add (2073 / 500 : Rat) (4147 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (15731 / 5000 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (511 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_7 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (409 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.sqrt (1023 / 500 : Rat) (100 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (419 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_8 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.add (20471 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (26179 / 25000 : Rat) (131 / 125 : Rat) (IntervalCert.sqrt (21931 / 20000 : Rat) (1097 / 1000 : Rat) (IntervalCert.sqrt (120243 / 100000 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values14SpecialCert_9 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (259 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))),
    IntervalCert.sqrt (2077 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14SpecialCert_10 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (1039 / 500 : Rat) (IntervalCert.add (1079 / 250 : Rat) (4317 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (331607 / 100000 : Rat) (33161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (28951 / 12500 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (20797 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13497 / 12500 : Rat) (27 / 25 : Rat) (IntervalCert.sqrt (11659 / 10000 : Rat) (583 / 500 : Rat) (IntervalCert.sqrt (1359323 / 1000000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (92387953 / 50000000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (85355339 / 25000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1207106781 / 500000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (14142135623 / 10000000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999999 / 10000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_11 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2097 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (137 / 125 : Rat) (5483 / 5000 : Rat) (IntervalCert.sqrt (601 / 500 : Rat) (481 / 400 : Rat) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))),
    IntervalCert.sqrt (2101 / 1000 : Rat) (100 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (883 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_12 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (21011 / 10000 : Rat) (IntervalCert.add (2207 / 500 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (17071 / 5000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (241421 / 100000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.add (5257 / 2500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (110289 / 100000 : Rat) (1103 / 1000 : Rat) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))))

private def values14SpecialCert_13 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (213387 / 100000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1133 / 1000 : Rat) (226773 / 200000 : Rat) (IntervalCert.sqrt (257 / 200 : Rat) (1285649 / 1000000 : Rat) (IntervalCert.sqrt (413 / 250 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))),
    IntervalCert.sqrt (42679 / 20000 : Rat) (100 : Rat) (IntervalCert.add (455377 / 100000 : Rat) (2277 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3553773 / 1000000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (25537739 / 10000000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14SpecialCert_14 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (1067 / 500 : Rat) (IntervalCert.add (4553 / 1000 : Rat) (22769 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (35537 / 10000 : Rat) (177689 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (1276887 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77688699 / 50000000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (241421357 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000000001 / 10000000000 : Rat))))))))),
    IntervalCert.add (21347 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (104427 / 100000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

private def values14SpecialCert_15 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (427 / 200 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))),
    IntervalCert.add (1069 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (11387 / 10000 : Rat) (1139 / 1000 : Rat) (IntervalCert.sqrt (1621 / 1250 : Rat) (1297 / 1000 : Rat) (IntervalCert.sqrt (16817 / 10000 : Rat) (841 / 500 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_16 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1083 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (233 / 200 : Rat) (116591 / 100000 : Rat) (IntervalCert.sqrt (1359 / 1000 : Rat) (135933 / 100000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.sqrt (87 / 40 : Rat) (100 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14SpecialCert_17 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (272 / 125 : Rat) (IntervalCert.add (1183 / 250 : Rat) (4733 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (2181 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))))))

private def values14SpecialCert_18 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1091 / 500 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))))),
    IntervalCert.add (2189 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_19 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (549 / 250 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (239 / 200 : Rat) (5979 / 5000 : Rat) (IntervalCert.sqrt (1429 / 1000 : Rat) (7149 / 5000 : Rat) (IntervalCert.add (511 / 250 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))),
    IntervalCert.sqrt (2197 / 1000 : Rat) (100 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14SpecialCert_20 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (1099 / 500 : Rat) (IntervalCert.add (1207 / 250 : Rat) (4829 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (9571 / 2500 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (141421 / 50000 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (1101 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1503 / 1250 : Rat) (1203 / 1000 : Rat) (IntervalCert.sqrt (7229 / 5000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values14SpecialCert_21 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (11053 / 5000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (121 / 100 : Rat) (121051 / 100000 : Rat) (IntervalCert.sqrt (293 / 200 : Rat) (732667 / 500000 : Rat) (IntervalCert.add (2147 / 1000 : Rat) (2147203 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (717 / 625 : Rat) (11472027 / 10000000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)))))))))),
    IntervalCert.add (2211 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14SpecialCert_22 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (553 / 250 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))),
    IntervalCert.add (277 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))))))

private def values14SpecialCert_23 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (89 / 40 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (153 / 125 : Rat) (12243 / 10000 : Rat) (IntervalCert.sqrt (3747 / 2500 : Rat) (14989 / 10000 : Rat) (IntervalCert.add (4493 / 2000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (2233 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

private def values14SpecialCert_24 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (4467 / 2000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))))),
    IntervalCert.add (1396 / 625 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (123363 / 100000 : Rat) (617 / 500 : Rat) (IntervalCert.sqrt (76093 / 50000 : Rat) (761 / 500 : Rat) (IntervalCert.add (231607 / 100000 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_25 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1117 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1233 / 1000 : Rat) (12337 / 10000 : Rat) (IntervalCert.sqrt (1521 / 1000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.sqrt (559 / 250 : Rat) (100 : Rat) (IntervalCert.add (49999 / 10000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_26 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (2237 / 1000 : Rat) (IntervalCert.add (4999 / 1000 : Rat) (5001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (1123 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values14SpecialCert_27 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2271 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (127 / 100 : Rat) (12703 / 10000 : Rat) (IntervalCert.sqrt (1613 / 1000 : Rat) (2017 / 1250 : Rat) (IntervalCert.add (2603 / 1000 : Rat) (5207 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))),
    IntervalCert.sqrt (2277 / 1000 : Rat) (100 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (519 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14SpecialCert_28 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (1139 / 500 : Rat) (IntervalCert.add (5189 / 1000 : Rat) (518921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (10473 / 2500 : Rat) (523651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3189207 / 1000000 : Rat) (3986509 / 1250000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (21892071 / 10000000 : Rat) (27365089 / 12500000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (237841423 / 200000000 : Rat) (297301779 / 250000000 : Rat) (IntervalCert.sqrt (141421356237 / 100000000000 : Rat) (1414213563 / 1000000000 : Rat) (IntervalCert.add (1999999999999 / 1000000000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (9999999999999 / 10000000000000 : Rat) (10000000001 / 10000000000 : Rat))))))))),
    IntervalCert.add (22797 / 10000 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)))))))))

private def values14SpecialCert_29 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))),
    IntervalCert.add (457 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (643 / 500 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_30 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1163 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (53 / 40 : Rat) (13259 / 10000 : Rat) (IntervalCert.sqrt (1757 / 1000 : Rat) (879 / 500 : Rat) (IntervalCert.add (309 / 100 : Rat) (309051 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (4181 / 2000 : Rat) (522627 / 250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5452539 / 5000000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.sqrt (5817 / 2500 : Rat) (100 : Rat) (IntervalCert.add (2707 / 500 : Rat) (1083 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (44143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (170711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (1207107 / 500000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14SpecialCert_31 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (2327 / 1000 : Rat) (IntervalCert.add (2707 / 500 : Rat) (54143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (22071 / 5000 : Rat) (220711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (341421 / 100000 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (292 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13363 / 10000 : Rat) (1337 / 1000 : Rat) (IntervalCert.sqrt (8929 / 5000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_32 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (58409 / 25000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (167 / 125 : Rat) (41761 / 31250 : Rat) (IntervalCert.sqrt (357 / 200 : Rat) (446459 / 250000 : Rat) (IntervalCert.add (3189 / 1000 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (5473 / 2500 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)))))))))),
    IntervalCert.add (5841 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_33 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2337 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))),
    IntervalCert.add (2359 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13593 / 10000 : Rat) (34 / 25 : Rat) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_34 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (59 / 25 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1359 / 1000 : Rat) (6797 / 5000 : Rat) (IntervalCert.sqrt (1847 / 1000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (1707 / 500 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (1189 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))))))

private def values14SpecialCert_35 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2379 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))))),
    IntervalCert.add (2389 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (13899 / 10000 : Rat) (139 / 100 : Rat) (IntervalCert.sqrt (38637 / 20000 : Rat) (483 / 250 : Rat) (IntervalCert.add (74641 / 20000 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (6830127 / 2500000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1732050807 / 1000000000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999999 / 1000000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999999 / 100000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14SpecialCert_36 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (239 / 100 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1389 / 1000 : Rat) (8687 / 6250 : Rat) (IntervalCert.sqrt (1931 / 1000 : Rat) (96593 / 50000 : Rat) (IntervalCert.add (933 / 250 : Rat) (186603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))),
    IntervalCert.add (1203 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))

private def values14SpecialCert_37 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2407 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))),
    IntervalCert.add (1207 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_38 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1211 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1421 / 1000 : Rat) (71097 / 50000 : Rat) (IntervalCert.add (2021 / 1000 : Rat) (20219 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (5109 / 5000 : Rat) (510949 / 500000 : Rat) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat))))))))))),
    IntervalCert.add (97 / 40 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (3159 / 3125 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values14SpecialCert_39 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1213 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (101 / 100 : Rat) (1011 / 1000 : Rat) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))),
    IntervalCert.add (2429 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14297 / 10000 : Rat) (143 / 100 : Rat) (IntervalCert.add (10221 / 5000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (104427 / 100000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))))

private def values14SpecialCert_40 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (243 / 100 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1429 / 1000 : Rat) (7149 / 5000 : Rat) (IntervalCert.add (511 / 250 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (5221 / 5000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))),
    IntervalCert.add (487 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14SpecialCert_41 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (12179 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (609 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (102189 / 100000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (104427 / 100000 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))))

private def values14SpecialCert_42 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2437 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1021 / 1000 : Rat) (511 / 500 : Rat) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))),
    IntervalCert.add (2439 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14391 / 10000 : Rat) (36 / 25 : Rat) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_43 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (612371 / 250000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1449 / 1000 : Rat) (14494837 / 10000000 : Rat) (IntervalCert.sqrt (2101 / 1000 : Rat) (210100299 / 100000000 : Rat) (IntervalCert.add (441421 / 100000 : Rat) (4414213563 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (3414213 / 1000000 : Rat) (4267766953 / 1250000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.add (4828427 / 2000000 : Rat) (120710678119 / 50000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000000001 / 1000000000000 : Rat)) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707106781187 / 500000000000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000000000001 / 1000000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000000000001 / 10000000000000 : Rat))))))))),
    IntervalCert.sqrt (2449489 / 1000000 : Rat) (100 : Rat) (IntervalCert.add (5999999 / 1000000 : Rat) (6001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (49999999 / 10000000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999999 / 100000000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999999 / 1000000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999999 / 10000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999999 / 100000000000 : Rat) (100000001 / 100000000 : Rat))))))))))

private def values14SpecialCert_44 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (49 / 20 : Rat) (IntervalCert.add (5999 / 1000 : Rat) (6001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (49999 / 10000 : Rat) (50001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))),
    IntervalCert.add (1227 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (3637 / 2500 : Rat) (291 / 200 : Rat) (IntervalCert.add (105823 / 50000 : Rat) (2117 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_45 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (491 / 200 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (727 / 500 : Rat) (145481 / 100000 : Rat) (IntervalCert.add (529 / 250 : Rat) (211647 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (5582349 / 5000000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1558131 / 1250000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (1229 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))))

private def values14SpecialCert_46 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2459 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))),
    IntervalCert.add (493 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14653 / 10000 : Rat) (733 / 500 : Rat) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_47 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (62 / 25 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))))))),
    IntervalCert.add (497 / 200 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (134 / 125 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_48 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1243 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1071 / 1000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (717 / 625 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (311 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (14887 / 10000 : Rat) (1489 / 1000 : Rat) (IntervalCert.add (22163 / 10000 : Rat) (2217 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (60819 / 50000 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_49 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2499 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (749 / 500 : Rat) (37471 / 25000 : Rat) (IntervalCert.add (1123 / 500 : Rat) (224651 / 100000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (313 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))))

private def values14SpecialCert_50 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3131 / 1250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))))),
    IntervalCert.add (6263 / 2500 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_51 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1253 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))),
    IntervalCert.add (2521 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7609 / 5000 : Rat) (761 / 500 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_52 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1261 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1521 / 1000 : Rat) (15219 / 10000 : Rat) (IntervalCert.add (579 / 250 : Rat) (23161 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (131607 / 100000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (253 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2791 / 2500 : Rat) (1117 / 1000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14SpecialCert_53 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2531 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (279 / 250 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (1271 / 500 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (7711 / 5000 : Rat) (1543 / 1000 : Rat) (IntervalCert.add (2973 / 1250 : Rat) (2379 / 1000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_54 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1277 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (2561 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (717 / 625 : Rat) (287 / 250 : Rat) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_55 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1281 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1147 / 1000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))),
    IntervalCert.add (25639 / 10000 : Rat) (100 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19549 / 12500 : Rat) (391 / 250 : Rat) (IntervalCert.add (48917 / 20000 : Rat) (1223 / 500 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (722929 / 500000 : Rat) (14459 / 10000 : Rat) (IntervalCert.add (2090507 / 1000000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_56 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2599 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (799 / 500 : Rat) (15981 / 10000 : Rat) (IntervalCert.add (25537 / 10000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (2603 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))))

private def values14SpecialCert_57 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (99999 / 100000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))))))),
    IntervalCert.add (2613 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (3227 / 2000 : Rat) (807 / 500 : Rat) (IntervalCert.add (13017 / 5000 : Rat) (651 / 250 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_58 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2629 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (407 / 250 : Rat) (1018 / 625 : Rat) (IntervalCert.add (663 / 250 : Rat) (26529 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1033 / 625 : Rat) (413223 / 250000 : Rat) (IntervalCert.add (683 / 250 : Rat) (2732051 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))),
    IntervalCert.add (263 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (12163 / 10000 : Rat) (1217 / 1000 : Rat) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_59 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2631 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (152 / 125 : Rat) (3041 / 2500 : Rat) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (661 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14SpecialCert_60 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (26443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))),
    IntervalCert.sqrt (26457 / 10000 : Rat) (100 : Rat) (IntervalCert.add (69999 / 10000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (599999 / 100000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (4999999 / 1000000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (39999999 / 10000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))

private def values14SpecialCert_61 : IntervalCert × IntervalCert :=
  (IntervalCert.sqrt (0 : Rat) (1323 / 500 : Rat) (IntervalCert.add (6999 / 1000 : Rat) (7001 / 1000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (59999 / 10000 : Rat) (60001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (499999 / 100000 : Rat) (500001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (4000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000000001 / 1000000000 : Rat)))))))),
    IntervalCert.add (663 / 250 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (1033 / 625 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_62 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2653 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (413 / 250 : Rat) (16529 / 10000 : Rat) (IntervalCert.add (683 / 250 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (133 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2493 / 2000 : Rat) (1247 / 1000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14SpecialCert_63 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2661 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (623 / 500 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (667 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_64 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2669 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (2681 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (16817 / 10000 : Rat) (841 / 500 : Rat) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_65 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (336 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (1687 / 1000 : Rat) (4219 / 2500 : Rat) (IntervalCert.add (2847 / 1000 : Rat) (14239 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (273 / 100 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_66 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (27303 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (329 / 250 : Rat) (52643 / 40000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))),
    IntervalCert.add (683 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999999 / 10000000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14SpecialCert_67 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2733 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (400001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (3000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000001 / 100000000 : Rat))))))))),
    IntervalCert.add (1371 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14SpecialCert_68 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2743 / 1000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (27447 / 10000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (87239 / 50000 : Rat) (349 / 200 : Rat) (IntervalCert.add (304427 / 100000 : Rat) (609 / 200 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2044273 / 1000000 : Rat) (20443 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (10442737 / 10000000 : Rat) (26107 / 25000 : Rat) (IntervalCert.sqrt (10905077 / 10000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_69 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1387 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1773 / 1000 : Rat) (8869 / 5000 : Rat) (IntervalCert.add (1573 / 500 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (347 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (5221 / 5000 : Rat) (209 / 200 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))))))

private def values14SpecialCert_70 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2777 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (261 / 250 : Rat) (10443 / 10000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat))))))),
    IntervalCert.add (557 / 200 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (8929 / 5000 : Rat) (893 / 500 : Rat) (IntervalCert.add (7973 / 2500 : Rat) (31893 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_71 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (28211 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1821 / 1000 : Rat) (182101 / 100000 : Rat) (IntervalCert.add (331607 / 100000 : Rat) (132643 / 40000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (1158037 / 500000 : Rat) (23160741 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (131607401 / 100000000 : Rat) (65803701 / 50000000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000000001 / 100000000000 : Rat))))))))),
    IntervalCert.add (1129 / 400 : Rat) (100 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (1091 / 1000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

private def values14SpecialCert_72 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2823 / 1000 : Rat) (IntervalCert.sqrt (109 / 100 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))),
    IntervalCert.add (707 / 250 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.sqrt (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (399999 / 100000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (2999999 / 1000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14SpecialCert_73 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.sqrt (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (40001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (2847 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_74 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (356 / 125 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1847 / 1000 : Rat) (9239 / 5000 : Rat) (IntervalCert.add (1707 / 500 : Rat) (34143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (143 / 50 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (28917 / 20000 : Rat) (723 / 500 : Rat) (IntervalCert.add (4181 / 2000 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14SpecialCert_75 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2861 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (289 / 200 : Rat) (723 / 500 : Rat) (IntervalCert.add (209 / 100 : Rat) (10453 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2181 / 2000 : Rat) (109051 / 100000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (118921 / 100000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))),
    IntervalCert.add (577 / 200 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (18851 / 10000 : Rat) (943 / 500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (1777 / 500 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (12769 / 5000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14SpecialCert_76 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1443 / 500 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (377 / 200 : Rat) (4713 / 2500 : Rat) (IntervalCert.add (35537 / 10000 : Rat) (17769 / 5000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (255377 / 100000 : Rat) (127689 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat))))))))),
    IntervalCert.add (2893 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (2959 / 2000 : Rat) (37 / 25 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (219 / 100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_77 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1447 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1479 / 1000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (2189 / 1000 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (2973 / 2500 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (2921 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (119 / 100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_78 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1461 / 500 : Rat) (IntervalCert.sqrt (1189 / 1000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))),
    IntervalCert.add (2931 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (9659 / 5000 : Rat) (483 / 250 : Rat) (IntervalCert.add (933 / 250 : Rat) (37321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (54641 / 20000 : Rat) (136603 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (1732051 / 1000000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30000001 / 10000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000000001 / 1000000000 : Rat))))))))))

private def values14SpecialCert_79 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (2957 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (489 / 250 : Rat) (19567 / 10000 : Rat) (IntervalCert.add (957 / 250 : Rat) (7657 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7071 / 2500 : Rat) (282843 / 100000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (2967 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (15537 / 10000 : Rat) (777 / 500 : Rat) (IntervalCert.add (1207 / 500 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))))))

private def values14SpecialCert_80 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (371 / 125 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (1553 / 1000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)))))))),
    IntervalCert.add (2999 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.sqrt (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.add (39999 / 10000 : Rat) (4001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (299999 / 100000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_81 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3047 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1023 / 500 : Rat) (5117 / 2500 : Rat) (IntervalCert.add (4189 / 1000 : Rat) (41893 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (7973 / 2500 : Rat) (318921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (2189207 / 1000000 : Rat) (273651 / 125000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (11892071 / 10000000 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (35355339 / 25000000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (100000001 / 100000000 : Rat))))))))),
    IntervalCert.add (381 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (131607 / 100000 : Rat) (1317 / 1000 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

private def values14SpecialCert_82 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3049 / 1000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (329 / 250 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))),
    IntervalCert.add (382 / 125 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (10283 / 5000 : Rat) (2057 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (105663 / 100000 : Rat) (10567 / 10000 : Rat) (IntervalCert.sqrt (1116469 / 1000000 : Rat) (2233 / 2000 : Rat) (IntervalCert.sqrt (155813 / 125000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (1553773 / 1000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (2414213 / 1000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_83 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3057 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (257 / 125 : Rat) (20567 / 10000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (5283 / 5000 : Rat) (3302 / 3125 : Rat) (IntervalCert.sqrt (55823 / 50000 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (3067 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (165289 / 100000 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (54641 / 20000 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))

private def values14SpecialCert_84 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (767 / 250 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (413 / 250 : Rat) (1653 / 1000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27321 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat))))))),
    IntervalCert.add (3071 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (207107 / 100000 : Rat) (259 / 125 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (42843 / 40000 : Rat) (10711 / 10000 : Rat) (IntervalCert.sqrt (573601 / 500000 : Rat) (114721 / 100000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (16451 / 12500 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_85 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3117 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (529 / 250 : Rat) (4233 / 2000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2791 / 2500 : Rat) (111647 / 100000 : Rat) (IntervalCert.sqrt (2493 / 2000 : Rat) (249301 / 200000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (776887 / 500000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000000001 / 1000000000 : Rat)))))))))),
    IntervalCert.add (1573 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))))))))

private def values14SpecialCert_86 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (31463 / 10000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (433 / 250 : Rat) (86603 / 50000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (300001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))))),
    IntervalCert.add (3147 / 1000 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (1342 / 625 : Rat) (537 / 250 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (573601 / 500000 : Rat) (11473 / 10000 : Rat) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_87 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1123 / 500 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (2493 / 2000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377 / 100000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000001 / 10000000 : Rat)))))))))),
    IntervalCert.add (3261 / 1000 : Rat) (100 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (283 / 200 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.sqrt (18477 / 10000 : Rat) (231 / 125 : Rat) (IntervalCert.add (1707 / 500 : Rat) (683 / 200 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))))))

private def values14SpecialCert_88 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1631 / 500 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (1847 / 1000 : Rat) (23097 / 12500 : Rat) (IntervalCert.add (1707 / 500 : Rat) (1707107 / 500000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (12071 / 5000 : Rat) (3017767 / 1250000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (141421 / 100000 : Rat) (141421357 / 100000000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200000001 / 100000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000000001 / 1000000000 : Rat))))))),
    IntervalCert.add (3279 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (22797 / 10000 : Rat) (57 / 25 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (1090507 / 1000000 : Rat) (5453 / 5000 : Rat) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (11893 / 10000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))))))

private def values14SpecialCert_89 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (32857 / 10000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (457 / 200 : Rat) (45713 / 20000 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1607 / 1250 : Rat) (3214121 / 2500000 : Rat) (IntervalCert.sqrt (1033 / 625 : Rat) (16528917 / 10000000 : Rat) (IntervalCert.add (683 / 250 : Rat) (27320509 / 10000000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.sqrt (34641 / 20000 : Rat) (173205081 / 100000000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3000000001 / 1000000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20000000001 / 10000000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100000000001 / 100000000000 : Rat))))))))),
    IntervalCert.add (16429 / 5000 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (155377 / 100000 : Rat) (777 / 500 : Rat) (IntervalCert.add (241421 / 100000 : Rat) (24143 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (1414213 / 1000000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (1999999 / 1000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (9999999 / 10000000 : Rat) (1000001 / 1000000 : Rat)))))))

private def values14SpecialCert_90 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (1643 / 500 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (1553 / 1000 : Rat) (7769 / 5000 : Rat) (IntervalCert.add (1207 / 500 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))))),
    IntervalCert.add (829 / 250 : Rat) (100 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (231607 / 100000 : Rat) (2317 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (658037 / 500000 : Rat) (13161 / 10000 : Rat) (IntervalCert.sqrt (4330127 / 2500000 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (299999999 / 100000000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (1999999999 / 1000000000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.sqrt (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)))))))))))

private def values14SpecialCert_91 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (3459 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (1229 / 500 : Rat) (4917 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)))) (IntervalCert.sqrt (5221 / 5000 : Rat) (522137 / 500000 : Rat) (IntervalCert.sqrt (2181 / 2000 : Rat) (272627 / 250000 : Rat) (IntervalCert.sqrt (2973 / 2500 : Rat) (1486509 / 1250000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (1767767 / 1250000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20000001 / 10000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100000001 / 100000000 : Rat)))))))),
    IntervalCert.add (433 / 125 : Rat) (100 : Rat) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat))))) (IntervalCert.sqrt (34641 / 20000 : Rat) (1733 / 1000 : Rat) (IntervalCert.add (2999999 / 1000000 : Rat) (3001 / 1000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (19999999 / 10000000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (100001 / 100000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (100001 / 100000 : Rat)))))))

private def values14SpecialCert_92 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (693 / 200 : Rat) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))) (IntervalCert.sqrt (433 / 250 : Rat) (17321 / 10000 : Rat) (IntervalCert.add (29999 / 10000 : Rat) (30001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))))),
    IntervalCert.add (3479 / 1000 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (4959 / 2000 : Rat) (62 / 25 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.sqrt (147959 / 100000 : Rat) (3699 / 2500 : Rat) (IntervalCert.add (5473 / 2500 : Rat) (218921 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (1189207 / 1000000 : Rat) (148651 / 125000 : Rat) (IntervalCert.sqrt (2828427 / 2000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (19999999 / 10000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.sqrt (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (10000001 / 10000000 : Rat)))))))))))

private def values14SpecialCert_93 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (4237 / 1000 : Rat) (IntervalCert.one (999 / 1000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (809 / 250 : Rat) (32361 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (111803 / 50000 : Rat) (223607 / 100000 : Rat) (IntervalCert.add (499999 / 100000 : Rat) (5000001 / 1000000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.add (3999999 / 1000000 : Rat) (40000001 / 10000000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100000001 / 100000000 : Rat)) (IntervalCert.add (29999999 / 10000000 : Rat) (300000001 / 100000000 : Rat) (IntervalCert.one (99999999 / 100000000 : Rat) (1000000001 / 1000000000 : Rat)) (IntervalCert.add (199999999 / 100000000 : Rat) (2000000001 / 1000000000 : Rat) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)) (IntervalCert.one (999999999 / 1000000000 : Rat) (10000000001 / 10000000000 : Rat)))))))),
    IntervalCert.add (2121 / 500 : Rat) (100 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (283 / 200 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (2001 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)))) (IntervalCert.add (7071 / 2500 : Rat) (2829 / 1000 : Rat) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.sqrt (141421 / 100000 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (100001 / 100000 : Rat))))))

private def values14SpecialCert_94 : IntervalCert × IntervalCert :=
  (IntervalCert.add (0 : Rat) (4243 / 1000 : Rat) (IntervalCert.sqrt (707 / 500 : Rat) (14143 / 10000 : Rat) (IntervalCert.add (19999 / 10000 : Rat) (20001 / 10000 : Rat) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.one (99999 / 100000 : Rat) (100001 / 100000 : Rat)))) (IntervalCert.add (707 / 250 : Rat) (5657 / 2000 : Rat) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)))) (IntervalCert.sqrt (7071 / 5000 : Rat) (70711 / 50000 : Rat) (IntervalCert.add (199999 / 100000 : Rat) (200001 / 100000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.one (999999 / 1000000 : Rat) (1000001 / 1000000 : Rat))))),
    IntervalCert.add (2123 / 500 : Rat) (100 : Rat) (IntervalCert.one (9999 / 10000 : Rat) (1001 / 1000 : Rat)) (IntervalCert.add (6493 / 2000 : Rat) (3247 / 1000 : Rat) (IntervalCert.one (999999 / 1000000 : Rat) (10001 / 10000 : Rat)) (IntervalCert.add (280813 / 125000 : Rat) (11233 / 5000 : Rat) (IntervalCert.one (9999999 / 10000000 : Rat) (100001 / 100000 : Rat)) (IntervalCert.sqrt (12465047 / 10000000 : Rat) (124651 / 100000 : Rat) (IntervalCert.sqrt (155377397 / 100000000 : Rat) (77689 / 50000 : Rat) (IntervalCert.add (60355339 / 25000000 : Rat) (120711 / 50000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (1000001 / 1000000 : Rat)) (IntervalCert.sqrt (707106781 / 500000000 : Rat) (707107 / 500000 : Rat) (IntervalCert.add (1999999999 / 1000000000 : Rat) (2000001 / 1000000 : Rat) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat)) (IntervalCert.one (9999999999 / 10000000000 : Rat) (10000001 / 10000000 : Rat))))))))))

private def values14SpecialCertNat : Nat -> IntervalCert × IntervalCert
  | 0 => values14SpecialCert_0
  | 1 => values14SpecialCert_1
  | 2 => values14SpecialCert_2
  | 3 => values14SpecialCert_3
  | 4 => values14SpecialCert_4
  | 5 => values14SpecialCert_5
  | 6 => values14SpecialCert_6
  | 7 => values14SpecialCert_7
  | 8 => values14SpecialCert_8
  | 9 => values14SpecialCert_9
  | 10 => values14SpecialCert_10
  | 11 => values14SpecialCert_11
  | 12 => values14SpecialCert_12
  | 13 => values14SpecialCert_13
  | 14 => values14SpecialCert_14
  | 15 => values14SpecialCert_15
  | 16 => values14SpecialCert_16
  | 17 => values14SpecialCert_17
  | 18 => values14SpecialCert_18
  | 19 => values14SpecialCert_19
  | 20 => values14SpecialCert_20
  | 21 => values14SpecialCert_21
  | 22 => values14SpecialCert_22
  | 23 => values14SpecialCert_23
  | 24 => values14SpecialCert_24
  | 25 => values14SpecialCert_25
  | 26 => values14SpecialCert_26
  | 27 => values14SpecialCert_27
  | 28 => values14SpecialCert_28
  | 29 => values14SpecialCert_29
  | 30 => values14SpecialCert_30
  | 31 => values14SpecialCert_31
  | 32 => values14SpecialCert_32
  | 33 => values14SpecialCert_33
  | 34 => values14SpecialCert_34
  | 35 => values14SpecialCert_35
  | 36 => values14SpecialCert_36
  | 37 => values14SpecialCert_37
  | 38 => values14SpecialCert_38
  | 39 => values14SpecialCert_39
  | 40 => values14SpecialCert_40
  | 41 => values14SpecialCert_41
  | 42 => values14SpecialCert_42
  | 43 => values14SpecialCert_43
  | 44 => values14SpecialCert_44
  | 45 => values14SpecialCert_45
  | 46 => values14SpecialCert_46
  | 47 => values14SpecialCert_47
  | 48 => values14SpecialCert_48
  | 49 => values14SpecialCert_49
  | 50 => values14SpecialCert_50
  | 51 => values14SpecialCert_51
  | 52 => values14SpecialCert_52
  | 53 => values14SpecialCert_53
  | 54 => values14SpecialCert_54
  | 55 => values14SpecialCert_55
  | 56 => values14SpecialCert_56
  | 57 => values14SpecialCert_57
  | 58 => values14SpecialCert_58
  | 59 => values14SpecialCert_59
  | 60 => values14SpecialCert_60
  | 61 => values14SpecialCert_61
  | 62 => values14SpecialCert_62
  | 63 => values14SpecialCert_63
  | 64 => values14SpecialCert_64
  | 65 => values14SpecialCert_65
  | 66 => values14SpecialCert_66
  | 67 => values14SpecialCert_67
  | 68 => values14SpecialCert_68
  | 69 => values14SpecialCert_69
  | 70 => values14SpecialCert_70
  | 71 => values14SpecialCert_71
  | 72 => values14SpecialCert_72
  | 73 => values14SpecialCert_73
  | 74 => values14SpecialCert_74
  | 75 => values14SpecialCert_75
  | 76 => values14SpecialCert_76
  | 77 => values14SpecialCert_77
  | 78 => values14SpecialCert_78
  | 79 => values14SpecialCert_79
  | 80 => values14SpecialCert_80
  | 81 => values14SpecialCert_81
  | 82 => values14SpecialCert_82
  | 83 => values14SpecialCert_83
  | 84 => values14SpecialCert_84
  | 85 => values14SpecialCert_85
  | 86 => values14SpecialCert_86
  | 87 => values14SpecialCert_87
  | 88 => values14SpecialCert_88
  | 89 => values14SpecialCert_89
  | 90 => values14SpecialCert_90
  | 91 => values14SpecialCert_91
  | 92 => values14SpecialCert_92
  | 93 => values14SpecialCert_93
  | 94 => values14SpecialCert_94
  | _ => values14SpecialCert_0

private def values14SpecialCert (i : Fin 95) :
    IntervalCert × IntervalCert :=
  values14SpecialCertNat i.1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem values14SpecialCert_separated :
    ∀ i : Fin 95,
      (values14SpecialCert i).1.separated (values14SpecialCert i).2 = true := by
  native_decide

set_option linter.unusedTactic false in
theorem values14_special_249 :
    values14 (249 : Fin 455) < values14 (250 : Fin 455) := by
  have hcert := values14SpecialCert_separated (0 : Fin 95)
  change values14SpecialCert_0.1.separated values14SpecialCert_0.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_0.1 values14SpecialCert_0.2 hcert ?_ ?_
  · rw [show values14 (249 : Fin 455) = Real.sqrt (values13 (249 : Fin 264)) by rfl]
    simp only [values14SpecialCert_0, IntervalCert.expr, eval]
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (250 : Fin 455) = 1 + values12 (1 : Fin 154) by rfl]
    simp only [values14SpecialCert_0, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_254 :
    values14 (254 : Fin 455) < values14 (255 : Fin 455) := by
  have hcert := values14SpecialCert_separated (1 : Fin 95)
  change values14SpecialCert_1.1.separated values14SpecialCert_1.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_1.1 values14SpecialCert_1.2 hcert ?_ ?_
  · rw [show values14 (254 : Fin 455) = 1 + values12 (5 : Fin 154) by rfl]
    simp only [values14SpecialCert_1, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    simp only [values14SpecialCert_1, IntervalCert.expr, eval]
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_255 :
    values14 (255 : Fin 455) < values14 (256 : Fin 455) := by
  have hcert := values14SpecialCert_separated (2 : Fin 95)
  change values14SpecialCert_2.1.separated values14SpecialCert_2.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_2.1 values14SpecialCert_2.2 hcert ?_ ?_
  · rw [show values14 (255 : Fin 455) = Real.sqrt (values13 (250 : Fin 264)) by rfl]
    simp only [values14SpecialCert_2, IntervalCert.expr, eval]
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (256 : Fin 455) = 1 + values12 (6 : Fin 154) by rfl]
    simp only [values14SpecialCert_2, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_258 :
    values14 (258 : Fin 455) < values14 (259 : Fin 455) := by
  have hcert := values14SpecialCert_separated (3 : Fin 95)
  change values14SpecialCert_3.1.separated values14SpecialCert_3.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_3.1 values14SpecialCert_3.2 hcert ?_ ?_
  · rw [show values14 (258 : Fin 455) = 1 + values12 (8 : Fin 154) by rfl]
    simp only [values14SpecialCert_3, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    simp only [values14SpecialCert_3, IntervalCert.expr, eval]
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_259 :
    values14 (259 : Fin 455) < values14 (260 : Fin 455) := by
  have hcert := values14SpecialCert_separated (4 : Fin 95)
  change values14SpecialCert_4.1.separated values14SpecialCert_4.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_4.1 values14SpecialCert_4.2 hcert ?_ ?_
  · rw [show values14 (259 : Fin 455) = Real.sqrt (values13 (251 : Fin 264)) by rfl]
    simp only [values14SpecialCert_4, IntervalCert.expr, eval]
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (260 : Fin 455) = 1 + values12 (9 : Fin 154) by rfl]
    simp only [values14SpecialCert_4, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_262 :
    values14 (262 : Fin 455) < values14 (263 : Fin 455) := by
  have hcert := values14SpecialCert_separated (5 : Fin 95)
  change values14SpecialCert_5.1.separated values14SpecialCert_5.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_5.1 values14SpecialCert_5.2 hcert ?_ ?_
  · rw [show values14 (262 : Fin 455) = 1 + values12 (11 : Fin 154) by rfl]
    simp only [values14SpecialCert_5, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    simp only [values14SpecialCert_5, IntervalCert.expr, eval]
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_263 :
    values14 (263 : Fin 455) < values14 (264 : Fin 455) := by
  have hcert := values14SpecialCert_separated (6 : Fin 95)
  change values14SpecialCert_6.1.separated values14SpecialCert_6.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_6.1 values14SpecialCert_6.2 hcert ?_ ?_
  · rw [show values14 (263 : Fin 455) = Real.sqrt (values13 (252 : Fin 264)) by rfl]
    simp only [values14SpecialCert_6, IntervalCert.expr, eval]
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    simp only [values14SpecialCert_6, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_264 :
    values14 (264 : Fin 455) < values14 (265 : Fin 455) := by
  have hcert := values14SpecialCert_separated (7 : Fin 95)
  change values14SpecialCert_7.1.separated values14SpecialCert_7.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_7.1 values14SpecialCert_7.2 hcert ?_ ?_
  · rw [show values14 (264 : Fin 455) = 1 + values12 (12 : Fin 154) by rfl]
    simp only [values14SpecialCert_7, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    simp only [values14SpecialCert_7, IntervalCert.expr, eval]
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_265 :
    values14 (265 : Fin 455) < values14 (266 : Fin 455) := by
  have hcert := values14SpecialCert_separated (8 : Fin 95)
  change values14SpecialCert_8.1.separated values14SpecialCert_8.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_8.1 values14SpecialCert_8.2 hcert ?_ ?_
  · rw [show values14 (265 : Fin 455) = Real.sqrt (values13 (253 : Fin 264)) by rfl]
    simp only [values14SpecialCert_8, IntervalCert.expr, eval]
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (266 : Fin 455) = 1 + values12 (13 : Fin 154) by rfl]
    simp only [values14SpecialCert_8, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_270 :
    values14 (270 : Fin 455) < values14 (271 : Fin 455) := by
  have hcert := values14SpecialCert_separated (9 : Fin 95)
  change values14SpecialCert_9.1.separated values14SpecialCert_9.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_9.1 values14SpecialCert_9.2 hcert ?_ ?_
  · rw [show values14 (270 : Fin 455) = 1 + values12 (17 : Fin 154) by rfl]
    simp only [values14SpecialCert_9, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    simp only [values14SpecialCert_9, IntervalCert.expr, eval]
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_271 :
    values14 (271 : Fin 455) < values14 (272 : Fin 455) := by
  have hcert := values14SpecialCert_separated (10 : Fin 95)
  change values14SpecialCert_10.1.separated values14SpecialCert_10.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_10.1 values14SpecialCert_10.2 hcert ?_ ?_
  · rw [show values14 (271 : Fin 455) = Real.sqrt (values13 (254 : Fin 264)) by rfl]
    simp only [values14SpecialCert_10, IntervalCert.expr, eval]
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (272 : Fin 455) = 1 + values12 (18 : Fin 154) by rfl]
    simp only [values14SpecialCert_10, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_275 :
    values14 (275 : Fin 455) < values14 (276 : Fin 455) := by
  have hcert := values14SpecialCert_separated (11 : Fin 95)
  change values14SpecialCert_11.1.separated values14SpecialCert_11.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_11.1 values14SpecialCert_11.2 hcert ?_ ?_
  · rw [show values14 (275 : Fin 455) = 1 + values12 (21 : Fin 154) by rfl]
    simp only [values14SpecialCert_11, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    simp only [values14SpecialCert_11, IntervalCert.expr, eval]
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_276 :
    values14 (276 : Fin 455) < values14 (277 : Fin 455) := by
  have hcert := values14SpecialCert_separated (12 : Fin 95)
  change values14SpecialCert_12.1.separated values14SpecialCert_12.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_12.1 values14SpecialCert_12.2 hcert ?_ ?_
  · rw [show values14 (276 : Fin 455) = Real.sqrt (values13 (255 : Fin 264)) by rfl]
    simp only [values14SpecialCert_12, IntervalCert.expr, eval]
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (277 : Fin 455) = 1 + values12 (22 : Fin 154) by rfl]
    simp only [values14SpecialCert_12, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_281 :
    values14 (281 : Fin 455) < values14 (282 : Fin 455) := by
  have hcert := values14SpecialCert_separated (13 : Fin 95)
  change values14SpecialCert_13.1.separated values14SpecialCert_13.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_13.1 values14SpecialCert_13.2 hcert ?_ ?_
  · rw [show values14 (281 : Fin 455) = 1 + values12 (26 : Fin 154) by rfl]
    simp only [values14SpecialCert_13, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    simp only [values14SpecialCert_13, IntervalCert.expr, eval]
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_282 :
    values14 (282 : Fin 455) < values14 (283 : Fin 455) := by
  have hcert := values14SpecialCert_separated (14 : Fin 95)
  change values14SpecialCert_14.1.separated values14SpecialCert_14.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_14.1 values14SpecialCert_14.2 hcert ?_ ?_
  · rw [show values14 (282 : Fin 455) = Real.sqrt (values13 (256 : Fin 264)) by rfl]
    simp only [values14SpecialCert_14, IntervalCert.expr, eval]
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14SpecialCert_14, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_283 :
    values14 (283 : Fin 455) < values14 (284 : Fin 455) := by
  have hcert := values14SpecialCert_separated (15 : Fin 95)
  change values14SpecialCert_15.1.separated values14SpecialCert_15.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_15.1 values14SpecialCert_15.2 hcert ?_ ?_
  · rw [show values14 (283 : Fin 455) = values6 (1 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14SpecialCert_15, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (284 : Fin 455) = 1 + values12 (27 : Fin 154) by rfl]
    simp only [values14SpecialCert_15, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_287 :
    values14 (287 : Fin 455) < values14 (288 : Fin 455) := by
  have hcert := values14SpecialCert_separated (16 : Fin 95)
  change values14SpecialCert_16.1.separated values14SpecialCert_16.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_16.1 values14SpecialCert_16.2 hcert ?_ ?_
  · rw [show values14 (287 : Fin 455) = 1 + values12 (30 : Fin 154) by rfl]
    simp only [values14SpecialCert_16, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    simp only [values14SpecialCert_16, IntervalCert.expr, eval]
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_288 :
    values14 (288 : Fin 455) < values14 (289 : Fin 455) := by
  have hcert := values14SpecialCert_separated (17 : Fin 95)
  change values14SpecialCert_17.1.separated values14SpecialCert_17.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_17.1 values14SpecialCert_17.2 hcert ?_ ?_
  · rw [show values14 (288 : Fin 455) = Real.sqrt (values13 (257 : Fin 264)) by rfl]
    simp only [values14SpecialCert_17, IntervalCert.expr, eval]
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    simp only [values14SpecialCert_17, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_289 :
    values14 (289 : Fin 455) < values14 (290 : Fin 455) := by
  have hcert := values14SpecialCert_separated (18 : Fin 95)
  change values14SpecialCert_18.1.separated values14SpecialCert_18.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_18.1 values14SpecialCert_18.2 hcert ?_ ?_
  · rw [show values14 (289 : Fin 455) = values6 (1 : Fin 8) + values7 (2 : Fin 13) by rfl]
    simp only [values14SpecialCert_18, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (290 : Fin 455) = 1 + values12 (31 : Fin 154) by rfl]
    simp only [values14SpecialCert_18, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_292 :
    values14 (292 : Fin 455) < values14 (293 : Fin 455) := by
  have hcert := values14SpecialCert_separated (19 : Fin 95)
  change values14SpecialCert_19.1.separated values14SpecialCert_19.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_19.1 values14SpecialCert_19.2 hcert ?_ ?_
  · rw [show values14 (292 : Fin 455) = 1 + values12 (33 : Fin 154) by rfl]
    simp only [values14SpecialCert_19, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    simp only [values14SpecialCert_19, IntervalCert.expr, eval]
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_293 :
    values14 (293 : Fin 455) < values14 (294 : Fin 455) := by
  have hcert := values14SpecialCert_separated (20 : Fin 95)
  change values14SpecialCert_20.1.separated values14SpecialCert_20.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_20.1 values14SpecialCert_20.2 hcert ?_ ?_
  · rw [show values14 (293 : Fin 455) = Real.sqrt (values13 (258 : Fin 264)) by rfl]
    simp only [values14SpecialCert_20, IntervalCert.expr, eval]
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (294 : Fin 455) = 1 + values12 (34 : Fin 154) by rfl]
    simp only [values14SpecialCert_20, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_295 :
    values14 (295 : Fin 455) < values14 (296 : Fin 455) := by
  have hcert := values14SpecialCert_separated (21 : Fin 95)
  change values14SpecialCert_21.1.separated values14SpecialCert_21.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_21.1 values14SpecialCert_21.2 hcert ?_ ?_
  · rw [show values14 (295 : Fin 455) = 1 + values12 (35 : Fin 154) by rfl]
    simp only [values14SpecialCert_21, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    simp only [values14SpecialCert_21, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_296 :
    values14 (296 : Fin 455) < values14 (297 : Fin 455) := by
  have hcert := values14SpecialCert_separated (22 : Fin 95)
  change values14SpecialCert_22.1.separated values14SpecialCert_22.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_22.1 values14SpecialCert_22.2 hcert ?_ ?_
  · rw [show values14 (296 : Fin 455) = values5 (1 : Fin 5) + values8 (1 : Fin 20) by rfl]
    simp only [values14SpecialCert_22, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (297 : Fin 455) = 1 + values12 (36 : Fin 154) by rfl]
    simp only [values14SpecialCert_22, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_299 :
    values14 (299 : Fin 455) < values14 (300 : Fin 455) := by
  have hcert := values14SpecialCert_separated (23 : Fin 95)
  change values14SpecialCert_23.1.separated values14SpecialCert_23.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_23.1 values14SpecialCert_23.2 hcert ?_ ?_
  · rw [show values14 (299 : Fin 455) = 1 + values12 (38 : Fin 154) by rfl]
    simp only [values14SpecialCert_23, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    simp only [values14SpecialCert_23, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_300 :
    values14 (300 : Fin 455) < values14 (301 : Fin 455) := by
  have hcert := values14SpecialCert_separated (24 : Fin 95)
  change values14SpecialCert_24.1.separated values14SpecialCert_24.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_24.1 values14SpecialCert_24.2 hcert ?_ ?_
  · rw [show values14 (300 : Fin 455) = values5 (1 : Fin 5) + values8 (2 : Fin 20) by rfl]
    simp only [values14SpecialCert_24, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    simp only [values14SpecialCert_24, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_301 :
    values14 (301 : Fin 455) < values14 (302 : Fin 455) := by
  have hcert := values14SpecialCert_separated (25 : Fin 95)
  change values14SpecialCert_25.1.separated values14SpecialCert_25.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_25.1 values14SpecialCert_25.2 hcert ?_ ?_
  · rw [show values14 (301 : Fin 455) = 1 + values12 (39 : Fin 154) by rfl]
    simp only [values14SpecialCert_25, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    simp only [values14SpecialCert_25, IntervalCert.expr, eval]
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_302 :
    values14 (302 : Fin 455) < values14 (303 : Fin 455) := by
  have hcert := values14SpecialCert_separated (26 : Fin 95)
  change values14SpecialCert_26.1.separated values14SpecialCert_26.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_26.1 values14SpecialCert_26.2 hcert ?_ ?_
  · rw [show values14 (302 : Fin 455) = Real.sqrt (values13 (259 : Fin 264)) by rfl]
    simp only [values14SpecialCert_26, IntervalCert.expr, eval]
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (303 : Fin 455) = 1 + values12 (40 : Fin 154) by rfl]
    simp only [values14SpecialCert_26, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_306 :
    values14 (306 : Fin 455) < values14 (307 : Fin 455) := by
  have hcert := values14SpecialCert_separated (27 : Fin 95)
  change values14SpecialCert_27.1.separated values14SpecialCert_27.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_27.1 values14SpecialCert_27.2 hcert ?_ ?_
  · rw [show values14 (306 : Fin 455) = 1 + values12 (43 : Fin 154) by rfl]
    simp only [values14SpecialCert_27, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    simp only [values14SpecialCert_27, IntervalCert.expr, eval]
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_307 :
    values14 (307 : Fin 455) < values14 (308 : Fin 455) := by
  have hcert := values14SpecialCert_separated (28 : Fin 95)
  change values14SpecialCert_28.1.separated values14SpecialCert_28.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_28.1 values14SpecialCert_28.2 hcert ?_ ?_
  · rw [show values14 (307 : Fin 455) = Real.sqrt (values13 (260 : Fin 264)) by rfl]
    simp only [values14SpecialCert_28, IntervalCert.expr, eval]
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    simp only [values14SpecialCert_28, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_308 :
    values14 (308 : Fin 455) < values14 (309 : Fin 455) := by
  have hcert := values14SpecialCert_separated (29 : Fin 95)
  change values14SpecialCert_29.1.separated values14SpecialCert_29.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_29.1 values14SpecialCert_29.2 hcert ?_ ?_
  · rw [show values14 (308 : Fin 455) = values5 (1 : Fin 5) + values8 (3 : Fin 20) by rfl]
    simp only [values14SpecialCert_29, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (309 : Fin 455) = 1 + values12 (44 : Fin 154) by rfl]
    simp only [values14SpecialCert_29, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_312 :
    values14 (312 : Fin 455) < values14 (313 : Fin 455) := by
  have hcert := values14SpecialCert_separated (30 : Fin 95)
  change values14SpecialCert_30.1.separated values14SpecialCert_30.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_30.1 values14SpecialCert_30.2 hcert ?_ ?_
  · rw [show values14 (312 : Fin 455) = 1 + values12 (47 : Fin 154) by rfl]
    simp only [values14SpecialCert_30, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    simp only [values14SpecialCert_30, IntervalCert.expr, eval]
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_313 :
    values14 (313 : Fin 455) < values14 (314 : Fin 455) := by
  have hcert := values14SpecialCert_separated (31 : Fin 95)
  change values14SpecialCert_31.1.separated values14SpecialCert_31.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_31.1 values14SpecialCert_31.2 hcert ?_ ?_
  · rw [show values14 (313 : Fin 455) = Real.sqrt (values13 (261 : Fin 264)) by rfl]
    simp only [values14SpecialCert_31, IntervalCert.expr, eval]
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    simp only [values14SpecialCert_31, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_314 :
    values14 (314 : Fin 455) < values14 (315 : Fin 455) := by
  have hcert := values14SpecialCert_separated (32 : Fin 95)
  change values14SpecialCert_32.1.separated values14SpecialCert_32.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_32.1 values14SpecialCert_32.2 hcert ?_ ?_
  · rw [show values14 (314 : Fin 455) = 1 + values12 (48 : Fin 154) by rfl]
    simp only [values14SpecialCert_32, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    simp only [values14SpecialCert_32, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_315 :
    values14 (315 : Fin 455) < values14 (316 : Fin 455) := by
  have hcert := values14SpecialCert_separated (33 : Fin 95)
  change values14SpecialCert_33.1.separated values14SpecialCert_33.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_33.1 values14SpecialCert_33.2 hcert ?_ ?_
  · rw [show values14 (315 : Fin 455) = values5 (1 : Fin 5) + values8 (4 : Fin 20) by rfl]
    simp only [values14SpecialCert_33, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    simp only [values14SpecialCert_33, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_316 :
    values14 (316 : Fin 455) < values14 (317 : Fin 455) := by
  have hcert := values14SpecialCert_separated (34 : Fin 95)
  change values14SpecialCert_34.1.separated values14SpecialCert_34.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_34.1 values14SpecialCert_34.2 hcert ?_ ?_
  · rw [show values14 (316 : Fin 455) = 1 + values12 (49 : Fin 154) by rfl]
    simp only [values14SpecialCert_34, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    simp only [values14SpecialCert_34, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_317 :
    values14 (317 : Fin 455) < values14 (318 : Fin 455) := by
  have hcert := values14SpecialCert_separated (35 : Fin 95)
  change values14SpecialCert_35.1.separated values14SpecialCert_35.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_35.1 values14SpecialCert_35.2 hcert ?_ ?_
  · rw [show values14 (317 : Fin 455) = values5 (1 : Fin 5) + values8 (5 : Fin 20) by rfl]
    simp only [values14SpecialCert_35, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    simp only [values14SpecialCert_35, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_318 :
    values14 (318 : Fin 455) < values14 (319 : Fin 455) := by
  have hcert := values14SpecialCert_separated (36 : Fin 95)
  change values14SpecialCert_36.1.separated values14SpecialCert_36.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_36.1 values14SpecialCert_36.2 hcert ?_ ?_
  · rw [show values14 (318 : Fin 455) = 1 + values12 (50 : Fin 154) by rfl]
    simp only [values14SpecialCert_36, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14SpecialCert_36, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_319 :
    values14 (319 : Fin 455) < values14 (320 : Fin 455) := by
  have hcert := values14SpecialCert_separated (37 : Fin 95)
  change values14SpecialCert_37.1.separated values14SpecialCert_37.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_37.1 values14SpecialCert_37.2 hcert ?_ ?_
  · rw [show values14 (319 : Fin 455) = values6 (1 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14SpecialCert_37, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (320 : Fin 455) = 1 + values12 (51 : Fin 154) by rfl]
    simp only [values14SpecialCert_37, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_322 :
    values14 (322 : Fin 455) < values14 (323 : Fin 455) := by
  have hcert := values14SpecialCert_separated (38 : Fin 95)
  change values14SpecialCert_38.1.separated values14SpecialCert_38.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_38.1 values14SpecialCert_38.2 hcert ?_ ?_
  · rw [show values14 (322 : Fin 455) = 1 + values12 (53 : Fin 154) by rfl]
    simp only [values14SpecialCert_38, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    simp only [values14SpecialCert_38, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_323 :
    values14 (323 : Fin 455) < values14 (324 : Fin 455) := by
  have hcert := values14SpecialCert_separated (39 : Fin 95)
  change values14SpecialCert_39.1.separated values14SpecialCert_39.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_39.1 values14SpecialCert_39.2 hcert ?_ ?_
  · rw [show values14 (323 : Fin 455) = Real.sqrt 2 + values9 (1 : Fin 33) by rfl]
    simp only [values14SpecialCert_39, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    simp only [values14SpecialCert_39, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_324 :
    values14 (324 : Fin 455) < values14 (325 : Fin 455) := by
  have hcert := values14SpecialCert_separated (40 : Fin 95)
  change values14SpecialCert_40.1.separated values14SpecialCert_40.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_40.1 values14SpecialCert_40.2 hcert ?_ ?_
  · rw [show values14 (324 : Fin 455) = 1 + values12 (54 : Fin 154) by rfl]
    simp only [values14SpecialCert_40, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    simp only [values14SpecialCert_40, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_325 :
    values14 (325 : Fin 455) < values14 (326 : Fin 455) := by
  have hcert := values14SpecialCert_separated (41 : Fin 95)
  change values14SpecialCert_41.1.separated values14SpecialCert_41.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_41.1 values14SpecialCert_41.2 hcert ?_ ?_
  · rw [show values14 (325 : Fin 455) = values5 (1 : Fin 5) + values8 (6 : Fin 20) by rfl]
    simp only [values14SpecialCert_41, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    simp only [values14SpecialCert_41, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_326 :
    values14 (326 : Fin 455) < values14 (327 : Fin 455) := by
  have hcert := values14SpecialCert_separated (42 : Fin 95)
  change values14SpecialCert_42.1.separated values14SpecialCert_42.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_42.1 values14SpecialCert_42.2 hcert ?_ ?_
  · rw [show values14 (326 : Fin 455) = Real.sqrt 2 + values9 (2 : Fin 33) by rfl]
    simp only [values14SpecialCert_42, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (327 : Fin 455) = 1 + values12 (55 : Fin 154) by rfl]
    simp only [values14SpecialCert_42, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_329 :
    values14 (329 : Fin 455) < values14 (330 : Fin 455) := by
  have hcert := values14SpecialCert_separated (43 : Fin 95)
  change values14SpecialCert_43.1.separated values14SpecialCert_43.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_43.1 values14SpecialCert_43.2 hcert ?_ ?_
  · rw [show values14 (329 : Fin 455) = 1 + values12 (57 : Fin 154) by rfl]
    simp only [values14SpecialCert_43, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    simp only [values14SpecialCert_43, IntervalCert.expr, eval]
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_330 :
    values14 (330 : Fin 455) < values14 (331 : Fin 455) := by
  have hcert := values14SpecialCert_separated (44 : Fin 95)
  change values14SpecialCert_44.1.separated values14SpecialCert_44.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_44.1 values14SpecialCert_44.2 hcert ?_ ?_
  · rw [show values14 (330 : Fin 455) = Real.sqrt (values13 (262 : Fin 264)) by rfl]
    simp only [values14SpecialCert_44, IntervalCert.expr, eval]
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    simp only [values14SpecialCert_44, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_331 :
    values14 (331 : Fin 455) < values14 (332 : Fin 455) := by
  have hcert := values14SpecialCert_separated (45 : Fin 95)
  change values14SpecialCert_45.1.separated values14SpecialCert_45.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_45.1 values14SpecialCert_45.2 hcert ?_ ?_
  · rw [show values14 (331 : Fin 455) = 1 + values12 (58 : Fin 154) by rfl]
    simp only [values14SpecialCert_45, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    simp only [values14SpecialCert_45, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_332 :
    values14 (332 : Fin 455) < values14 (333 : Fin 455) := by
  have hcert := values14SpecialCert_separated (46 : Fin 95)
  change values14SpecialCert_46.1.separated values14SpecialCert_46.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_46.1 values14SpecialCert_46.2 hcert ?_ ?_
  · rw [show values14 (332 : Fin 455) = Real.sqrt 2 + values9 (3 : Fin 33) by rfl]
    simp only [values14SpecialCert_46, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (333 : Fin 455) = 1 + values12 (59 : Fin 154) by rfl]
    simp only [values14SpecialCert_46, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_334 :
    values14 (334 : Fin 455) < values14 (335 : Fin 455) := by
  have hcert := values14SpecialCert_separated (47 : Fin 95)
  change values14SpecialCert_47.1.separated values14SpecialCert_47.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_47.1 values14SpecialCert_47.2 hcert ?_ ?_
  · rw [show values14 (334 : Fin 455) = 1 + values12 (60 : Fin 154) by rfl]
    simp only [values14SpecialCert_47, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    simp only [values14SpecialCert_47, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_335 :
    values14 (335 : Fin 455) < values14 (336 : Fin 455) := by
  have hcert := values14SpecialCert_separated (48 : Fin 95)
  change values14SpecialCert_48.1.separated values14SpecialCert_48.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_48.1 values14SpecialCert_48.2 hcert ?_ ?_
  · rw [show values14 (335 : Fin 455) = Real.sqrt 2 + values9 (4 : Fin 33) by rfl]
    simp only [values14SpecialCert_48, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (336 : Fin 455) = 1 + values12 (61 : Fin 154) by rfl]
    simp only [values14SpecialCert_48, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_338 :
    values14 (338 : Fin 455) < values14 (339 : Fin 455) := by
  have hcert := values14SpecialCert_separated (49 : Fin 95)
  change values14SpecialCert_49.1.separated values14SpecialCert_49.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_49.1 values14SpecialCert_49.2 hcert ?_ ?_
  · rw [show values14 (338 : Fin 455) = 1 + values12 (63 : Fin 154) by rfl]
    simp only [values14SpecialCert_49, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    simp only [values14SpecialCert_49, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_339 :
    values14 (339 : Fin 455) < values14 (340 : Fin 455) := by
  have hcert := values14SpecialCert_separated (50 : Fin 95)
  change values14SpecialCert_50.1.separated values14SpecialCert_50.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_50.1 values14SpecialCert_50.2 hcert ?_ ?_
  · rw [show values14 (339 : Fin 455) = Real.sqrt 2 + values9 (5 : Fin 33) by rfl]
    simp only [values14SpecialCert_50, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    simp only [values14SpecialCert_50, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_340 :
    values14 (340 : Fin 455) < values14 (341 : Fin 455) := by
  have hcert := values14SpecialCert_separated (51 : Fin 95)
  change values14SpecialCert_51.1.separated values14SpecialCert_51.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_51.1 values14SpecialCert_51.2 hcert ?_ ?_
  · rw [show values14 (340 : Fin 455) = values5 (1 : Fin 5) + values8 (7 : Fin 20) by rfl]
    simp only [values14SpecialCert_51, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    simp only [values14SpecialCert_51, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_341 :
    values14 (341 : Fin 455) < values14 (342 : Fin 455) := by
  have hcert := values14SpecialCert_separated (52 : Fin 95)
  change values14SpecialCert_52.1.separated values14SpecialCert_52.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_52.1 values14SpecialCert_52.2 hcert ?_ ?_
  · rw [show values14 (341 : Fin 455) = 1 + values12 (64 : Fin 154) by rfl]
    simp only [values14SpecialCert_52, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    simp only [values14SpecialCert_52, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_342 :
    values14 (342 : Fin 455) < values14 (343 : Fin 455) := by
  have hcert := values14SpecialCert_separated (53 : Fin 95)
  change values14SpecialCert_53.1.separated values14SpecialCert_53.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_53.1 values14SpecialCert_53.2 hcert ?_ ?_
  · rw [show values14 (342 : Fin 455) = Real.sqrt 2 + values9 (6 : Fin 33) by rfl]
    simp only [values14SpecialCert_53, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (343 : Fin 455) = 1 + values12 (65 : Fin 154) by rfl]
    simp only [values14SpecialCert_53, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_344 :
    values14 (344 : Fin 455) < values14 (345 : Fin 455) := by
  have hcert := values14SpecialCert_separated (54 : Fin 95)
  change values14SpecialCert_54.1.separated values14SpecialCert_54.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_54.1 values14SpecialCert_54.2 hcert ?_ ?_
  · rw [show values14 (344 : Fin 455) = 1 + values12 (66 : Fin 154) by rfl]
    simp only [values14SpecialCert_54, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    simp only [values14SpecialCert_54, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_345 :
    values14 (345 : Fin 455) < values14 (346 : Fin 455) := by
  have hcert := values14SpecialCert_separated (55 : Fin 95)
  change values14SpecialCert_55.1.separated values14SpecialCert_55.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_55.1 values14SpecialCert_55.2 hcert ?_ ?_
  · rw [show values14 (345 : Fin 455) = Real.sqrt 2 + values9 (7 : Fin 33) by rfl]
    simp only [values14SpecialCert_55, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (346 : Fin 455) = 1 + values12 (67 : Fin 154) by rfl]
    simp only [values14SpecialCert_55, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_349 :
    values14 (349 : Fin 455) < values14 (350 : Fin 455) := by
  have hcert := values14SpecialCert_separated (56 : Fin 95)
  change values14SpecialCert_56.1.separated values14SpecialCert_56.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_56.1 values14SpecialCert_56.2 hcert ?_ ?_
  · rw [show values14 (349 : Fin 455) = 1 + values12 (70 : Fin 154) by rfl]
    simp only [values14SpecialCert_56, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    simp only [values14SpecialCert_56, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_350 :
    values14 (350 : Fin 455) < values14 (351 : Fin 455) := by
  have hcert := values14SpecialCert_separated (57 : Fin 95)
  change values14SpecialCert_57.1.separated values14SpecialCert_57.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_57.1 values14SpecialCert_57.2 hcert ?_ ?_
  · rw [show values14 (350 : Fin 455) = Real.sqrt 2 + values9 (8 : Fin 33) by rfl]
    simp only [values14SpecialCert_57, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (351 : Fin 455) = 1 + values12 (71 : Fin 154) by rfl]
    simp only [values14SpecialCert_57, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_352 :
    values14 (352 : Fin 455) < values14 (353 : Fin 455) := by
  have hcert := values14SpecialCert_separated (58 : Fin 95)
  change values14SpecialCert_58.1.separated values14SpecialCert_58.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_58.1 values14SpecialCert_58.2 hcert ?_ ?_
  · rw [show values14 (352 : Fin 455) = 1 + values12 (72 : Fin 154) by rfl]
    simp only [values14SpecialCert_58, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    simp only [values14SpecialCert_58, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_353 :
    values14 (353 : Fin 455) < values14 (354 : Fin 455) := by
  have hcert := values14SpecialCert_separated (59 : Fin 95)
  change values14SpecialCert_59.1.separated values14SpecialCert_59.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_59.1 values14SpecialCert_59.2 hcert ?_ ?_
  · rw [show values14 (353 : Fin 455) = Real.sqrt 2 + values9 (9 : Fin 33) by rfl]
    simp only [values14SpecialCert_59, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14SpecialCert_59, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_354 :
    values14 (354 : Fin 455) < values14 (355 : Fin 455) := by
  have hcert := values14SpecialCert_separated (60 : Fin 95)
  change values14SpecialCert_60.1.separated values14SpecialCert_60.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_60.1 values14SpecialCert_60.2 hcert ?_ ?_
  · rw [show values14 (354 : Fin 455) = values6 (1 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14SpecialCert_60, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    simp only [values14SpecialCert_60, IntervalCert.expr, eval]
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_355 :
    values14 (355 : Fin 455) < values14 (356 : Fin 455) := by
  have hcert := values14SpecialCert_separated (61 : Fin 95)
  change values14SpecialCert_61.1.separated values14SpecialCert_61.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_61.1 values14SpecialCert_61.2 hcert ?_ ?_
  · rw [show values14 (355 : Fin 455) = Real.sqrt (values13 (263 : Fin 264)) by rfl]
    simp only [values14SpecialCert_61, IntervalCert.expr, eval]
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    simp only [values14SpecialCert_61, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_356 :
    values14 (356 : Fin 455) < values14 (357 : Fin 455) := by
  have hcert := values14SpecialCert_separated (62 : Fin 95)
  change values14SpecialCert_62.1.separated values14SpecialCert_62.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_62.1 values14SpecialCert_62.2 hcert ?_ ?_
  · rw [show values14 (356 : Fin 455) = 1 + values12 (73 : Fin 154) by rfl]
    simp only [values14SpecialCert_62, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    simp only [values14SpecialCert_62, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_357 :
    values14 (357 : Fin 455) < values14 (358 : Fin 455) := by
  have hcert := values14SpecialCert_separated (63 : Fin 95)
  change values14SpecialCert_63.1.separated values14SpecialCert_63.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_63.1 values14SpecialCert_63.2 hcert ?_ ?_
  · rw [show values14 (357 : Fin 455) = Real.sqrt 2 + values9 (10 : Fin 33) by rfl]
    simp only [values14SpecialCert_63, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    simp only [values14SpecialCert_63, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_358 :
    values14 (358 : Fin 455) < values14 (359 : Fin 455) := by
  have hcert := values14SpecialCert_separated (64 : Fin 95)
  change values14SpecialCert_64.1.separated values14SpecialCert_64.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_64.1 values14SpecialCert_64.2 hcert ?_ ?_
  · rw [show values14 (358 : Fin 455) = values5 (1 : Fin 5) + values8 (9 : Fin 20) by rfl]
    simp only [values14SpecialCert_64, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (359 : Fin 455) = 1 + values12 (74 : Fin 154) by rfl]
    simp only [values14SpecialCert_64, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_360 :
    values14 (360 : Fin 455) < values14 (361 : Fin 455) := by
  have hcert := values14SpecialCert_separated (65 : Fin 95)
  change values14SpecialCert_65.1.separated values14SpecialCert_65.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_65.1 values14SpecialCert_65.2 hcert ?_ ?_
  · rw [show values14 (360 : Fin 455) = 1 + values12 (75 : Fin 154) by rfl]
    simp only [values14SpecialCert_65, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    simp only [values14SpecialCert_65, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_361 :
    values14 (361 : Fin 455) < values14 (362 : Fin 455) := by
  have hcert := values14SpecialCert_separated (66 : Fin 95)
  change values14SpecialCert_66.1.separated values14SpecialCert_66.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_66.1 values14SpecialCert_66.2 hcert ?_ ?_
  · rw [show values14 (361 : Fin 455) = Real.sqrt 2 + values9 (11 : Fin 33) by rfl]
    simp only [values14SpecialCert_66, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    simp only [values14SpecialCert_66, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_362 :
    values14 (362 : Fin 455) < values14 (363 : Fin 455) := by
  have hcert := values14SpecialCert_separated (67 : Fin 95)
  change values14SpecialCert_67.1.separated values14SpecialCert_67.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_67.1 values14SpecialCert_67.2 hcert ?_ ?_
  · rw [show values14 (362 : Fin 455) = 1 + values12 (76 : Fin 154) by rfl]
    simp only [values14SpecialCert_67, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    simp only [values14SpecialCert_67, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_363 :
    values14 (363 : Fin 455) < values14 (364 : Fin 455) := by
  have hcert := values14SpecialCert_separated (68 : Fin 95)
  change values14SpecialCert_68.1.separated values14SpecialCert_68.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_68.1 values14SpecialCert_68.2 hcert ?_ ?_
  · rw [show values14 (363 : Fin 455) = values5 (1 : Fin 5) + values8 (10 : Fin 20) by rfl]
    simp only [values14SpecialCert_68, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (364 : Fin 455) = 1 + values12 (77 : Fin 154) by rfl]
    simp only [values14SpecialCert_68, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_366 :
    values14 (366 : Fin 455) < values14 (367 : Fin 455) := by
  have hcert := values14SpecialCert_separated (69 : Fin 95)
  change values14SpecialCert_69.1.separated values14SpecialCert_69.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_69.1 values14SpecialCert_69.2 hcert ?_ ?_
  · rw [show values14 (366 : Fin 455) = 1 + values12 (79 : Fin 154) by rfl]
    simp only [values14SpecialCert_69, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14SpecialCert_69, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_367 :
    values14 (367 : Fin 455) < values14 (368 : Fin 455) := by
  have hcert := values14SpecialCert_separated (70 : Fin 95)
  change values14SpecialCert_70.1.separated values14SpecialCert_70.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_70.1 values14SpecialCert_70.2 hcert ?_ ?_
  · rw [show values14 (367 : Fin 455) = values6 (4 : Fin 8) + values7 (1 : Fin 13) by rfl]
    simp only [values14SpecialCert_70, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (368 : Fin 455) = 1 + values12 (80 : Fin 154) by rfl]
    simp only [values14SpecialCert_70, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_369 :
    values14 (369 : Fin 455) < values14 (370 : Fin 455) := by
  have hcert := values14SpecialCert_separated (71 : Fin 95)
  change values14SpecialCert_71.1.separated values14SpecialCert_71.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_71.1 values14SpecialCert_71.2 hcert ?_ ?_
  · rw [show values14 (369 : Fin 455) = 1 + values12 (81 : Fin 154) by rfl]
    simp only [values14SpecialCert_71, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14SpecialCert_71, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_370 :
    values14 (370 : Fin 455) < values14 (371 : Fin 455) := by
  have hcert := values14SpecialCert_separated (72 : Fin 95)
  change values14SpecialCert_72.1.separated values14SpecialCert_72.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_72.1 values14SpecialCert_72.2 hcert ?_ ?_
  · rw [show values14 (370 : Fin 455) = values6 (1 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14SpecialCert_72, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    simp only [values14SpecialCert_72, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_371 :
    values14 (371 : Fin 455) < values14 (372 : Fin 455) := by
  have hcert := values14SpecialCert_separated (73 : Fin 95)
  change values14SpecialCert_73.1.separated values14SpecialCert_73.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_73.1 values14SpecialCert_73.2 hcert ?_ ?_
  · rw [show values14 (371 : Fin 455) = Real.sqrt 2 + values9 (12 : Fin 33) by rfl]
    simp only [values14SpecialCert_73, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    simp only [values14SpecialCert_73, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_372 :
    values14 (372 : Fin 455) < values14 (373 : Fin 455) := by
  have hcert := values14SpecialCert_separated (74 : Fin 95)
  change values14SpecialCert_74.1.separated values14SpecialCert_74.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_74.1 values14SpecialCert_74.2 hcert ?_ ?_
  · rw [show values14 (372 : Fin 455) = 1 + values12 (82 : Fin 154) by rfl]
    simp only [values14SpecialCert_74, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    simp only [values14SpecialCert_74, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_373 :
    values14 (373 : Fin 455) < values14 (374 : Fin 455) := by
  have hcert := values14SpecialCert_separated (75 : Fin 95)
  change values14SpecialCert_75.1.separated values14SpecialCert_75.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_75.1 values14SpecialCert_75.2 hcert ?_ ?_
  · rw [show values14 (373 : Fin 455) = Real.sqrt 2 + values9 (13 : Fin 33) by rfl]
    simp only [values14SpecialCert_75, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    simp only [values14SpecialCert_75, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_374 :
    values14 (374 : Fin 455) < values14 (375 : Fin 455) := by
  have hcert := values14SpecialCert_separated (76 : Fin 95)
  change values14SpecialCert_76.1.separated values14SpecialCert_76.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_76.1 values14SpecialCert_76.2 hcert ?_ ?_
  · rw [show values14 (374 : Fin 455) = 1 + values12 (83 : Fin 154) by rfl]
    simp only [values14SpecialCert_76, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    simp only [values14SpecialCert_76, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_375 :
    values14 (375 : Fin 455) < values14 (376 : Fin 455) := by
  have hcert := values14SpecialCert_separated (77 : Fin 95)
  change values14SpecialCert_77.1.separated values14SpecialCert_77.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_77.1 values14SpecialCert_77.2 hcert ?_ ?_
  · rw [show values14 (375 : Fin 455) = Real.sqrt 2 + values9 (14 : Fin 33) by rfl]
    simp only [values14SpecialCert_77, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    simp only [values14SpecialCert_77, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_376 :
    values14 (376 : Fin 455) < values14 (377 : Fin 455) := by
  have hcert := values14SpecialCert_separated (78 : Fin 95)
  change values14SpecialCert_78.1.separated values14SpecialCert_78.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_78.1 values14SpecialCert_78.2 hcert ?_ ?_
  · rw [show values14 (376 : Fin 455) = values5 (1 : Fin 5) + values8 (11 : Fin 20) by rfl]
    simp only [values14SpecialCert_78, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (377 : Fin 455) = 1 + values12 (84 : Fin 154) by rfl]
    simp only [values14SpecialCert_78, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_378 :
    values14 (378 : Fin 455) < values14 (379 : Fin 455) := by
  have hcert := values14SpecialCert_separated (79 : Fin 95)
  change values14SpecialCert_79.1.separated values14SpecialCert_79.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_79.1 values14SpecialCert_79.2 hcert ?_ ?_
  · rw [show values14 (378 : Fin 455) = 1 + values12 (85 : Fin 154) by rfl]
    simp only [values14SpecialCert_79, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    simp only [values14SpecialCert_79, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_379 :
    values14 (379 : Fin 455) < values14 (380 : Fin 455) := by
  have hcert := values14SpecialCert_separated (80 : Fin 95)
  change values14SpecialCert_80.1.separated values14SpecialCert_80.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_80.1 values14SpecialCert_80.2 hcert ?_ ?_
  · rw [show values14 (379 : Fin 455) = Real.sqrt 2 + values9 (15 : Fin 33) by rfl]
    simp only [values14SpecialCert_80, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (380 : Fin 455) = 1 + values12 (86 : Fin 154) by rfl]
    simp only [values14SpecialCert_80, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_386 :
    values14 (386 : Fin 455) < values14 (387 : Fin 455) := by
  have hcert := values14SpecialCert_separated (81 : Fin 95)
  change values14SpecialCert_81.1.separated values14SpecialCert_81.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_81.1 values14SpecialCert_81.2 hcert ?_ ?_
  · rw [show values14 (386 : Fin 455) = 1 + values12 (92 : Fin 154) by rfl]
    simp only [values14SpecialCert_81, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14SpecialCert_81, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_387 :
    values14 (387 : Fin 455) < values14 (388 : Fin 455) := by
  have hcert := values14SpecialCert_separated (82 : Fin 95)
  change values14SpecialCert_82.1.separated values14SpecialCert_82.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_82.1 values14SpecialCert_82.2 hcert ?_ ?_
  · rw [show values14 (387 : Fin 455) = values6 (4 : Fin 8) + values7 (4 : Fin 13) by rfl]
    simp only [values14SpecialCert_82, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    simp only [values14SpecialCert_82, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_388 :
    values14 (388 : Fin 455) < values14 (389 : Fin 455) := by
  have hcert := values14SpecialCert_separated (83 : Fin 95)
  change values14SpecialCert_83.1.separated values14SpecialCert_83.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_83.1 values14SpecialCert_83.2 hcert ?_ ?_
  · rw [show values14 (388 : Fin 455) = 1 + values12 (93 : Fin 154) by rfl]
    simp only [values14SpecialCert_83, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    simp only [values14SpecialCert_83, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_389 :
    values14 (389 : Fin 455) < values14 (390 : Fin 455) := by
  have hcert := values14SpecialCert_separated (84 : Fin 95)
  change values14SpecialCert_84.1.separated values14SpecialCert_84.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_84.1 values14SpecialCert_84.2 hcert ?_ ?_
  · rw [show values14 (389 : Fin 455) = Real.sqrt 2 + values9 (16 : Fin 33) by rfl]
    simp only [values14SpecialCert_84, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (390 : Fin 455) = 1 + values12 (94 : Fin 154) by rfl]
    simp only [values14SpecialCert_84, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_394 :
    values14 (394 : Fin 455) < values14 (395 : Fin 455) := by
  have hcert := values14SpecialCert_separated (85 : Fin 95)
  change values14SpecialCert_85.1.separated values14SpecialCert_85.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_85.1 values14SpecialCert_85.2 hcert ?_ ?_
  · rw [show values14 (394 : Fin 455) = 1 + values12 (98 : Fin 154) by rfl]
    simp only [values14SpecialCert_85, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    simp only [values14SpecialCert_85, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_395 :
    values14 (395 : Fin 455) < values14 (396 : Fin 455) := by
  have hcert := values14SpecialCert_separated (86 : Fin 95)
  change values14SpecialCert_86.1.separated values14SpecialCert_86.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_86.1 values14SpecialCert_86.2 hcert ?_ ?_
  · rw [show values14 (395 : Fin 455) = Real.sqrt 2 + values9 (17 : Fin 33) by rfl]
    simp only [values14SpecialCert_86, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (396 : Fin 455) = 1 + values12 (99 : Fin 154) by rfl]
    simp only [values14SpecialCert_86, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_401 :
    values14 (401 : Fin 455) < values14 (402 : Fin 455) := by
  have hcert := values14SpecialCert_separated (87 : Fin 95)
  change values14SpecialCert_87.1.separated values14SpecialCert_87.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_87.1 values14SpecialCert_87.2 hcert ?_ ?_
  · rw [show values14 (401 : Fin 455) = 1 + values12 (104 : Fin 154) by rfl]
    simp only [values14SpecialCert_87, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    simp only [values14SpecialCert_87, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_402 :
    values14 (402 : Fin 455) < values14 (403 : Fin 455) := by
  have hcert := values14SpecialCert_separated (88 : Fin 95)
  change values14SpecialCert_88.1.separated values14SpecialCert_88.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_88.1 values14SpecialCert_88.2 hcert ?_ ?_
  · rw [show values14 (402 : Fin 455) = Real.sqrt 2 + values9 (18 : Fin 33) by rfl]
    simp only [values14SpecialCert_88, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (403 : Fin 455) = 1 + values12 (105 : Fin 154) by rfl]
    simp only [values14SpecialCert_88, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_404 :
    values14 (404 : Fin 455) < values14 (405 : Fin 455) := by
  have hcert := values14SpecialCert_separated (89 : Fin 95)
  change values14SpecialCert_89.1.separated values14SpecialCert_89.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_89.1 values14SpecialCert_89.2 hcert ?_ ?_
  · rw [show values14 (404 : Fin 455) = 1 + values12 (106 : Fin 154) by rfl]
    simp only [values14SpecialCert_89, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14SpecialCert_89, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_405 :
    values14 (405 : Fin 455) < values14 (406 : Fin 455) := by
  have hcert := values14SpecialCert_separated (90 : Fin 95)
  change values14SpecialCert_90.1.separated values14SpecialCert_90.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_90.1 values14SpecialCert_90.2 hcert ?_ ?_
  · rw [show values14 (405 : Fin 455) = values6 (4 : Fin 8) + values7 (6 : Fin 13) by rfl]
    simp only [values14SpecialCert_90, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (406 : Fin 455) = 1 + values12 (107 : Fin 154) by rfl]
    simp only [values14SpecialCert_90, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_413 :
    values14 (413 : Fin 455) < values14 (414 : Fin 455) := by
  have hcert := values14SpecialCert_separated (91 : Fin 95)
  change values14SpecialCert_91.1.separated values14SpecialCert_91.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_91.1 values14SpecialCert_91.2 hcert ?_ ?_
  · rw [show values14 (413 : Fin 455) = 1 + values12 (114 : Fin 154) by rfl]
    simp only [values14SpecialCert_91, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14SpecialCert_91, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_414 :
    values14 (414 : Fin 455) < values14 (415 : Fin 455) := by
  have hcert := values14SpecialCert_separated (92 : Fin 95)
  change values14SpecialCert_92.1.separated values14SpecialCert_92.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_92.1 values14SpecialCert_92.2 hcert ?_ ?_
  · rw [show values14 (414 : Fin 455) = values6 (4 : Fin 8) + values7 (7 : Fin 13) by rfl]
    simp only [values14SpecialCert_92, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (415 : Fin 455) = 1 + values12 (115 : Fin 154) by rfl]
    simp only [values14SpecialCert_92, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_437 :
    values14 (437 : Fin 455) < values14 (438 : Fin 455) := by
  have hcert := values14SpecialCert_separated (93 : Fin 95)
  change values14SpecialCert_93.1.separated values14SpecialCert_93.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_93.1 values14SpecialCert_93.2 hcert ?_ ?_
  · rw [show values14 (437 : Fin 455) = 1 + values12 (137 : Fin 154) by rfl]
    simp only [values14SpecialCert_93, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    simp only [values14SpecialCert_93, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

set_option linter.unusedTactic false in
theorem values14_special_438 :
    values14 (438 : Fin 455) < values14 (439 : Fin 455) := by
  have hcert := values14SpecialCert_separated (94 : Fin 95)
  change values14SpecialCert_94.1.separated values14SpecialCert_94.2 = true at hcert
  refine IntervalCert.lt_of_separated values14SpecialCert_94.1 values14SpecialCert_94.2 hcert ?_ ?_
  · rw [show values14 (438 : Fin 455) = Real.sqrt 2 + values9 (27 : Fin 33) by rfl]
    simp only [values14SpecialCert_94, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf
  · rw [show values14 (439 : Fin 455) = 1 + values12 (138 : Fin 154) by rfl]
    simp only [values14SpecialCert_94, IntervalCert.expr, eval]
    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf

end Expr
end A158415
end LeanProofs
