import LeanProofs.A158415FifteenTable

/-!
# Binary size-fifteen range lemmas for OEIS A158415

This module contains generated candidate-index certificates for inclusions
from recursive candidate families into the size-15 representative table.
-/

namespace LeanProofs
namespace A158415
namespace Expr

open Set

set_option maxRecDepth 10000
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
def values5_add_values9_mem_range_values15_indexNat : Nat -> Nat -> Nat
  | 0, 0 => 430
  | 0, 1 => 439
  | 0, 2 => 444
  | 0, 3 => 454
  | 0, 4 => 467
  | 0, 5 => 472
  | 0, 6 => 483
  | 0, 7 => 493
  | 0, 8 => 500
  | 0, 9 => 512
  | 0, 10 => 521
  | 0, 11 => 536
  | 0, 12 => 554
  | 0, 13 => 567
  | 0, 14 => 576
  | 0, 15 => 592
  | 0, 16 => 616
  | 0, 17 => 626
  | 0, 18 => 644
  | 0, 19 => 658
  | 0, 20 => 669
  | 0, 21 => 676
  | 0, 22 => 689
  | 0, 23 => 705
  | 0, 24 => 710
  | 0, 25 => 725
  | 0, 26 => 736
  | 0, 27 => 741
  | 0, 28 => 747
  | 0, 29 => 758
  | 0, 30 => 765
  | 0, 31 => 776
  | 0, 32 => 786
  | 1, 0 => 500
  | 1, 1 => 506
  | 1, 2 => 511
  | 1, 3 => 516
  | 1, 4 => 526
  | 1, 5 => 531
  | 1, 6 => 535
  | 1, 7 => 542
  | 1, 8 => 548
  | 1, 9 => 552
  | 1, 10 => 564
  | 1, 11 => 583
  | 1, 12 => 604
  | 1, 13 => 611
  | 1, 14 => 618
  | 1, 15 => 628
  | 1, 16 => 642
  | 1, 17 => 652
  | 1, 18 => 668
  | 1, 19 => 689
  | 1, 20 => 695
  | 1, 21 => 701
  | 1, 22 => 709
  | 1, 23 => 723
  | 1, 24 => 729
  | 1, 25 => 737
  | 1, 26 => 744
  | 1, 27 => 749
  | 1, 28 => 758
  | 1, 29 => 764
  | 1, 30 => 771
  | 1, 31 => 780
  | 1, 32 => 787
  | 2, 0 => 554
  | 2, 1 => 559
  | 2, 2 => 565
  | 2, 3 => 573
  | 2, 4 => 578
  | 2, 5 => 582
  | 2, 6 => 588
  | 2, 7 => 594
  | 2, 8 => 604
  | 2, 9 => 609
  | 2, 10 => 617
  | 2, 11 => 625
  | 2, 12 => 641
  | 2, 13 => 645
  | 2, 14 => 650
  | 2, 15 => 656
  | 2, 16 => 674
  | 2, 17 => 684
  | 2, 18 => 699
  | 2, 19 => 710
  | 2, 20 => 716
  | 2, 21 => 722
  | 2, 22 => 729
  | 2, 23 => 735
  | 2, 24 => 741
  | 2, 25 => 746
  | 2, 26 => 756
  | 2, 27 => 761
  | 2, 28 => 765
  | 2, 29 => 771
  | 2, 30 => 774
  | 2, 31 => 782
  | 2, 32 => 788
  | 3, 0 => 658
  | 3, 1 => 661
  | 3, 2 => 664
  | 3, 3 => 669
  | 3, 4 => 675
  | 3, 5 => 676
  | 3, 6 => 682
  | 3, 7 => 685
  | 3, 8 => 689
  | 3, 9 => 694
  | 3, 10 => 698
  | 3, 11 => 705
  | 3, 12 => 710
  | 3, 13 => 714
  | 3, 14 => 719
  | 3, 15 => 725
  | 3, 16 => 732
  | 3, 17 => 736
  | 3, 18 => 742
  | 3, 19 => 747
  | 3, 20 => 751
  | 3, 21 => 753
  | 3, 22 => 758
  | 3, 23 => 763
  | 3, 24 => 765
  | 3, 25 => 770
  | 3, 26 => 773
  | 3, 27 => 774
  | 3, 28 => 776
  | 3, 29 => 780
  | 3, 30 => 782
  | 3, 31 => 786
  | 3, 32 => 789
  | 4, 0 => 747
  | 4, 1 => 748
  | 4, 2 => 750
  | 4, 3 => 751
  | 4, 4 => 752
  | 4, 5 => 753
  | 4, 6 => 755
  | 4, 7 => 757
  | 4, 8 => 758
  | 4, 9 => 759
  | 4, 10 => 762
  | 4, 11 => 763
  | 4, 12 => 765
  | 4, 13 => 766
  | 4, 14 => 768
  | 4, 15 => 770
  | 4, 16 => 772
  | 4, 17 => 773
  | 4, 18 => 775
  | 4, 19 => 776
  | 4, 20 => 777
  | 4, 21 => 778
  | 4, 22 => 780
  | 4, 23 => 781
  | 4, 24 => 782
  | 4, 25 => 783
  | 4, 26 => 784
  | 4, 27 => 785
  | 4, 28 => 786
  | 4, 29 => 787
  | 4, 30 => 788
  | 4, 31 => 789
  | 4, 32 => 790
  | _, _ => 0

def values5_add_values9_mem_range_values15_index (i : Fin 5) (j : Fin 33) : Fin 791 :=
  Fin.ofNat 791 (values5_add_values9_mem_range_values15_indexNat i.1 j.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem values5_add_values9_mem_range_values15_index_spec (i : Fin 5) (j : Fin 33) :
    values15 (values5_add_values9_mem_range_values15_index i j) = values5 i + values9 j := by
  fin_cases i <;> fin_cases j
  next =>
    change Real.sqrt (values14 (430 : Fin 455)) = values5 (0 : Fin 5) + values9 (0 : Fin 33)
    rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (8 : Fin 264) = values5 (0 : Fin 5) + values9 (1 : Fin 33)
    rw [show values13 (8 : Fin 264) = Real.sqrt (values12 (8 : Fin 154)) by rfl]
    rw [show values12 (8 : Fin 154) = Real.sqrt (values11 (8 : Fin 91)) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (12 : Fin 264) = values5 (0 : Fin 5) + values9 (2 : Fin 33)
    rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
    rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (19 : Fin 264) = values5 (0 : Fin 5) + values9 (3 : Fin 33)
    rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
    rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (28 : Fin 264) = values5 (0 : Fin 5) + values9 (4 : Fin 33)
    rw [show values13 (28 : Fin 264) = Real.sqrt (values12 (28 : Fin 154)) by rfl]
    rw [show values12 (28 : Fin 154) = Real.sqrt (values11 (28 : Fin 91)) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (31 : Fin 264) = values5 (0 : Fin 5) + values9 (5 : Fin 33)
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (40 : Fin 264) = values5 (0 : Fin 5) + values9 (6 : Fin 33)
    rw [show values13 (40 : Fin 264) = Real.sqrt (values12 (40 : Fin 154)) by rfl]
    rw [show values12 (40 : Fin 154) = Real.sqrt (values11 (40 : Fin 91)) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (46 : Fin 264) = values5 (0 : Fin 5) + values9 (7 : Fin 33)
    rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
    rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values5 (0 : Fin 5) + values9 (8 : Fin 33)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (60 : Fin 264) = values5 (0 : Fin 5) + values9 (9 : Fin 33)
    rw [show values13 (60 : Fin 264) = Real.sqrt (values12 (60 : Fin 154)) by rfl]
    rw [show values12 (60 : Fin 154) = Real.sqrt (values11 (60 : Fin 91)) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (66 : Fin 264) = values5 (0 : Fin 5) + values9 (10 : Fin 33)
    rw [show values13 (66 : Fin 264) = Real.sqrt (values12 (66 : Fin 154)) by rfl]
    rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (76 : Fin 264) = values5 (0 : Fin 5) + values9 (11 : Fin 33)
    rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
    rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values5 (0 : Fin 5) + values9 (12 : Fin 33)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (95 : Fin 264) = values5 (0 : Fin 5) + values9 (13 : Fin 33)
    rw [show values13 (95 : Fin 264) = Real.sqrt (values12 (95 : Fin 154)) by rfl]
    rw [show values12 (95 : Fin 154) = 1 + values10 (8 : Fin 54) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (100 : Fin 264) = values5 (0 : Fin 5) + values9 (14 : Fin 33)
    rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
    rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (110 : Fin 264) = values5 (0 : Fin 5) + values9 (15 : Fin 33)
    rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
    rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (124 : Fin 264) = values5 (0 : Fin 5) + values9 (16 : Fin 33)
    rw [show values13 (124 : Fin 264) = Real.sqrt (values12 (124 : Fin 154)) by rfl]
    rw [show values12 (124 : Fin 154) = 1 + values10 (28 : Fin 54) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (130 : Fin 264) = values5 (0 : Fin 5) + values9 (17 : Fin 33)
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (140 : Fin 264) = values5 (0 : Fin 5) + values9 (18 : Fin 33)
    rw [show values13 (140 : Fin 264) = Real.sqrt (values12 (140 : Fin 154)) by rfl]
    rw [show values12 (140 : Fin 154) = 1 + values10 (40 : Fin 54) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values5 (0 : Fin 5) + values9 (19 : Fin 33)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (155 : Fin 264) = values5 (0 : Fin 5) + values9 (20 : Fin 33)
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values5 (0 : Fin 5) + values9 (21 : Fin 33)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values5 (0 : Fin 5) + values9 (22 : Fin 33)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (182 : Fin 264) = values5 (0 : Fin 5) + values9 (23 : Fin 33)
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values5 (0 : Fin 5) + values9 (24 : Fin 33)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (201 : Fin 264) = values5 (0 : Fin 5) + values9 (25 : Fin 33)
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values5 (0 : Fin 5) + values9 (26 : Fin 33)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values5 (0 : Fin 5) + values9 (27 : Fin 33)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values5 (0 : Fin 5) + values9 (28 : Fin 33)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values5 (0 : Fin 5) + values9 (29 : Fin 33)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values5 (0 : Fin 5) + values9 (30 : Fin 33)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values5 (0 : Fin 5) + values9 (31 : Fin 33)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values5 (0 : Fin 5) + values9 (32 : Fin 33)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values5 (1 : Fin 5) + values9 (0 : Fin 33)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
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
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values5 (1 : Fin 5) + values9 (12 : Fin 33)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next =>
    change 1 + values13 (170 : Fin 264) = values5 (1 : Fin 5) + values9 (19 : Fin 33)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (174 : Fin 264) = values5 (1 : Fin 5) + values9 (20 : Fin 33)
    rw [show values13 (174 : Fin 264) = values5 (1 : Fin 5) + values7 (1 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (179 : Fin 264) = values5 (1 : Fin 5) + values9 (21 : Fin 33)
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (186 : Fin 264) = values5 (1 : Fin 5) + values9 (22 : Fin 33)
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (199 : Fin 264) = values5 (1 : Fin 5) + values9 (23 : Fin 33)
    rw [show values13 (199 : Fin 264) = values5 (1 : Fin 5) + values7 (4 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values5 (1 : Fin 5) + values9 (24 : Fin 33)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (212 : Fin 264) = values5 (1 : Fin 5) + values9 (25 : Fin 33)
    rw [show values13 (212 : Fin 264) = values5 (1 : Fin 5) + values7 (6 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (219 : Fin 264) = values5 (1 : Fin 5) + values9 (26 : Fin 33)
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (43 : Fin 54) = values5 (1 : Fin 5) + values9 (27 : Fin 33)
    rw [show values10 (43 : Fin 54) = Real.sqrt 2 + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values5 (1 : Fin 5) + values9 (28 : Fin 33)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (237 : Fin 264) = values5 (1 : Fin 5) + values9 (29 : Fin 33)
    rw [show values13 (237 : Fin 264) = 1 + values11 (65 : Fin 91) by rfl]
    rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values5 (1 : Fin 5) + values9 (30 : Fin 33)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values5 (1 : Fin 5) + values9 (31 : Fin 33)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (260 : Fin 264) = values5 (1 : Fin 5) + values9 (32 : Fin 33)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values5 (2 : Fin 5) + values9 (0 : Fin 33)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (2 : Fin 54) = values5 (2 : Fin 5) + values9 (1 : Fin 33)
    rw [show values10 (2 : Fin 54) = Real.sqrt (values9 (2 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (3 : Fin 54) = values5 (2 : Fin 5) + values9 (2 : Fin 33)
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (5 : Fin 54) = values5 (2 : Fin 5) + values9 (3 : Fin 33)
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (7 : Fin 54) = values5 (2 : Fin 5) + values9 (4 : Fin 33)
    rw [show values10 (7 : Fin 54) = Real.sqrt (values9 (7 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (8 : Fin 54) = values5 (2 : Fin 5) + values9 (5 : Fin 33)
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (10 : Fin 54) = values5 (2 : Fin 5) + values9 (6 : Fin 33)
    rw [show values10 (10 : Fin 54) = Real.sqrt (values9 (10 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (11 : Fin 54) = values5 (2 : Fin 5) + values9 (7 : Fin 33)
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values5 (2 : Fin 5) + values9 (8 : Fin 33)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (14 : Fin 54) = values5 (2 : Fin 5) + values9 (9 : Fin 33)
    rw [show values10 (14 : Fin 54) = Real.sqrt (values9 (14 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (15 : Fin 54) = values5 (2 : Fin 5) + values9 (10 : Fin 33)
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (17 : Fin 54) = values5 (2 : Fin 5) + values9 (11 : Fin 33)
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (19 : Fin 54) = values5 (2 : Fin 5) + values9 (12 : Fin 33)
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (21 : Fin 54) = values5 (2 : Fin 5) + values9 (13 : Fin 33)
    rw [show values10 (21 : Fin 54) = Real.sqrt (values9 (21 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (22 : Fin 54) = values5 (2 : Fin 5) + values9 (14 : Fin 33)
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (24 : Fin 54) = values5 (2 : Fin 5) + values9 (15 : Fin 33)
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (26 : Fin 54) = values5 (2 : Fin 5) + values9 (16 : Fin 33)
    rw [show values10 (26 : Fin 54) = Real.sqrt (values9 (26 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (28 : Fin 54) = values5 (2 : Fin 5) + values9 (17 : Fin 33)
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (30 : Fin 54) = values5 (2 : Fin 5) + values9 (18 : Fin 33)
    rw [show values10 (30 : Fin 54) = Real.sqrt (values9 (30 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values5 (2 : Fin 5) + values9 (19 : Fin 33)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (193 : Fin 264) = values5 (2 : Fin 5) + values9 (20 : Fin 33)
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values5 (2 : Fin 5) + values9 (21 : Fin 33)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values5 (2 : Fin 5) + values9 (22 : Fin 33)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (210 : Fin 264) = values5 (2 : Fin 5) + values9 (23 : Fin 33)
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values5 (2 : Fin 5) + values9 (24 : Fin 33)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (221 : Fin 264) = values5 (2 : Fin 5) + values9 (25 : Fin 33)
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values5 (2 : Fin 5) + values9 (26 : Fin 33)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (45 : Fin 54) = values5 (2 : Fin 5) + values9 (27 : Fin 33)
    rw [show values10 (45 : Fin 54) = Real.sqrt 2 + values5 (2 : Fin 5) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values5 (2 : Fin 5) + values9 (28 : Fin 33)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values5 (2 : Fin 5) + values9 (29 : Fin 33)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (247 : Fin 264) = values5 (2 : Fin 5) + values9 (30 : Fin 33)
    rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
    rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values5 (2 : Fin 5) + values9 (31 : Fin 33)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values5 (2 : Fin 5) + values9 (32 : Fin 33)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values5 (3 : Fin 5) + values9 (0 : Fin 33)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (149 : Fin 264) = values5 (3 : Fin 5) + values9 (1 : Fin 33)
    rw [show values13 (149 : Fin 264) = 1 + values11 (3 : Fin 91) by rfl]
    rw [show values11 (3 : Fin 91) = Real.sqrt (values10 (3 : Fin 54)) by rfl]
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (151 : Fin 264) = values5 (3 : Fin 5) + values9 (2 : Fin 33)
    rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
    rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (155 : Fin 264) = values5 (3 : Fin 5) + values9 (3 : Fin 33)
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (159 : Fin 264) = values5 (3 : Fin 5) + values9 (4 : Fin 33)
    rw [show values13 (159 : Fin 264) = 1 + values11 (11 : Fin 91) by rfl]
    rw [show values11 (11 : Fin 91) = Real.sqrt (values10 (11 : Fin 54)) by rfl]
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values5 (3 : Fin 5) + values9 (5 : Fin 33)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (164 : Fin 264) = values5 (3 : Fin 5) + values9 (6 : Fin 33)
    rw [show values13 (164 : Fin 264) = 1 + values11 (15 : Fin 91) by rfl]
    rw [show values11 (15 : Fin 91) = Real.sqrt (values10 (15 : Fin 54)) by rfl]
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (166 : Fin 264) = values5 (3 : Fin 5) + values9 (7 : Fin 33)
    rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
    rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values5 (3 : Fin 5) + values9 (8 : Fin 33)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (173 : Fin 264) = values5 (3 : Fin 5) + values9 (9 : Fin 33)
    rw [show values13 (173 : Fin 264) = 1 + values11 (22 : Fin 91) by rfl]
    rw [show values11 (22 : Fin 91) = Real.sqrt (values10 (22 : Fin 54)) by rfl]
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (177 : Fin 264) = values5 (3 : Fin 5) + values9 (10 : Fin 33)
    rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
    rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (182 : Fin 264) = values5 (3 : Fin 5) + values9 (11 : Fin 33)
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values5 (3 : Fin 5) + values9 (12 : Fin 33)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (191 : Fin 264) = values5 (3 : Fin 5) + values9 (13 : Fin 33)
    rw [show values13 (191 : Fin 264) = 1 + values11 (34 : Fin 91) by rfl]
    rw [show values11 (34 : Fin 91) = Real.sqrt (values10 (34 : Fin 54)) by rfl]
    rw [show values10 (34 : Fin 54) = 1 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (195 : Fin 264) = values5 (3 : Fin 5) + values9 (14 : Fin 33)
    rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
    rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (201 : Fin 264) = values5 (3 : Fin 5) + values9 (15 : Fin 33)
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (207 : Fin 264) = values5 (3 : Fin 5) + values9 (16 : Fin 33)
    rw [show values13 (207 : Fin 264) = 1 + values11 (44 : Fin 91) by rfl]
    rw [show values11 (44 : Fin 91) = Real.sqrt (values10 (44 : Fin 54)) by rfl]
    rw [show values10 (44 : Fin 54) = 1 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values5 (3 : Fin 5) + values9 (17 : Fin 33)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (217 : Fin 264) = values5 (3 : Fin 5) + values9 (18 : Fin 33)
    rw [show values13 (217 : Fin 264) = 1 + values11 (49 : Fin 91) by rfl]
    rw [show values11 (49 : Fin 91) = Real.sqrt (values10 (49 : Fin 54)) by rfl]
    rw [show values10 (49 : Fin 54) = 1 + values8 (15 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values5 (3 : Fin 5) + values9 (19 : Fin 33)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (225 : Fin 264) = values5 (3 : Fin 5) + values9 (20 : Fin 33)
    rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values5 (3 : Fin 5) + values9 (21 : Fin 33)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values5 (3 : Fin 5) + values9 (22 : Fin 33)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (236 : Fin 264) = values5 (3 : Fin 5) + values9 (23 : Fin 33)
    rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values5 (3 : Fin 5) + values9 (24 : Fin 33)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (243 : Fin 264) = values5 (3 : Fin 5) + values9 (25 : Fin 33)
    rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values5 (3 : Fin 5) + values9 (26 : Fin 33)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (247 : Fin 264) = values5 (3 : Fin 5) + values9 (27 : Fin 33)
    rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
    rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values5 (3 : Fin 5) + values9 (28 : Fin 33)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values5 (3 : Fin 5) + values9 (29 : Fin 33)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values5 (3 : Fin 5) + values9 (30 : Fin 33)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values5 (3 : Fin 5) + values9 (31 : Fin 33)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (262 : Fin 264) = values5 (3 : Fin 5) + values9 (32 : Fin 33)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values5 (4 : Fin 5) + values9 (0 : Fin 33)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (223 : Fin 264) = values5 (4 : Fin 5) + values9 (1 : Fin 33)
    rw [show values13 (223 : Fin 264) = 1 + values11 (52 : Fin 91) by rfl]
    rw [show values11 (52 : Fin 91) = 1 + values9 (1 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (224 : Fin 264) = values5 (4 : Fin 5) + values9 (2 : Fin 33)
    rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
    rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (225 : Fin 264) = values5 (4 : Fin 5) + values9 (3 : Fin 33)
    rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (226 : Fin 264) = values5 (4 : Fin 5) + values9 (4 : Fin 33)
    rw [show values13 (226 : Fin 264) = 1 + values11 (55 : Fin 91) by rfl]
    rw [show values11 (55 : Fin 91) = 1 + values9 (4 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values5 (4 : Fin 5) + values9 (5 : Fin 33)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (229 : Fin 264) = values5 (4 : Fin 5) + values9 (6 : Fin 33)
    rw [show values13 (229 : Fin 264) = 1 + values11 (58 : Fin 91) by rfl]
    rw [show values11 (58 : Fin 91) = 1 + values9 (6 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (231 : Fin 264) = values5 (4 : Fin 5) + values9 (7 : Fin 33)
    rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
    rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values5 (4 : Fin 5) + values9 (8 : Fin 33)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (233 : Fin 264) = values5 (4 : Fin 5) + values9 (9 : Fin 33)
    rw [show values13 (233 : Fin 264) = 1 + values11 (61 : Fin 91) by rfl]
    rw [show values11 (61 : Fin 91) = 1 + values9 (9 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (235 : Fin 264) = values5 (4 : Fin 5) + values9 (10 : Fin 33)
    rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
    rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (236 : Fin 264) = values5 (4 : Fin 5) + values9 (11 : Fin 33)
    rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values5 (4 : Fin 5) + values9 (12 : Fin 33)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (239 : Fin 264) = values5 (4 : Fin 5) + values9 (13 : Fin 33)
    rw [show values13 (239 : Fin 264) = 1 + values11 (67 : Fin 91) by rfl]
    rw [show values11 (67 : Fin 91) = 1 + values9 (13 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (241 : Fin 264) = values5 (4 : Fin 5) + values9 (14 : Fin 33)
    rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
    rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (243 : Fin 264) = values5 (4 : Fin 5) + values9 (15 : Fin 33)
    rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (245 : Fin 264) = values5 (4 : Fin 5) + values9 (16 : Fin 33)
    rw [show values13 (245 : Fin 264) = 1 + values11 (72 : Fin 91) by rfl]
    rw [show values11 (72 : Fin 91) = 1 + values9 (16 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values5 (4 : Fin 5) + values9 (17 : Fin 33)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (248 : Fin 264) = values5 (4 : Fin 5) + values9 (18 : Fin 33)
    rw [show values13 (248 : Fin 264) = 1 + values11 (75 : Fin 91) by rfl]
    rw [show values11 (75 : Fin 91) = 1 + values9 (18 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values5 (4 : Fin 5) + values9 (19 : Fin 33)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (250 : Fin 264) = values5 (4 : Fin 5) + values9 (20 : Fin 33)
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (251 : Fin 264) = values5 (4 : Fin 5) + values9 (21 : Fin 33)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values5 (4 : Fin 5) + values9 (22 : Fin 33)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (254 : Fin 264) = values5 (4 : Fin 5) + values9 (23 : Fin 33)
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values5 (4 : Fin 5) + values9 (24 : Fin 33)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (256 : Fin 264) = values5 (4 : Fin 5) + values9 (25 : Fin 33)
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (257 : Fin 264) = values5 (4 : Fin 5) + values9 (26 : Fin 33)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (258 : Fin 264) = values5 (4 : Fin 5) + values9 (27 : Fin 33)
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values5 (4 : Fin 5) + values9 (28 : Fin 33)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (260 : Fin 264) = values5 (4 : Fin 5) + values9 (29 : Fin 33)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values5 (4 : Fin 5) + values9 (30 : Fin 33)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (262 : Fin 264) = values5 (4 : Fin 5) + values9 (31 : Fin 33)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (263 : Fin 264) = values5 (4 : Fin 5) + values9 (32 : Fin 33)
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem values5_add_values9_mem_range_values15 (i : Fin 5) (j : Fin 33) :
    (Set.range values15) (values5 i + values9 j) := by
  exact ⟨values5_add_values9_mem_range_values15_index i j, values5_add_values9_mem_range_values15_index_spec i j⟩

def values6_add_values8_mem_range_values15_indexNat : Nat -> Nat -> Nat
  | 0, 0 => 430
  | 0, 1 => 444
  | 0, 2 => 454
  | 0, 3 => 472
  | 0, 4 => 493
  | 0, 5 => 500
  | 0, 6 => 521
  | 0, 7 => 536
  | 0, 8 => 554
  | 0, 9 => 576
  | 0, 10 => 592
  | 0, 11 => 626
  | 0, 12 => 658
  | 0, 13 => 676
  | 0, 14 => 689
  | 0, 15 => 710
  | 0, 16 => 736
  | 0, 17 => 747
  | 0, 18 => 765
  | 0, 19 => 776
  | 1, 0 => 472
  | 1, 1 => 482
  | 1, 2 => 490
  | 1, 3 => 499
  | 1, 4 => 519
  | 1, 5 => 531
  | 1, 6 => 543
  | 1, 7 => 553
  | 1, 8 => 582
  | 1, 9 => 598
  | 1, 10 => 613
  | 1, 11 => 640
  | 1, 12 => 676
  | 1, 13 => 688
  | 1, 14 => 701
  | 1, 15 => 722
  | 1, 16 => 740
  | 1, 17 => 753
  | 1, 18 => 769
  | 1, 19 => 778
  | 2, 0 => 500
  | 2, 1 => 511
  | 2, 2 => 516
  | 2, 3 => 531
  | 2, 4 => 542
  | 2, 5 => 548
  | 2, 6 => 564
  | 2, 7 => 583
  | 2, 8 => 604
  | 2, 9 => 618
  | 2, 10 => 628
  | 2, 11 => 652
  | 2, 12 => 689
  | 2, 13 => 701
  | 2, 14 => 709
  | 2, 15 => 729
  | 2, 16 => 744
  | 2, 17 => 758
  | 2, 18 => 771
  | 2, 19 => 780
  | 3, 0 => 554
  | 3, 1 => 565
  | 3, 2 => 573
  | 3, 3 => 582
  | 3, 4 => 594
  | 3, 5 => 604
  | 3, 6 => 617
  | 3, 7 => 625
  | 3, 8 => 641
  | 3, 9 => 650
  | 3, 10 => 656
  | 3, 11 => 684
  | 3, 12 => 710
  | 3, 13 => 722
  | 3, 14 => 729
  | 3, 15 => 741
  | 3, 16 => 756
  | 3, 17 => 765
  | 3, 18 => 774
  | 3, 19 => 782
  | 4, 0 => 626
  | 4, 1 => 630
  | 4, 2 => 635
  | 4, 3 => 640
  | 4, 4 => 648
  | 4, 5 => 652
  | 4, 6 => 657
  | 4, 7 => 671
  | 4, 8 => 684
  | 4, 9 => 693
  | 4, 10 => 703
  | 4, 11 => 717
  | 4, 12 => 736
  | 4, 13 => 740
  | 4, 14 => 744
  | 4, 15 => 756
  | 4, 16 => 767
  | 4, 17 => 773
  | 4, 18 => 779
  | 4, 19 => 784
  | 5, 0 => 658
  | 5, 1 => 664
  | 5, 2 => 669
  | 5, 3 => 676
  | 5, 4 => 685
  | 5, 5 => 689
  | 5, 6 => 698
  | 5, 7 => 705
  | 5, 8 => 710
  | 5, 9 => 719
  | 5, 10 => 725
  | 5, 11 => 736
  | 5, 12 => 747
  | 5, 13 => 753
  | 5, 14 => 758
  | 5, 15 => 765
  | 5, 16 => 773
  | 5, 17 => 776
  | 5, 18 => 782
  | 5, 19 => 786
  | 6, 0 => 710
  | 6, 1 => 713
  | 6, 2 => 716
  | 6, 3 => 722
  | 6, 4 => 726
  | 6, 5 => 729
  | 6, 6 => 733
  | 6, 7 => 735
  | 6, 8 => 741
  | 6, 9 => 743
  | 6, 10 => 746
  | 6, 11 => 756
  | 6, 12 => 765
  | 6, 13 => 769
  | 6, 14 => 771
  | 6, 15 => 774
  | 6, 16 => 779
  | 6, 17 => 782
  | 6, 18 => 785
  | 6, 19 => 788
  | 7, 0 => 747
  | 7, 1 => 750
  | 7, 2 => 751
  | 7, 3 => 753
  | 7, 4 => 757
  | 7, 5 => 758
  | 7, 6 => 762
  | 7, 7 => 763
  | 7, 8 => 765
  | 7, 9 => 768
  | 7, 10 => 770
  | 7, 11 => 773
  | 7, 12 => 776
  | 7, 13 => 778
  | 7, 14 => 780
  | 7, 15 => 782
  | 7, 16 => 784
  | 7, 17 => 786
  | 7, 18 => 788
  | 7, 19 => 789
  | _, _ => 0

def values6_add_values8_mem_range_values15_index (i : Fin 8) (j : Fin 20) : Fin 791 :=
  Fin.ofNat 791 (values6_add_values8_mem_range_values15_indexNat i.1 j.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem values6_add_values8_mem_range_values15_index_spec (i : Fin 8) (j : Fin 20) :
    values15 (values6_add_values8_mem_range_values15_index i j) = values6 i + values8 j := by
  fin_cases i <;> fin_cases j
  next =>
    change Real.sqrt (values14 (430 : Fin 455)) = values6 (0 : Fin 8) + values8 (0 : Fin 20)
    rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (12 : Fin 264) = values6 (0 : Fin 8) + values8 (1 : Fin 20)
    rw [show values13 (12 : Fin 264) = Real.sqrt (values12 (12 : Fin 154)) by rfl]
    rw [show values12 (12 : Fin 154) = Real.sqrt (values11 (12 : Fin 91)) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (19 : Fin 264) = values6 (0 : Fin 8) + values8 (2 : Fin 20)
    rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
    rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (31 : Fin 264) = values6 (0 : Fin 8) + values8 (3 : Fin 20)
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (46 : Fin 264) = values6 (0 : Fin 8) + values8 (4 : Fin 20)
    rw [show values13 (46 : Fin 264) = Real.sqrt (values12 (46 : Fin 154)) by rfl]
    rw [show values12 (46 : Fin 154) = Real.sqrt (values11 (46 : Fin 91)) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values6 (0 : Fin 8) + values8 (5 : Fin 20)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (66 : Fin 264) = values6 (0 : Fin 8) + values8 (6 : Fin 20)
    rw [show values13 (66 : Fin 264) = Real.sqrt (values12 (66 : Fin 154)) by rfl]
    rw [show values12 (66 : Fin 154) = Real.sqrt (values11 (66 : Fin 91)) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (76 : Fin 264) = values6 (0 : Fin 8) + values8 (7 : Fin 20)
    rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
    rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values6 (0 : Fin 8) + values8 (8 : Fin 20)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (100 : Fin 264) = values6 (0 : Fin 8) + values8 (9 : Fin 20)
    rw [show values13 (100 : Fin 264) = Real.sqrt (values12 (100 : Fin 154)) by rfl]
    rw [show values12 (100 : Fin 154) = 1 + values10 (12 : Fin 54) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (110 : Fin 264) = values6 (0 : Fin 8) + values8 (10 : Fin 20)
    rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
    rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (130 : Fin 264) = values6 (0 : Fin 8) + values8 (11 : Fin 20)
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values6 (0 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values6 (0 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values6 (0 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values6 (0 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values6 (0 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values6 (0 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values6 (0 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values6 (0 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (31 : Fin 264) = values6 (1 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next => rfl
  next =>
    change values5 (1 : Fin 5) + values9 (5 : Fin 33) = values6 (1 : Fin 8) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change Real.sqrt 2 + values10 (8 : Fin 54) = values6 (1 : Fin 8) + values8 (8 : Fin 20)
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next =>
    change 1 + values13 (160 : Fin 264) = values6 (1 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (169 : Fin 264) = values6 (1 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (169 : Fin 264) = values6 (1 : Fin 8) + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (179 : Fin 264) = values6 (1 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values6 (1 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (215 : Fin 264) = values6 (1 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (215 : Fin 264) = values6 (1 : Fin 8) + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values6 (1 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (242 : Fin 264) = values6 (1 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (242 : Fin 264) = 1 + values11 (69 : Fin 91) by rfl]
    rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (251 : Fin 264) = values6 (1 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values6 (2 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (2 : Fin 33) = values6 (2 : Fin 8) + values8 (1 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (3 : Fin 33) = values6 (2 : Fin 8) + values8 (2 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (5 : Fin 33) = values6 (2 : Fin 8) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (7 : Fin 33) = values6 (2 : Fin 8) + values8 (4 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (8 : Fin 33) = values6 (2 : Fin 8) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (10 : Fin 33) = values6 (2 : Fin 8) + values8 (6 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (11 : Fin 33) = values6 (2 : Fin 8) + values8 (7 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values6 (2 : Fin 8) + values8 (8 : Fin 20)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (14 : Fin 33) = values6 (2 : Fin 8) + values8 (9 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (15 : Fin 33) = values6 (2 : Fin 8) + values8 (10 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (17 : Fin 33) = values6 (2 : Fin 8) + values8 (11 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values6 (2 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (179 : Fin 264) = values6 (2 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (186 : Fin 264) = values6 (2 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values6 (2 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (219 : Fin 264) = values6 (2 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values6 (2 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values6 (2 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values6 (2 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values6 (3 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (3 : Fin 54) = values6 (3 : Fin 8) + values8 (1 : Fin 20)
    rw [show values10 (3 : Fin 54) = Real.sqrt (values9 (3 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (5 : Fin 54) = values6 (3 : Fin 8) + values8 (2 : Fin 20)
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (8 : Fin 54) = values6 (3 : Fin 8) + values8 (3 : Fin 20)
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (11 : Fin 54) = values6 (3 : Fin 8) + values8 (4 : Fin 20)
    rw [show values10 (11 : Fin 54) = Real.sqrt (values9 (11 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values6 (3 : Fin 8) + values8 (5 : Fin 20)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (15 : Fin 54) = values6 (3 : Fin 8) + values8 (6 : Fin 20)
    rw [show values10 (15 : Fin 54) = Real.sqrt (values9 (15 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (17 : Fin 54) = values6 (3 : Fin 8) + values8 (7 : Fin 20)
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (19 : Fin 54) = values6 (3 : Fin 8) + values8 (8 : Fin 20)
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (22 : Fin 54) = values6 (3 : Fin 8) + values8 (9 : Fin 20)
    rw [show values10 (22 : Fin 54) = Real.sqrt (values9 (22 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (24 : Fin 54) = values6 (3 : Fin 8) + values8 (10 : Fin 20)
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (28 : Fin 54) = values6 (3 : Fin 8) + values8 (11 : Fin 20)
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values6 (3 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values6 (3 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values6 (3 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values6 (3 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values6 (3 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values6 (3 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (247 : Fin 264) = values6 (3 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
    rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values6 (3 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (130 : Fin 264) = values6 (4 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change values6 (1 : Fin 8) + values8 (11 : Fin 20) = values6 (4 : Fin 8) + values8 (3 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values5 (1 : Fin 5) + values9 (17 : Fin 33) = values6 (4 : Fin 8) + values8 (5 : Fin 20)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next =>
    change Real.sqrt 2 + values10 (28 : Fin 54) = values6 (4 : Fin 8) + values8 (8 : Fin 20)
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next => rfl
  next => rfl
  next =>
    change 1 + values13 (211 : Fin 264) = values6 (4 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (215 : Fin 264) = values6 (4 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (215 : Fin 264) = values6 (1 : Fin 8) + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (219 : Fin 264) = values6 (4 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values6 (4 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (240 : Fin 264) = values6 (4 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (240 : Fin 264) = values6 (4 : Fin 8) + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values6 (4 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (252 : Fin 264) = values6 (4 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (257 : Fin 264) = values6 (4 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values6 (5 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (151 : Fin 264) = values6 (5 : Fin 8) + values8 (1 : Fin 20)
    rw [show values13 (151 : Fin 264) = 1 + values11 (5 : Fin 91) by rfl]
    rw [show values11 (5 : Fin 91) = Real.sqrt (values10 (5 : Fin 54)) by rfl]
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (155 : Fin 264) = values6 (5 : Fin 8) + values8 (2 : Fin 20)
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values6 (5 : Fin 8) + values8 (3 : Fin 20)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (166 : Fin 264) = values6 (5 : Fin 8) + values8 (4 : Fin 20)
    rw [show values13 (166 : Fin 264) = 1 + values11 (17 : Fin 91) by rfl]
    rw [show values11 (17 : Fin 91) = Real.sqrt (values10 (17 : Fin 54)) by rfl]
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values6 (5 : Fin 8) + values8 (5 : Fin 20)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (177 : Fin 264) = values6 (5 : Fin 8) + values8 (6 : Fin 20)
    rw [show values13 (177 : Fin 264) = 1 + values11 (24 : Fin 91) by rfl]
    rw [show values11 (24 : Fin 91) = Real.sqrt (values10 (24 : Fin 54)) by rfl]
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (182 : Fin 264) = values6 (5 : Fin 8) + values8 (7 : Fin 20)
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values6 (5 : Fin 8) + values8 (8 : Fin 20)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (195 : Fin 264) = values6 (5 : Fin 8) + values8 (9 : Fin 20)
    rw [show values13 (195 : Fin 264) = 1 + values11 (36 : Fin 91) by rfl]
    rw [show values11 (36 : Fin 91) = Real.sqrt (values10 (36 : Fin 54)) by rfl]
    rw [show values10 (36 : Fin 54) = 1 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (201 : Fin 264) = values6 (5 : Fin 8) + values8 (10 : Fin 20)
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values6 (5 : Fin 8) + values8 (11 : Fin 20)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values6 (5 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values6 (5 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values6 (5 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values6 (5 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values6 (5 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values6 (5 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values6 (5 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values6 (5 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values6 (6 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (190 : Fin 264) = values6 (6 : Fin 8) + values8 (1 : Fin 20)
    rw [show values13 (190 : Fin 264) = Real.sqrt 2 + values8 (1 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (193 : Fin 264) = values6 (6 : Fin 8) + values8 (2 : Fin 20)
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values6 (6 : Fin 8) + values8 (3 : Fin 20)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (202 : Fin 264) = values6 (6 : Fin 8) + values8 (4 : Fin 20)
    rw [show values13 (202 : Fin 264) = Real.sqrt 2 + values8 (4 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values6 (6 : Fin 8) + values8 (5 : Fin 20)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (208 : Fin 264) = values6 (6 : Fin 8) + values8 (6 : Fin 20)
    rw [show values13 (208 : Fin 264) = Real.sqrt 2 + values8 (6 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (210 : Fin 264) = values6 (6 : Fin 8) + values8 (7 : Fin 20)
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values6 (6 : Fin 8) + values8 (8 : Fin 20)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (218 : Fin 264) = values6 (6 : Fin 8) + values8 (9 : Fin 20)
    rw [show values13 (218 : Fin 264) = Real.sqrt 2 + values8 (9 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (221 : Fin 264) = values6 (6 : Fin 8) + values8 (10 : Fin 20)
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values6 (6 : Fin 8) + values8 (11 : Fin 20)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values6 (6 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (242 : Fin 264) = values6 (6 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (242 : Fin 264) = 1 + values11 (69 : Fin 91) by rfl]
    rw [show values11 (69 : Fin 91) = Real.sqrt 2 + values6 (1 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values6 (6 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (247 : Fin 264) = values6 (6 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
    rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (252 : Fin 264) = values6 (6 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (252 : Fin 264) = 1 + values11 (79 : Fin 91) by rfl]
    rw [show values11 (79 : Fin 91) = Real.sqrt 2 + values6 (4 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values6 (6 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (258 : Fin 264) = values6 (6 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (258 : Fin 264) = 1 + values11 (85 : Fin 91) by rfl]
    rw [show values11 (85 : Fin 91) = 1 + values9 (27 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values6 (6 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values6 (7 : Fin 8) + values8 (0 : Fin 20)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (224 : Fin 264) = values6 (7 : Fin 8) + values8 (1 : Fin 20)
    rw [show values13 (224 : Fin 264) = 1 + values11 (53 : Fin 91) by rfl]
    rw [show values11 (53 : Fin 91) = 1 + values9 (2 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (225 : Fin 264) = values6 (7 : Fin 8) + values8 (2 : Fin 20)
    rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values6 (7 : Fin 8) + values8 (3 : Fin 20)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (231 : Fin 264) = values6 (7 : Fin 8) + values8 (4 : Fin 20)
    rw [show values13 (231 : Fin 264) = 1 + values11 (59 : Fin 91) by rfl]
    rw [show values11 (59 : Fin 91) = 1 + values9 (7 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values6 (7 : Fin 8) + values8 (5 : Fin 20)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (235 : Fin 264) = values6 (7 : Fin 8) + values8 (6 : Fin 20)
    rw [show values13 (235 : Fin 264) = 1 + values11 (63 : Fin 91) by rfl]
    rw [show values11 (63 : Fin 91) = 1 + values9 (10 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (236 : Fin 264) = values6 (7 : Fin 8) + values8 (7 : Fin 20)
    rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values6 (7 : Fin 8) + values8 (8 : Fin 20)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (241 : Fin 264) = values6 (7 : Fin 8) + values8 (9 : Fin 20)
    rw [show values13 (241 : Fin 264) = 1 + values11 (68 : Fin 91) by rfl]
    rw [show values11 (68 : Fin 91) = 1 + values9 (14 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (243 : Fin 264) = values6 (7 : Fin 8) + values8 (10 : Fin 20)
    rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values6 (7 : Fin 8) + values8 (11 : Fin 20)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values6 (7 : Fin 8) + values8 (12 : Fin 20)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (251 : Fin 264) = values6 (7 : Fin 8) + values8 (13 : Fin 20)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values6 (7 : Fin 8) + values8 (14 : Fin 20)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values6 (7 : Fin 8) + values8 (15 : Fin 20)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (257 : Fin 264) = values6 (7 : Fin 8) + values8 (16 : Fin 20)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values6 (7 : Fin 8) + values8 (17 : Fin 20)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values6 (7 : Fin 8) + values8 (18 : Fin 20)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (262 : Fin 264) = values6 (7 : Fin 8) + values8 (19 : Fin 20)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem values6_add_values8_mem_range_values15 (i : Fin 8) (j : Fin 20) :
    (Set.range values15) (values6 i + values8 j) := by
  exact ⟨values6_add_values8_mem_range_values15_index i j, values6_add_values8_mem_range_values15_index_spec i j⟩

def values7_add_values7_mem_range_values15_indexNat : Nat -> Nat -> Nat
  | 0, 0 => 430
  | 0, 1 => 454
  | 0, 2 => 472
  | 0, 3 => 500
  | 0, 4 => 536
  | 0, 5 => 554
  | 0, 6 => 592
  | 0, 7 => 626
  | 0, 8 => 658
  | 0, 9 => 689
  | 0, 10 => 710
  | 0, 11 => 747
  | 0, 12 => 776
  | 1, 0 => 454
  | 1, 1 => 471
  | 1, 2 => 490
  | 1, 3 => 516
  | 1, 4 => 546
  | 1, 5 => 573
  | 1, 6 => 602
  | 1, 7 => 635
  | 1, 8 => 669
  | 1, 9 => 695
  | 1, 10 => 716
  | 1, 11 => 751
  | 1, 12 => 777
  | 2, 0 => 472
  | 2, 1 => 490
  | 2, 2 => 499
  | 2, 3 => 531
  | 2, 4 => 553
  | 2, 5 => 582
  | 2, 6 => 613
  | 2, 7 => 640
  | 2, 8 => 676
  | 2, 9 => 701
  | 2, 10 => 722
  | 2, 11 => 753
  | 2, 12 => 778
  | 3, 0 => 500
  | 3, 1 => 516
  | 3, 2 => 531
  | 3, 3 => 548
  | 3, 4 => 583
  | 3, 5 => 604
  | 3, 6 => 628
  | 3, 7 => 652
  | 3, 8 => 689
  | 3, 9 => 709
  | 3, 10 => 729
  | 3, 11 => 758
  | 3, 12 => 780
  | 4, 0 => 536
  | 4, 1 => 546
  | 4, 2 => 553
  | 4, 3 => 583
  | 4, 4 => 610
  | 4, 5 => 625
  | 4, 6 => 647
  | 4, 7 => 671
  | 4, 8 => 705
  | 4, 9 => 723
  | 4, 10 => 735
  | 4, 11 => 763
  | 4, 12 => 781
  | 5, 0 => 554
  | 5, 1 => 573
  | 5, 2 => 582
  | 5, 3 => 604
  | 5, 4 => 625
  | 5, 5 => 641
  | 5, 6 => 656
  | 5, 7 => 684
  | 5, 8 => 710
  | 5, 9 => 729
  | 5, 10 => 741
  | 5, 11 => 765
  | 5, 12 => 782
  | 6, 0 => 592
  | 6, 1 => 602
  | 6, 2 => 613
  | 6, 3 => 628
  | 6, 4 => 647
  | 6, 5 => 656
  | 6, 6 => 681
  | 6, 7 => 703
  | 6, 8 => 725
  | 6, 9 => 737
  | 6, 10 => 746
  | 6, 11 => 770
  | 6, 12 => 783
  | 7, 0 => 626
  | 7, 1 => 635
  | 7, 2 => 640
  | 7, 3 => 652
  | 7, 4 => 671
  | 7, 5 => 684
  | 7, 6 => 703
  | 7, 7 => 717
  | 7, 8 => 736
  | 7, 9 => 744
  | 7, 10 => 756
  | 7, 11 => 773
  | 7, 12 => 784
  | 8, 0 => 658
  | 8, 1 => 669
  | 8, 2 => 676
  | 8, 3 => 689
  | 8, 4 => 705
  | 8, 5 => 710
  | 8, 6 => 725
  | 8, 7 => 736
  | 8, 8 => 747
  | 8, 9 => 758
  | 8, 10 => 765
  | 8, 11 => 776
  | 8, 12 => 786
  | 9, 0 => 689
  | 9, 1 => 695
  | 9, 2 => 701
  | 9, 3 => 709
  | 9, 4 => 723
  | 9, 5 => 729
  | 9, 6 => 737
  | 9, 7 => 744
  | 9, 8 => 758
  | 9, 9 => 764
  | 9, 10 => 771
  | 9, 11 => 780
  | 9, 12 => 787
  | 10, 0 => 710
  | 10, 1 => 716
  | 10, 2 => 722
  | 10, 3 => 729
  | 10, 4 => 735
  | 10, 5 => 741
  | 10, 6 => 746
  | 10, 7 => 756
  | 10, 8 => 765
  | 10, 9 => 771
  | 10, 10 => 774
  | 10, 11 => 782
  | 10, 12 => 788
  | 11, 0 => 747
  | 11, 1 => 751
  | 11, 2 => 753
  | 11, 3 => 758
  | 11, 4 => 763
  | 11, 5 => 765
  | 11, 6 => 770
  | 11, 7 => 773
  | 11, 8 => 776
  | 11, 9 => 780
  | 11, 10 => 782
  | 11, 11 => 786
  | 11, 12 => 789
  | 12, 0 => 776
  | 12, 1 => 777
  | 12, 2 => 778
  | 12, 3 => 780
  | 12, 4 => 781
  | 12, 5 => 782
  | 12, 6 => 783
  | 12, 7 => 784
  | 12, 8 => 786
  | 12, 9 => 787
  | 12, 10 => 788
  | 12, 11 => 789
  | 12, 12 => 790
  | _, _ => 0

def values7_add_values7_mem_range_values15_index (i : Fin 13) (j : Fin 13) : Fin 791 :=
  Fin.ofNat 791 (values7_add_values7_mem_range_values15_indexNat i.1 j.1)

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
set_option maxHeartbeats 20000000 in
theorem values7_add_values7_mem_range_values15_index_spec (i : Fin 13) (j : Fin 13) :
    values15 (values7_add_values7_mem_range_values15_index i j) = values7 i + values7 j := by
  fin_cases i <;> fin_cases j
  next =>
    change Real.sqrt (values14 (430 : Fin 455)) = values7 (0 : Fin 13) + values7 (0 : Fin 13)
    rw [show values14 (430 : Fin 455) = 1 + values12 (130 : Fin 154) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (19 : Fin 264) = values7 (0 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
    rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (31 : Fin 264) = values7 (0 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values7 (0 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (76 : Fin 264) = values7 (0 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
    rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values7 (0 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (110 : Fin 264) = values7 (0 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
    rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (130 : Fin 264) = values7 (0 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values7 (0 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values7 (0 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values7 (0 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values7 (0 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values7 (0 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (19 : Fin 264) = values7 (1 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (19 : Fin 264) = Real.sqrt (values12 (19 : Fin 154)) by rfl]
    rw [show values12 (19 : Fin 154) = Real.sqrt (values11 (19 : Fin 91)) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values6 (1 : Fin 8) + values8 (2 : Fin 20) = values7 (1 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (3 : Fin 33) = values7 (1 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change Real.sqrt 2 + values10 (5 : Fin 54) = values7 (1 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values6 (4 : Fin 8) + values8 (2 : Fin 20) = values7 (1 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (155 : Fin 264) = values7 (1 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (174 : Fin 264) = values7 (1 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (174 : Fin 264) = values5 (1 : Fin 5) + values7 (1 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (193 : Fin 264) = values7 (1 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (225 : Fin 264) = values7 (1 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (250 : Fin 264) = values7 (1 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (31 : Fin 264) = values7 (2 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (31 : Fin 264) = Real.sqrt (values12 (31 : Fin 154)) by rfl]
    rw [show values12 (31 : Fin 154) = Real.sqrt (values11 (31 : Fin 91)) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (2 : Fin 20) = values7 (2 : Fin 13) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (3 : Fin 20) = values7 (2 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (5 : Fin 33) = values7 (2 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (7 : Fin 20) = values7 (2 : Fin 13) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (8 : Fin 54) = values7 (2 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (10 : Fin 20) = values7 (2 : Fin 13) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (11 : Fin 20) = values7 (2 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values7 (2 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (179 : Fin 264) = values7 (2 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values7 (2 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values7 (2 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (251 : Fin 264) = values7 (2 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (51 : Fin 264) = values7 (3 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (51 : Fin 264) = Real.sqrt (values12 (51 : Fin 154)) by rfl]
    rw [show values12 (51 : Fin 154) = Real.sqrt (values11 (51 : Fin 91)) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (3 : Fin 33) = values7 (3 : Fin 13) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (5 : Fin 33) = values7 (3 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (8 : Fin 33) = values7 (3 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (11 : Fin 33) = values7 (3 : Fin 13) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values7 (3 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (15 : Fin 33) = values7 (3 : Fin 13) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (17 : Fin 33) = values7 (3 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values7 (3 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (186 : Fin 264) = values7 (3 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values7 (3 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values7 (3 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values7 (3 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (76 : Fin 264) = values7 (4 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (76 : Fin 264) = Real.sqrt (values12 (76 : Fin 154)) by rfl]
    rw [show values12 (76 : Fin 154) = Real.sqrt (values11 (76 : Fin 91)) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values7 (1 : Fin 13) + values7 (4 : Fin 13) = values7 (4 : Fin 13) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (7 : Fin 20) = values7 (4 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (11 : Fin 33) = values7 (4 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change Real.sqrt 2 + values10 (17 : Fin 54) = values7 (4 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values6 (4 : Fin 8) + values8 (7 : Fin 20) = values7 (4 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (182 : Fin 264) = values7 (4 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (199 : Fin 264) = values7 (4 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (199 : Fin 264) = values5 (1 : Fin 5) + values7 (4 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (210 : Fin 264) = values7 (4 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (236 : Fin 264) = values7 (4 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (254 : Fin 264) = values7 (4 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (86 : Fin 264) = values7 (5 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (86 : Fin 264) = Real.sqrt (values12 (86 : Fin 154)) by rfl]
    rw [show values12 (86 : Fin 154) = Real.sqrt (values11 (86 : Fin 91)) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (5 : Fin 54) = values7 (5 : Fin 13) + values7 (1 : Fin 13)
    rw [show values10 (5 : Fin 54) = Real.sqrt (values9 (5 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (8 : Fin 54) = values7 (5 : Fin 13) + values7 (2 : Fin 13)
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (12 : Fin 54) = values7 (5 : Fin 13) + values7 (3 : Fin 13)
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (17 : Fin 54) = values7 (5 : Fin 13) + values7 (4 : Fin 13)
    rw [show values10 (17 : Fin 54) = Real.sqrt (values9 (17 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (19 : Fin 54) = values7 (5 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (24 : Fin 54) = values7 (5 : Fin 13) + values7 (6 : Fin 13)
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (28 : Fin 54) = values7 (5 : Fin 13) + values7 (7 : Fin 13)
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values7 (5 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values7 (5 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values7 (5 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values7 (5 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values7 (5 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (110 : Fin 264) = values7 (6 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (110 : Fin 264) = Real.sqrt (values12 (110 : Fin 154)) by rfl]
    rw [show values12 (110 : Fin 154) = 1 + values10 (19 : Fin 54) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values7 (1 : Fin 13) + values7 (6 : Fin 13) = values7 (6 : Fin 13) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (10 : Fin 20) = values7 (6 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (15 : Fin 33) = values7 (6 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values7 (4 : Fin 13) + values7 (6 : Fin 13) = values7 (6 : Fin 13) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (24 : Fin 54) = values7 (6 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (24 : Fin 54) = Real.sqrt (values9 (24 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next => rfl
  next =>
    change values6 (4 : Fin 8) + values8 (10 : Fin 20) = values7 (6 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (201 : Fin 264) = values7 (6 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (212 : Fin 264) = values7 (6 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (212 : Fin 264) = values5 (1 : Fin 5) + values7 (6 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (221 : Fin 264) = values7 (6 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (243 : Fin 264) = values7 (6 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (256 : Fin 264) = values7 (6 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (130 : Fin 264) = values7 (7 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (130 : Fin 264) = Real.sqrt (values12 (130 : Fin 154)) by rfl]
    rw [show values12 (130 : Fin 154) = 1 + values10 (31 : Fin 54) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (4 : Fin 8) + values8 (2 : Fin 20) = values7 (7 : Fin 13) + values7 (1 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (1 : Fin 8) + values8 (11 : Fin 20) = values7 (7 : Fin 13) + values7 (2 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values5 (1 : Fin 5) + values9 (17 : Fin 33) = values7 (7 : Fin 13) + values7 (3 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (4 : Fin 8) + values8 (7 : Fin 20) = values7 (7 : Fin 13) + values7 (4 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change Real.sqrt 2 + values10 (28 : Fin 54) = values7 (7 : Fin 13) + values7 (5 : Fin 13)
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (4 : Fin 8) + values8 (10 : Fin 20) = values7 (7 : Fin 13) + values7 (6 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change values6 (4 : Fin 8) + values8 (11 : Fin 20) = values7 (7 : Fin 13) + values7 (7 : Fin 13)
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values7 (7 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (219 : Fin 264) = values7 (7 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values7 (7 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values7 (7 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (257 : Fin 264) = values7 (7 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (146 : Fin 264) = values7 (8 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (146 : Fin 264) = Real.sqrt (values12 (146 : Fin 154)) by rfl]
    rw [show values12 (146 : Fin 154) = 1 + values10 (46 : Fin 54) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (155 : Fin 264) = values7 (8 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (155 : Fin 264) = 1 + values11 (8 : Fin 91) by rfl]
    rw [show values11 (8 : Fin 91) = Real.sqrt (values10 (8 : Fin 54)) by rfl]
    rw [show values10 (8 : Fin 54) = Real.sqrt (values9 (8 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (160 : Fin 264) = values7 (8 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (160 : Fin 264) = 1 + values11 (12 : Fin 91) by rfl]
    rw [show values11 (12 : Fin 91) = Real.sqrt (values10 (12 : Fin 54)) by rfl]
    rw [show values10 (12 : Fin 54) = Real.sqrt (values9 (12 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values7 (8 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (182 : Fin 264) = values7 (8 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (182 : Fin 264) = 1 + values11 (28 : Fin 91) by rfl]
    rw [show values11 (28 : Fin 91) = Real.sqrt (values10 (28 : Fin 54)) by rfl]
    rw [show values10 (28 : Fin 54) = Real.sqrt (values9 (28 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values7 (8 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (201 : Fin 264) = values7 (8 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (201 : Fin 264) = 1 + values11 (40 : Fin 91) by rfl]
    rw [show values11 (40 : Fin 91) = Real.sqrt (values10 (40 : Fin 54)) by rfl]
    rw [show values10 (40 : Fin 54) = 1 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (211 : Fin 264) = values7 (8 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (211 : Fin 264) = 1 + values11 (46 : Fin 91) by rfl]
    rw [show values11 (46 : Fin 91) = Real.sqrt (values10 (46 : Fin 54)) by rfl]
    rw [show values10 (46 : Fin 54) = 1 + values8 (12 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values7 (8 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values7 (8 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values7 (8 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values7 (8 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values7 (8 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (170 : Fin 264) = values7 (9 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (170 : Fin 264) = 1 + values11 (19 : Fin 91) by rfl]
    rw [show values11 (19 : Fin 91) = Real.sqrt (values10 (19 : Fin 54)) by rfl]
    rw [show values10 (19 : Fin 54) = Real.sqrt (values9 (19 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (174 : Fin 264) = values7 (9 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (174 : Fin 264) = values5 (1 : Fin 5) + values7 (1 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (179 : Fin 264) = values7 (9 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (179 : Fin 264) = values5 (1 : Fin 5) + values7 (2 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (186 : Fin 264) = values7 (9 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (186 : Fin 264) = values5 (1 : Fin 5) + values7 (3 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (199 : Fin 264) = values7 (9 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (199 : Fin 264) = values5 (1 : Fin 5) + values7 (4 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values7 (9 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (212 : Fin 264) = values7 (9 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (212 : Fin 264) = values5 (1 : Fin 5) + values7 (6 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (219 : Fin 264) = values7 (9 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (219 : Fin 264) = values5 (1 : Fin 5) + values7 (7 : Fin 13) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values7 (9 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (237 : Fin 264) = values7 (9 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (237 : Fin 264) = 1 + values11 (65 : Fin 91) by rfl]
    rw [show values11 (65 : Fin 91) = values5 (1 : Fin 5) + values5 (1 : Fin 5) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values7 (9 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values7 (9 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (260 : Fin 264) = values7 (9 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (187 : Fin 264) = values7 (10 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (187 : Fin 264) = 1 + values11 (31 : Fin 91) by rfl]
    rw [show values11 (31 : Fin 91) = Real.sqrt (values10 (31 : Fin 54)) by rfl]
    rw [show values10 (31 : Fin 54) = Real.sqrt (values9 (31 : Fin 33)) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (193 : Fin 264) = values7 (10 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (193 : Fin 264) = Real.sqrt 2 + values8 (2 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (198 : Fin 264) = values7 (10 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (198 : Fin 264) = Real.sqrt 2 + values8 (3 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (205 : Fin 264) = values7 (10 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (205 : Fin 264) = Real.sqrt 2 + values8 (5 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (210 : Fin 264) = values7 (10 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (210 : Fin 264) = Real.sqrt 2 + values8 (7 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (216 : Fin 264) = values7 (10 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (216 : Fin 264) = Real.sqrt 2 + values8 (8 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (221 : Fin 264) = values7 (10 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (221 : Fin 264) = Real.sqrt 2 + values8 (10 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (230 : Fin 264) = values7 (10 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (230 : Fin 264) = Real.sqrt 2 + values8 (11 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values7 (10 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (244 : Fin 264) = values7 (10 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (244 : Fin 264) = 1 + values11 (71 : Fin 91) by rfl]
    rw [show values11 (71 : Fin 91) = Real.sqrt 2 + values6 (2 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (247 : Fin 264) = values7 (10 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (247 : Fin 264) = 1 + values11 (74 : Fin 91) by rfl]
    rw [show values11 (74 : Fin 91) = Real.sqrt 2 + values6 (3 : Fin 8) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values7 (10 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values7 (10 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (222 : Fin 264) = values7 (11 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (222 : Fin 264) = 1 + values11 (51 : Fin 91) by rfl]
    rw [show values11 (51 : Fin 91) = Real.sqrt (values10 (51 : Fin 54)) by rfl]
    rw [show values10 (51 : Fin 54) = 1 + values8 (17 : Fin 20) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (225 : Fin 264) = values7 (11 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (225 : Fin 264) = 1 + values11 (54 : Fin 91) by rfl]
    rw [show values11 (54 : Fin 91) = 1 + values9 (3 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (227 : Fin 264) = values7 (11 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (227 : Fin 264) = 1 + values11 (56 : Fin 91) by rfl]
    rw [show values11 (56 : Fin 91) = 1 + values9 (5 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (232 : Fin 264) = values7 (11 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (232 : Fin 264) = 1 + values11 (60 : Fin 91) by rfl]
    rw [show values11 (60 : Fin 91) = 1 + values9 (8 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (236 : Fin 264) = values7 (11 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (236 : Fin 264) = 1 + values11 (64 : Fin 91) by rfl]
    rw [show values11 (64 : Fin 91) = 1 + values9 (11 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (238 : Fin 264) = values7 (11 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (238 : Fin 264) = 1 + values11 (66 : Fin 91) by rfl]
    rw [show values11 (66 : Fin 91) = 1 + values9 (12 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (243 : Fin 264) = values7 (11 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (243 : Fin 264) = 1 + values11 (70 : Fin 91) by rfl]
    rw [show values11 (70 : Fin 91) = 1 + values9 (15 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (246 : Fin 264) = values7 (11 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (246 : Fin 264) = 1 + values11 (73 : Fin 91) by rfl]
    rw [show values11 (73 : Fin 91) = 1 + values9 (17 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values7 (11 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values7 (11 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values7 (11 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values7 (11 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (262 : Fin 264) = values7 (11 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (249 : Fin 264) = values7 (12 : Fin 13) + values7 (0 : Fin 13)
    rw [show values13 (249 : Fin 264) = 1 + values11 (76 : Fin 91) by rfl]
    rw [show values11 (76 : Fin 91) = 1 + values9 (19 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (250 : Fin 264) = values7 (12 : Fin 13) + values7 (1 : Fin 13)
    rw [show values13 (250 : Fin 264) = 1 + values11 (77 : Fin 91) by rfl]
    rw [show values11 (77 : Fin 91) = 1 + values9 (20 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (251 : Fin 264) = values7 (12 : Fin 13) + values7 (2 : Fin 13)
    rw [show values13 (251 : Fin 264) = 1 + values11 (78 : Fin 91) by rfl]
    rw [show values11 (78 : Fin 91) = 1 + values9 (21 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (253 : Fin 264) = values7 (12 : Fin 13) + values7 (3 : Fin 13)
    rw [show values13 (253 : Fin 264) = 1 + values11 (80 : Fin 91) by rfl]
    rw [show values11 (80 : Fin 91) = 1 + values9 (22 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (254 : Fin 264) = values7 (12 : Fin 13) + values7 (4 : Fin 13)
    rw [show values13 (254 : Fin 264) = 1 + values11 (81 : Fin 91) by rfl]
    rw [show values11 (81 : Fin 91) = 1 + values9 (23 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (255 : Fin 264) = values7 (12 : Fin 13) + values7 (5 : Fin 13)
    rw [show values13 (255 : Fin 264) = 1 + values11 (82 : Fin 91) by rfl]
    rw [show values11 (82 : Fin 91) = 1 + values9 (24 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (256 : Fin 264) = values7 (12 : Fin 13) + values7 (6 : Fin 13)
    rw [show values13 (256 : Fin 264) = 1 + values11 (83 : Fin 91) by rfl]
    rw [show values11 (83 : Fin 91) = 1 + values9 (25 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (257 : Fin 264) = values7 (12 : Fin 13) + values7 (7 : Fin 13)
    rw [show values13 (257 : Fin 264) = 1 + values11 (84 : Fin 91) by rfl]
    rw [show values11 (84 : Fin 91) = 1 + values9 (26 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (259 : Fin 264) = values7 (12 : Fin 13) + values7 (8 : Fin 13)
    rw [show values13 (259 : Fin 264) = 1 + values11 (86 : Fin 91) by rfl]
    rw [show values11 (86 : Fin 91) = 1 + values9 (28 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (260 : Fin 264) = values7 (12 : Fin 13) + values7 (9 : Fin 13)
    rw [show values13 (260 : Fin 264) = 1 + values11 (87 : Fin 91) by rfl]
    rw [show values11 (87 : Fin 91) = 1 + values9 (29 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (261 : Fin 264) = values7 (12 : Fin 13) + values7 (10 : Fin 13)
    rw [show values13 (261 : Fin 264) = 1 + values11 (88 : Fin 91) by rfl]
    rw [show values11 (88 : Fin 91) = 1 + values9 (30 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (262 : Fin 264) = values7 (12 : Fin 13) + values7 (11 : Fin 13)
    rw [show values13 (262 : Fin 264) = 1 + values11 (89 : Fin 91) by rfl]
    rw [show values11 (89 : Fin 91) = 1 + values9 (31 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num
  next =>
    change 1 + values13 (263 : Fin 264) = values7 (12 : Fin 13) + values7 (12 : Fin 13)
    rw [show values13 (263 : Fin 264) = 1 + values11 (90 : Fin 91) by rfl]
    rw [show values11 (90 : Fin 91) = 1 + values9 (32 : Fin 33) by rfl]
    a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num

theorem values7_add_values7_mem_range_values15 (i : Fin 13) (j : Fin 13) :
    (Set.range values15) (values7 i + values7 j) := by
  exact ⟨values7_add_values7_mem_range_values15_index i j, values7_add_values7_mem_range_values15_index_spec i j⟩

end Expr
end A158415
end LeanProofs
