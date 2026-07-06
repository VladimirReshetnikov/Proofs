import LeanProofs.A198683Schoenfield

/-!
# Row-level Schoenfield certificates for OEIS A198683

`LeanProofs.A198683Schoenfield` checks normalized class-label lists. This
module keeps one more layer of the source table: each row is either a new
class (`none`, corresponding to an entry in the Count column) or a match to an
earlier 1-based row index (`some j`, corresponding to the Match column). The
checker reconstructs the normalized labels from that row data and then reuses
the existing finite certificate predicate.

This is still a finite Schoenfield-table certificate, not a semantic proof over
`LeanProofs.A198683.a198683ValueSet`.
-/

namespace LeanProofs

namespace A198683SchoenfieldRows

/-- Reconstruct normalized labels from Count/Match-style rows. -/
def labelsFromRowsFrom : Nat -> List Nat -> List (Option Nat) -> Option (List Nat)
  | _, acc, [] => some acc
  | next, acc, none :: rest =>
      labelsFromRowsFrom (next + 1) (acc ++ [next]) rest
  | next, acc, some matchIndex :: rest =>
      match matchIndex with
      | 0 => none
      | j + 1 =>
          match acc[j]? with
          | some label => labelsFromRowsFrom next (acc ++ [label]) rest
          | none => none

/-- Reconstruct normalized labels, starting class labels at 1. -/
def labelsFromRows (rows : List (Option Nat)) : Option (List Nat) :=
  labelsFromRowsFrom 1 [] rows

/-- A Count/Match row certificate: reconstruct labels and check their count. -/
def rowCertificateOk (rows : List (Option Nat)) (rowCount classes : Nat) : Bool :=
  match labelsFromRows rows with
  | some labels => A198683Schoenfield.certificateOk labels rowCount classes
  | none => false

/-- Count/Match rows from the n = 7 Schoenfield table. -/
def rowsSeven : List (Option Nat) :=
  List.flatten
    [
      [none, none, none, some 3, some 2, none, none, none, none, some 6, some 7, some 9, some 9, some 7, none, none],
      [none, some 17, some 16, none, none, none, some 7, some 20, some 21, none, some 26, some 21, some 15, none, some 17, some 17],
      [some 30, some 22, some 7, some 26, some 21, some 22, some 7, some 21, some 21, some 7, none, none, none, some 45, some 44, none],
      [none, none, none, some 48, some 49, some 51, some 51, some 49, none, none, none, some 59, some 58, none, none, none],
      [some 64, some 63, none, none, some 68, some 49, none, some 7, some 71, some 7, some 68, some 49, some 57, none, some 59, some 59],
      [some 78, some 71, some 7, none, none, some 71, some 7, some 85, some 85, some 7, some 43, some 44, some 45, some 45, some 44, some 48],
      [some 49, some 50, some 51, some 48, some 49, some 51, some 51, some 49, some 62, some 63, some 64, some 64, some 63, some 71, some 7, some 68],
      [some 49, some 71, some 7, some 85, some 85, some 7, some 62, some 63, some 64, some 64, some 63, some 68, some 49, some 85, some 7, some 68],
      [some 49, some 7, some 7, some 49]
    ]

/-- The n = 7 row data reconstruct exactly the normalized label certificate. -/
theorem rows_seven_reconstruct_labels :
    labelsFromRows rowsSeven = some A198683Schoenfield.labelsSeven := by
  native_decide

/-- Row-level Schoenfield table certificate for `A198683(7) = 34`. -/
theorem schoenfield_rows_a198683_seven :
    rowCertificateOk rowsSeven 132 34 = true := by
  native_decide

/-- Count/Match rows from the n = 8 Schoenfield table. -/
def rowsEight : List (Option Nat) :=
  List.flatten
    [
      [none, none, none, some 3, some 2, none, none, none, none, some 6, some 7, some 9, some 9, some 7, none, none],
      [none, some 17, some 16, none, none, none, some 7, some 20, some 21, none, some 26, some 21, some 15, none, some 17, some 17],
      [some 30, some 22, some 7, some 26, some 21, some 22, some 7, some 21, some 21, some 7, none, none, none, some 45, some 44, none],
      [none, none, none, some 48, some 49, some 51, some 51, some 49, none, none, none, some 59, some 58, none, none, none],
      [some 64, some 63, none, none, some 68, some 49, none, some 7, some 71, some 7, some 68, some 49, some 57, none, some 59, some 59],
      [some 78, some 71, some 7, none, none, some 71, some 7, some 85, some 85, some 7, some 43, some 44, some 45, some 45, some 44, some 48],
      [some 49, some 50, some 51, some 48, some 49, some 51, some 51, some 49, some 62, some 63, some 64, some 64, some 63, some 71, some 7, some 68],
      [some 49, some 71, some 7, some 85, some 85, some 7, some 62, some 63, some 64, some 64, some 63, some 68, some 49, some 85, some 7, some 68],
      [some 49, some 7, some 7, some 49, none, none, none, some 135, some 134, none, none, none, none, some 138, some 139, some 141],
      [some 141, some 139, none, none, none, some 149, some 148, none, none, none, some 139, some 152, some 153, none, some 158, some 153],
      [some 147, none, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139, some 153, some 153, some 139, none, none],
      [none, some 177, some 176, none, some 139, none, none, some 180, some 139, some 183, some 183, some 139, none, none, none, some 191],
      [some 190, none, some 49, none, none, some 194, some 49, some 197, some 197, some 49, none, none, none, some 205, some 204, none],
      [none, none, some 210, some 209, none, some 58, none, some 215, some 58, some 213, some 58, some 215, some 215, some 58, some 208, some 209],
      [some 210, some 210, some 209, some 203, some 208, none, none, some 205, some 210, some 205, some 210, some 230, some 231, none, some 7, some 7],
      [some 49, none, none, none, some 139, some 238, some 7, some 7, some 49, some 244, some 139, some 244, some 139, some 7, some 49, some 175],
      [some 176, some 177, some 177, some 176, some 180, some 139, some 182, some 183, some 180, some 139, some 183, some 183, some 139, some 213, some 58, some 215],
      [some 215, some 58, some 242, some 243, some 244, some 139, some 242, some 243, none, some 281, some 243, some 213, none, some 215, some 215, some 285],
      [some 244, some 139, some 281, some 243, some 244, some 139, some 243, some 243, some 139, some 133, some 134, some 135, some 135, some 134, some 138, some 139],
      [some 140, some 141, some 138, some 139, some 141, some 141, some 139, some 147, some 148, some 149, some 149, some 148, some 152, some 153, some 154, some 139],
      [some 152, some 153, some 158, some 158, some 153, some 147, some 162, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139],
      [some 153, some 153, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 213, some 58, some 215, some 215, some 58, some 208, some 231, some 210, some 210, some 231, some 238, some 7, some 7, some 49, some 244],
      [some 139, some 244, some 139, some 7, some 49, some 213, some 285, some 215, some 215, some 285, some 244, some 139, some 281, some 243, some 244, some 139],
      [some 243, some 243, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 208, some 231, some 210, some 210, some 231, some 244, some 139, some 7, some 49, some 244, some 139, some 243, some 243, some 139, some 208],
      [some 231, some 210, some 210, some 231, some 7, some 49, some 243, some 139, some 7, some 49, some 139, some 139, some 49]
    ]

/-- The n = 8 row data reconstruct exactly the normalized label certificate. -/
theorem rows_eight_reconstruct_labels :
    labelsFromRows rowsEight = some A198683Schoenfield.labelsEight := by
  native_decide

/-- Row-level Schoenfield table certificate for `A198683(8) = 77`. -/
theorem schoenfield_rows_a198683_eight :
    rowCertificateOk rowsEight 429 77 = true := by
  native_decide

/-- Count/Match rows from the n = 9 Schoenfield table. -/
def rowsNine : List (Option Nat) :=
  List.flatten
    [
      [none, none, none, some 3, some 2, none, none, none, none, some 6, some 7, some 9, some 9, some 7, none, none],
      [none, some 17, some 16, none, none, none, some 7, some 20, some 21, none, some 26, some 21, some 15, none, some 17, some 17],
      [some 30, some 22, some 7, some 26, some 21, some 22, some 7, some 21, some 21, some 7, none, none, none, some 45, some 44, none],
      [none, none, none, some 48, some 49, some 51, some 51, some 49, none, none, none, some 59, some 58, none, none, none],
      [some 64, some 63, none, none, some 68, some 49, none, some 7, some 71, some 7, some 68, some 49, some 57, none, some 59, some 59],
      [some 78, some 71, some 7, none, none, some 71, some 7, some 85, some 85, some 7, some 43, some 44, some 45, some 45, some 44, some 48],
      [some 49, some 50, some 51, some 48, some 49, some 51, some 51, some 49, some 62, some 63, some 64, some 64, some 63, some 71, some 7, some 68],
      [some 49, some 71, some 7, some 85, some 85, some 7, some 62, some 63, some 64, some 64, some 63, some 68, some 49, some 85, some 7, some 68],
      [some 49, some 7, some 7, some 49, none, none, none, some 135, some 134, none, none, none, none, some 138, some 139, some 141],
      [some 141, some 139, none, none, none, some 149, some 148, none, none, none, some 139, some 152, some 153, none, some 158, some 153],
      [some 147, none, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139, some 153, some 153, some 139, none, none],
      [none, some 177, some 176, none, some 139, none, none, some 180, some 139, some 183, some 183, some 139, none, none, none, some 191],
      [some 190, none, some 49, none, none, some 194, some 49, some 197, some 197, some 49, none, none, none, some 205, some 204, none],
      [none, none, some 210, some 209, none, some 58, none, some 215, some 58, some 213, some 58, some 215, some 215, some 58, some 208, some 209],
      [some 210, some 210, some 209, some 203, some 208, none, none, some 205, some 210, some 205, some 210, some 230, some 231, none, some 7, some 7],
      [some 49, none, none, none, some 139, some 238, some 7, some 7, some 49, some 244, some 139, some 244, some 139, some 7, some 49, some 175],
      [some 176, some 177, some 177, some 176, some 180, some 139, some 182, some 183, some 180, some 139, some 183, some 183, some 139, some 213, some 58, some 215],
      [some 215, some 58, some 242, some 243, some 244, some 139, some 242, some 243, none, some 281, some 243, some 213, none, some 215, some 215, some 285],
      [some 244, some 139, some 281, some 243, some 244, some 139, some 243, some 243, some 139, some 133, some 134, some 135, some 135, some 134, some 138, some 139],
      [some 140, some 141, some 138, some 139, some 141, some 141, some 139, some 147, some 148, some 149, some 149, some 148, some 152, some 153, some 154, some 139],
      [some 152, some 153, some 158, some 158, some 153, some 147, some 162, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139],
      [some 153, some 153, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 213, some 58, some 215, some 215, some 58, some 208, some 231, some 210, some 210, some 231, some 238, some 7, some 7, some 49, some 244],
      [some 139, some 244, some 139, some 7, some 49, some 213, some 285, some 215, some 215, some 285, some 244, some 139, some 281, some 243, some 244, some 139],
      [some 243, some 243, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 208, some 231, some 210, some 210, some 231, some 244, some 139, some 7, some 49, some 244, some 139, some 243, some 243, some 139, some 208],
      [some 231, some 210, some 210, some 231, some 7, some 49, some 243, some 139, some 7, some 49, some 139, some 139, some 49, none, none, none],
      [some 432, some 431, none, none, none, none, some 435, some 436, some 438, some 438, some 436, none, none, none, some 446, some 445],
      [none, none, none, some 436, some 449, some 450, none, some 455, some 450, some 444, none, some 446, some 446, some 459, some 451, some 436],
      [some 455, some 450, some 451, some 436, some 450, some 450, some 436, none, none, none, some 474, some 473, none, none, none, none],
      [some 477, some 478, some 480, some 480, some 478, none, none, none, some 488, some 487, none, none, none, some 493, some 492, none],
      [none, some 497, some 478, none, some 436, some 500, some 436, some 497, some 478, some 486, none, some 488, some 488, some 507, some 500, some 436],
      [none, none, some 500, some 436, some 514, some 514, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480],
      [some 477, some 478, some 480, some 480, some 478, some 491, some 492, some 493, some 493, some 492, some 500, some 436, some 497, some 478, some 500, some 436],
      [some 514, some 514, some 436, some 491, some 492, some 493, some 493, some 492, some 497, some 478, some 514, some 436, some 497, some 478, some 436, some 436],
      [some 478, none, none, none, some 564, some 563, none, none, none, none, some 567, some 568, some 570, some 570, some 568, none],
      [none, none, some 578, some 577, none, none, none, some 568, some 581, some 582, none, some 587, some 582, some 576, none, some 578],
      [some 578, some 591, some 583, some 568, some 587, some 582, some 583, some 568, some 582, some 582, some 568, none, none, none, some 606, some 605],
      [none, none, none, none, some 609, some 610, some 612, some 612, some 610, none, none, none, some 620, some 619, none, none],
      [none, some 610, some 623, some 624, none, some 629, some 624, some 618, none, some 620, some 620, some 633, some 625, some 610, some 629, some 624],
      [some 625, some 610, some 624, some 624, some 610, none, none, none, some 648, some 647, none, some 436, none, some 478, some 651, some 436],
      [some 478, some 478, some 436, none, none, none, some 662, some 661, none, some 478, none, none, some 665, some 478, some 668, some 668],
      [some 478, none, none, none, some 676, some 675, none, some 610, none, none, some 679, some 610, some 682, some 682, some 610, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 660, some 661, some 662],
      [some 662, some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, none, none, none, some 718, some 717],
      [none, none, none, some 723, some 722, some 718, none, none, some 728, some 727, some 718, some 727, some 728, some 728, some 727, some 721],
      [some 722, some 723, some 723, some 722, none, none, none, some 743, some 742, some 7, some 49, some 139, some 139, some 49, none, some 58],
      [none, some 753, some 58, none, some 487, none, some 758, some 487, some 741, some 742, some 743, some 743, some 742, some 7, some 49, some 139],
      [some 139, some 49, some 756, some 487, some 758, some 758, some 487, some 756, some 487, some 758, some 758, some 487, some 7, some 49, some 139, some 139],
      [some 49, some 646, some 660, some 647, some 661, some 648, some 662, some 648, some 662, some 647, some 661, some 651, some 665, some 436, some 478, some 653],
      [some 667, some 478, some 668, some 651, some 665, some 436, some 478, some 478, some 668, some 478, some 668, some 436, some 478, some 741, some 7, some 742],
      [some 49, some 743, some 139, some 743, some 139, some 742, some 49, none, none, some 825, some 610, none, some 436, some 436, some 478, some 824],
      [some 825, some 825, some 610, none, some 568, some 836, some 568, some 825, some 610, some 741, some 7, none, some 49, some 743, some 139, some 743],
      [some 139, some 844, some 49, some 828, some 436, some 436, some 478, some 836, some 568, some 825, some 610, some 828, some 436, some 436, some 478, some 825],
      [some 610, some 825, some 610, some 436, some 478, some 562, some 563, some 564, some 564, some 563, some 567, some 568, some 569, some 570, some 567, some 568],
      [some 570, some 570, some 568, some 576, some 577, some 578, some 578, some 577, some 581, some 582, some 583, some 568, some 581, some 582, some 587, some 587],
      [some 582, some 576, some 591, some 578, some 578, some 591, some 583, some 568, some 587, some 582, some 583, some 568, some 582, some 582, some 568, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 751, some 58, some 753],
      [some 753, some 58, some 756, none, some 758, some 758, some 932, some 824, some 825, some 825, some 610, some 836, some 568, some 836, some 568, some 825],
      [some 610, some 751, none, some 753, some 753, some 947, some 836, some 568, none, none, some 836, some 568, some 954, some 954, some 568, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 756, some 932, some 758],
      [some 758, some 932, some 836, some 568, some 825, some 610, some 836, some 568, some 954, some 954, some 568, some 756, some 932, some 758, some 758, some 932],
      [some 825, some 610, some 954, some 568, some 825, some 610, some 568, some 568, some 610, some 430, some 431, some 432, some 432, some 431, some 435, some 436],
      [some 437, some 438, some 435, some 436, some 438, some 438, some 436, none, some 445, some 446, some 446, some 445, some 449, some 450, none, some 436],
      [some 449, some 450, some 455, some 455, some 450, some 1016, some 459, some 446, some 446, some 459, some 1023, some 436, some 455, some 450, some 1023, some 436],
      [some 450, some 450, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480, some 477, some 478, some 480, some 480],
      [some 478, some 486, some 487, some 488, some 488, some 487, none, some 492, some 493, some 493, some 492, some 496, none, some 1069, some 478, some 500],
      [some 436, some 500, some 436, some 1069, some 478, some 486, some 507, some 488, some 488, some 507, some 500, some 436, some 513, some 514, some 500, some 436],
      [some 514, some 514, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480, some 477, some 478, some 480, some 480],
      [some 478, some 1063, some 492, some 493, some 493, some 492, some 500, some 436, some 1069, some 478, some 500, some 436, some 514, some 514, some 436, some 1063],
      [some 492, some 493, some 493, some 492, some 1069, some 478, some 514, some 436, some 1069, some 478, some 436, some 436, some 478, some 604, some 605, some 606],
      [some 606, some 605, some 609, some 610, some 611, some 612, some 609, some 610, some 612, some 612, some 610, some 618, some 619, some 620, some 620, some 619],
      [some 623, some 624, some 625, some 610, some 623, some 624, some 629, some 629, some 624, some 618, some 633, some 620, some 620, some 633, some 625, some 610],
      [some 629, some 624, some 625, some 610, some 624, some 624, some 610, some 674, some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682],
      [some 679, some 610, some 682, some 682, some 610, some 660, some 661, some 662, some 662, some 661, some 665, some 478, some 667, some 668, some 665, some 478],
      [some 668, some 668, some 478, some 741, none, some 743, some 743, some 1205, some 7, some 49, some 139, some 139, some 49, some 756, some 487, some 758],
      [some 758, some 487, some 756, some 487, some 758, some 758, some 487, some 7, some 49, some 139, some 139, some 49, some 741, some 7, some 844, some 49],
      [some 743, some 139, some 743, some 139, some 844, some 49, some 828, some 436, some 436, some 478, some 836, some 568, some 825, some 610, some 828, some 436],
      [some 436, some 478, some 825, some 610, some 825, some 610, some 436, some 478, some 674, some 675, some 676, some 676, some 675, some 679, some 610, some 681],
      [some 682, some 679, some 610, some 682, some 682, some 610, some 756, some 487, some 758, some 758, some 487, some 836, some 568, some 825, some 610, some 836],
      [some 568, some 954, some 954, some 568, some 756, some 932, some 758, some 758, some 932, some 825, some 610, some 954, some 568, some 825, some 610, some 568],
      [some 568, some 610, some 604, some 605, some 606, some 606, some 605, some 609, some 610, some 611, some 612, some 609, some 610, some 612, some 612, some 610],
      [some 618, some 619, some 620, some 620, some 619, some 623, some 624, some 625, some 610, some 623, some 624, some 629, some 629, some 624, some 618, some 633],
      [some 620, some 620, some 633, some 625, some 610, some 629, some 624, some 625, some 610, some 624, some 624, some 610, some 660, some 661, some 662, some 662],
      [some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, some 756, some 487, some 758, some 758, some 487, some 7],
      [some 49, some 139, some 139, some 49, some 828, some 436, some 436, some 478, some 825, some 610, some 825, some 610, some 436, some 478, some 756, some 932],
      [some 758, some 758, some 932, some 825, some 610, some 954, some 568, some 825, some 610, some 568, some 568, some 610, some 660, some 661, some 662, some 662],
      [some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, some 7, some 49, some 139, some 139, some 49, some 825],
      [some 610, some 436, some 478, some 825, some 610, some 568, some 568, some 610, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568],
      [some 610, some 436, some 478, some 610, some 610, some 478]
    ]

/-- The n = 9 row data reconstruct exactly the normalized label certificate. -/
theorem rows_nine_reconstruct_labels :
    labelsFromRows rowsNine = some A198683Schoenfield.labelsNine := by
  native_decide

/-- Row-level Schoenfield table certificate for `A198683(9) = 187`. -/
theorem schoenfield_rows_a198683_nine :
    rowCertificateOk rowsNine 1430 187 = true := by
  native_decide

/-- Count/Match rows from the n = 10 Schoenfield table. -/
def rowsTen : List (Option Nat) :=
  List.flatten
    [
      [none, none, none, some 3, some 2, none, none, none, none, some 6, some 7, some 9, some 9, some 7, none, none],
      [none, some 17, some 16, none, none, none, some 7, some 20, some 21, none, some 26, some 21, some 15, none, some 17, some 17],
      [some 30, some 22, some 7, some 26, some 21, some 22, some 7, some 21, some 21, some 7, none, none, none, some 45, some 44, none],
      [none, none, none, some 48, some 49, some 51, some 51, some 49, none, none, none, some 59, some 58, none, none, none],
      [some 64, some 63, none, none, some 68, some 49, none, some 7, some 71, some 7, some 68, some 49, some 57, none, some 59, some 59],
      [some 78, some 71, some 7, none, none, some 71, some 7, some 85, some 85, some 7, some 43, some 44, some 45, some 45, some 44, some 48],
      [some 49, some 50, some 51, some 48, some 49, some 51, some 51, some 49, some 62, some 63, some 64, some 64, some 63, some 71, some 7, some 68],
      [some 49, some 71, some 7, some 85, some 85, some 7, some 62, some 63, some 64, some 64, some 63, some 68, some 49, some 85, some 7, some 68],
      [some 49, some 7, some 7, some 49, none, none, none, some 135, some 134, none, none, none, none, some 138, some 139, some 141],
      [some 141, some 139, none, none, none, some 149, some 148, none, none, none, some 139, some 152, some 153, none, some 158, some 153],
      [some 147, none, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139, some 153, some 153, some 139, none, none],
      [none, some 177, some 176, none, some 139, none, none, some 180, some 139, some 183, some 183, some 139, none, none, none, some 191],
      [some 190, none, some 49, none, none, some 194, some 49, some 197, some 197, some 49, none, none, none, some 205, some 204, none],
      [none, none, some 210, some 209, none, some 58, none, some 215, some 58, some 213, some 58, some 215, some 215, some 58, some 208, some 209],
      [some 210, some 210, some 209, some 203, some 208, none, none, some 205, some 210, some 205, some 210, some 230, some 231, none, some 7, some 7],
      [some 49, none, none, none, some 139, some 238, some 7, some 7, some 49, some 244, some 139, some 244, some 139, some 7, some 49, some 175],
      [some 176, some 177, some 177, some 176, some 180, some 139, some 182, some 183, some 180, some 139, some 183, some 183, some 139, some 213, some 58, some 215],
      [some 215, some 58, some 242, some 243, some 244, some 139, some 242, some 243, none, some 281, some 243, some 213, none, some 215, some 215, some 285],
      [some 244, some 139, some 281, some 243, some 244, some 139, some 243, some 243, some 139, some 133, some 134, some 135, some 135, some 134, some 138, some 139],
      [some 140, some 141, some 138, some 139, some 141, some 141, some 139, some 147, some 148, some 149, some 149, some 148, some 152, some 153, some 154, some 139],
      [some 152, some 153, some 158, some 158, some 153, some 147, some 162, some 149, some 149, some 162, some 154, some 139, some 158, some 153, some 154, some 139],
      [some 153, some 153, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 213, some 58, some 215, some 215, some 58, some 208, some 231, some 210, some 210, some 231, some 238, some 7, some 7, some 49, some 244],
      [some 139, some 244, some 139, some 7, some 49, some 213, some 285, some 215, some 215, some 285, some 244, some 139, some 281, some 243, some 244, some 139],
      [some 243, some 243, some 139, some 189, some 190, some 191, some 191, some 190, some 194, some 49, some 196, some 197, some 194, some 49, some 197, some 197],
      [some 49, some 208, some 231, some 210, some 210, some 231, some 244, some 139, some 7, some 49, some 244, some 139, some 243, some 243, some 139, some 208],
      [some 231, some 210, some 210, some 231, some 7, some 49, some 243, some 139, some 7, some 49, some 139, some 139, some 49, none, none, none],
      [some 432, some 431, none, none, none, none, some 435, some 436, some 438, some 438, some 436, none, none, none, some 446, some 445],
      [none, none, none, some 436, some 449, some 450, none, some 455, some 450, some 444, none, some 446, some 446, some 459, some 451, some 436],
      [some 455, some 450, some 451, some 436, some 450, some 450, some 436, none, none, none, some 474, some 473, none, none, none, none],
      [some 477, some 478, some 480, some 480, some 478, none, none, none, some 488, some 487, none, none, none, some 493, some 492, none],
      [none, some 497, some 478, none, some 436, some 500, some 436, some 497, some 478, some 486, none, some 488, some 488, some 507, some 500, some 436],
      [none, none, some 500, some 436, some 514, some 514, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480],
      [some 477, some 478, some 480, some 480, some 478, some 491, some 492, some 493, some 493, some 492, some 500, some 436, some 497, some 478, some 500, some 436],
      [some 514, some 514, some 436, some 491, some 492, some 493, some 493, some 492, some 497, some 478, some 514, some 436, some 497, some 478, some 436, some 436],
      [some 478, none, none, none, some 564, some 563, none, none, none, none, some 567, some 568, some 570, some 570, some 568, none],
      [none, none, some 578, some 577, none, none, none, some 568, some 581, some 582, none, some 587, some 582, some 576, none, some 578],
      [some 578, some 591, some 583, some 568, some 587, some 582, some 583, some 568, some 582, some 582, some 568, none, none, none, some 606, some 605],
      [none, none, none, none, some 609, some 610, some 612, some 612, some 610, none, none, none, some 620, some 619, none, none],
      [none, some 610, some 623, some 624, none, some 629, some 624, some 618, none, some 620, some 620, some 633, some 625, some 610, some 629, some 624],
      [some 625, some 610, some 624, some 624, some 610, none, none, none, some 648, some 647, none, some 436, none, some 478, some 651, some 436],
      [some 478, some 478, some 436, none, none, none, some 662, some 661, none, some 478, none, none, some 665, some 478, some 668, some 668],
      [some 478, none, none, none, some 676, some 675, none, some 610, none, none, some 679, some 610, some 682, some 682, some 610, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 660, some 661, some 662],
      [some 662, some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, none, none, none, some 718, some 717],
      [none, none, none, some 723, some 722, some 718, none, none, some 728, some 727, some 718, some 727, some 728, some 728, some 727, some 721],
      [some 722, some 723, some 723, some 722, none, none, none, some 743, some 742, some 7, some 49, some 139, some 139, some 49, none, some 58],
      [none, some 753, some 58, none, some 487, none, some 758, some 487, some 741, some 742, some 743, some 743, some 742, some 7, some 49, some 139],
      [some 139, some 49, some 756, some 487, some 758, some 758, some 487, some 756, some 487, some 758, some 758, some 487, some 7, some 49, some 139, some 139],
      [some 49, some 646, some 660, some 647, some 661, some 648, some 662, some 648, some 662, some 647, some 661, some 651, some 665, some 436, some 478, some 653],
      [some 667, some 478, some 668, some 651, some 665, some 436, some 478, some 478, some 668, some 478, some 668, some 436, some 478, some 741, some 7, some 742],
      [some 49, some 743, some 139, some 743, some 139, some 742, some 49, none, none, some 825, some 610, none, some 436, some 436, some 478, some 824],
      [some 825, some 825, some 610, none, some 568, some 836, some 568, some 825, some 610, some 741, some 7, none, some 49, some 743, some 139, some 743],
      [some 139, some 844, some 49, some 828, some 436, some 436, some 478, some 836, some 568, some 825, some 610, some 828, some 436, some 436, some 478, some 825],
      [some 610, some 825, some 610, some 436, some 478, some 562, some 563, some 564, some 564, some 563, some 567, some 568, some 569, some 570, some 567, some 568],
      [some 570, some 570, some 568, some 576, some 577, some 578, some 578, some 577, some 581, some 582, some 583, some 568, some 581, some 582, some 587, some 587],
      [some 582, some 576, some 591, some 578, some 578, some 591, some 583, some 568, some 587, some 582, some 583, some 568, some 582, some 582, some 568, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 751, some 58, some 753],
      [some 753, some 58, some 756, none, some 758, some 758, some 932, some 824, some 825, some 825, some 610, some 836, some 568, some 836, some 568, some 825],
      [some 610, some 751, none, some 753, some 753, some 947, some 836, some 568, none, none, some 836, some 568, some 954, some 954, some 568, some 674],
      [some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682, some 679, some 610, some 682, some 682, some 610, some 756, some 932, some 758],
      [some 758, some 932, some 836, some 568, some 825, some 610, some 836, some 568, some 954, some 954, some 568, some 756, some 932, some 758, some 758, some 932],
      [some 825, some 610, some 954, some 568, some 825, some 610, some 568, some 568, some 610, some 430, some 431, some 432, some 432, some 431, some 435, some 436],
      [some 437, some 438, some 435, some 436, some 438, some 438, some 436, none, some 445, some 446, some 446, some 445, some 449, some 450, none, some 436],
      [some 449, some 450, some 455, some 455, some 450, some 1016, some 459, some 446, some 446, some 459, some 1023, some 436, some 455, some 450, some 1023, some 436],
      [some 450, some 450, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480, some 477, some 478, some 480, some 480],
      [some 478, some 486, some 487, some 488, some 488, some 487, none, some 492, some 493, some 493, some 492, some 496, none, some 1069, some 478, some 500],
      [some 436, some 500, some 436, some 1069, some 478, some 486, some 507, some 488, some 488, some 507, some 500, some 436, some 513, some 514, some 500, some 436],
      [some 514, some 514, some 436, some 472, some 473, some 474, some 474, some 473, some 477, some 478, some 479, some 480, some 477, some 478, some 480, some 480],
      [some 478, some 1063, some 492, some 493, some 493, some 492, some 500, some 436, some 1069, some 478, some 500, some 436, some 514, some 514, some 436, some 1063],
      [some 492, some 493, some 493, some 492, some 1069, some 478, some 514, some 436, some 1069, some 478, some 436, some 436, some 478, some 604, some 605, some 606],
      [some 606, some 605, some 609, some 610, some 611, some 612, some 609, some 610, some 612, some 612, some 610, some 618, some 619, some 620, some 620, some 619],
      [some 623, some 624, some 625, some 610, some 623, some 624, some 629, some 629, some 624, some 618, some 633, some 620, some 620, some 633, some 625, some 610],
      [some 629, some 624, some 625, some 610, some 624, some 624, some 610, some 674, some 675, some 676, some 676, some 675, some 679, some 610, some 681, some 682],
      [some 679, some 610, some 682, some 682, some 610, some 660, some 661, some 662, some 662, some 661, some 665, some 478, some 667, some 668, some 665, some 478],
      [some 668, some 668, some 478, some 741, none, some 743, some 743, some 1205, some 7, some 49, some 139, some 139, some 49, some 756, some 487, some 758],
      [some 758, some 487, some 756, some 487, some 758, some 758, some 487, some 7, some 49, some 139, some 139, some 49, some 741, some 7, some 844, some 49],
      [some 743, some 139, some 743, some 139, some 844, some 49, some 828, some 436, some 436, some 478, some 836, some 568, some 825, some 610, some 828, some 436],
      [some 436, some 478, some 825, some 610, some 825, some 610, some 436, some 478, some 674, some 675, some 676, some 676, some 675, some 679, some 610, some 681],
      [some 682, some 679, some 610, some 682, some 682, some 610, some 756, some 487, some 758, some 758, some 487, some 836, some 568, some 825, some 610, some 836],
      [some 568, some 954, some 954, some 568, some 756, some 932, some 758, some 758, some 932, some 825, some 610, some 954, some 568, some 825, some 610, some 568],
      [some 568, some 610, some 604, some 605, some 606, some 606, some 605, some 609, some 610, some 611, some 612, some 609, some 610, some 612, some 612, some 610],
      [some 618, some 619, some 620, some 620, some 619, some 623, some 624, some 625, some 610, some 623, some 624, some 629, some 629, some 624, some 618, some 633],
      [some 620, some 620, some 633, some 625, some 610, some 629, some 624, some 625, some 610, some 624, some 624, some 610, some 660, some 661, some 662, some 662],
      [some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, some 756, some 487, some 758, some 758, some 487, some 7],
      [some 49, some 139, some 139, some 49, some 828, some 436, some 436, some 478, some 825, some 610, some 825, some 610, some 436, some 478, some 756, some 932],
      [some 758, some 758, some 932, some 825, some 610, some 954, some 568, some 825, some 610, some 568, some 568, some 610, some 660, some 661, some 662, some 662],
      [some 661, some 665, some 478, some 667, some 668, some 665, some 478, some 668, some 668, some 478, some 7, some 49, some 139, some 139, some 49, some 825],
      [some 610, some 436, some 478, some 825, some 610, some 568, some 568, some 610, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568],
      [some 610, some 436, some 478, some 610, some 610, some 478, none, none, none, some 1433, some 1432, none, none, none, none, some 1436],
      [some 1437, some 1439, some 1439, some 1437, none, none, none, some 1447, some 1446, none, none, none, some 1437, some 1450, some 1451, none],
      [some 1456, some 1451, some 1445, none, some 1447, some 1447, some 1460, some 1452, some 1437, some 1456, some 1451, some 1452, some 1437, some 1451, some 1451, some 1437],
      [none, none, none, some 1475, some 1474, none, none, none, none, some 1478, some 1479, some 1481, some 1481, some 1479, none, none],
      [none, some 1489, some 1488, none, none, none, some 1494, some 1493, none, none, some 1498, some 1479, none, some 1437, some 1501, some 1437],
      [some 1498, some 1479, some 1487, none, some 1489, some 1489, some 1508, some 1501, some 1437, none, none, some 1501, some 1437, some 1515, some 1515, some 1437],
      [some 1473, some 1474, some 1475, some 1475, some 1474, some 1478, some 1479, some 1480, some 1481, some 1478, some 1479, some 1481, some 1481, some 1479, some 1492, some 1493],
      [some 1494, some 1494, some 1493, some 1501, some 1437, some 1498, some 1479, some 1501, some 1437, some 1515, some 1515, some 1437, some 1492, some 1493, some 1494, some 1494],
      [some 1493, some 1498, some 1479, some 1515, some 1437, some 1498, some 1479, some 1437, some 1437, some 1479, none, none, none, some 1565, some 1564, none],
      [none, none, none, some 1568, some 1569, some 1571, some 1571, some 1569, none, none, none, some 1579, some 1578, none, none, none],
      [some 1569, some 1582, some 1583, none, some 1588, some 1583, some 1577, none, some 1579, some 1579, some 1592, some 1584, some 1569, some 1588, some 1583, some 1584],
      [some 1569, some 1583, some 1583, some 1569, none, none, none, some 1607, some 1606, none, some 1569, none, none, some 1610, some 1569, some 1613],
      [some 1613, some 1569, none, none, none, some 1621, some 1620, none, some 1479, none, none, some 1624, some 1479, some 1627, some 1627, some 1479],
      [none, none, none, some 1635, some 1634, none, none, none, some 1640, some 1639, none, some 1488, none, some 1645, some 1488, some 1643],
      [some 1488, some 1645, some 1645, some 1488, some 1638, some 1639, some 1640, some 1640, some 1639, some 1633, some 1638, none, none, some 1635, some 1640, some 1635],
      [some 1640, some 1660, some 1661, none, some 1437, some 1437, some 1479, none, none, none, some 1569, some 1668, some 1437, some 1437, some 1479, some 1674],
      [some 1569, some 1674, some 1569, some 1437, some 1479, some 1605, some 1606, some 1607, some 1607, some 1606, some 1610, some 1569, some 1612, some 1613, some 1610, some 1569],
      [some 1613, some 1613, some 1569, some 1643, some 1488, some 1645, some 1645, some 1488, some 1672, some 1673, some 1674, some 1569, some 1672, some 1673, none, some 1711],
      [some 1673, some 1643, none, some 1645, some 1645, some 1715, some 1674, some 1569, some 1711, some 1673, some 1674, some 1569, some 1673, some 1673, some 1569, some 1563],
      [some 1564, some 1565, some 1565, some 1564, some 1568, some 1569, some 1570, some 1571, some 1568, some 1569, some 1571, some 1571, some 1569, some 1577, some 1578, some 1579],
      [some 1579, some 1578, some 1582, some 1583, some 1584, some 1569, some 1582, some 1583, some 1588, some 1588, some 1583, some 1577, some 1592, some 1579, some 1579, some 1592],
      [some 1584, some 1569, some 1588, some 1583, some 1584, some 1569, some 1583, some 1583, some 1569, some 1619, some 1620, some 1621, some 1621, some 1620, some 1624, some 1479],
      [some 1626, some 1627, some 1624, some 1479, some 1627, some 1627, some 1479, some 1643, some 1488, some 1645, some 1645, some 1488, some 1638, some 1661, some 1640, some 1640],
      [some 1661, some 1668, some 1437, some 1437, some 1479, some 1674, some 1569, some 1674, some 1569, some 1437, some 1479, some 1643, some 1715, some 1645, some 1645, some 1715],
      [some 1674, some 1569, some 1711, some 1673, some 1674, some 1569, some 1673, some 1673, some 1569, some 1619, some 1620, some 1621, some 1621, some 1620, some 1624, some 1479],
      [some 1626, some 1627, some 1624, some 1479, some 1627, some 1627, some 1479, some 1638, some 1661, some 1640, some 1640, some 1661, some 1674, some 1569, some 1437, some 1479],
      [some 1674, some 1569, some 1673, some 1673, some 1569, some 1638, some 1661, some 1640, some 1640, some 1661, some 1437, some 1479, some 1673, some 1569, some 1437, some 1479],
      [some 1569, some 1569, some 1479, none, none, none, some 1862, some 1861, none, none, none, none, some 1865, some 1866, some 1868, some 1868],
      [some 1866, none, none, none, some 1876, some 1875, none, none, none, some 1866, some 1879, some 1880, none, some 1885, some 1880, some 1874],
      [none, some 1876, some 1876, some 1889, some 1881, some 1866, some 1885, some 1880, some 1881, some 1866, some 1880, some 1880, some 1866, none, none, none],
      [some 1904, some 1903, none, none, none, none, some 1907, some 1908, some 1910, some 1910, some 1908, none, some 1488, none, some 1918, some 1488],
      [none, none, none, some 1923, some 1922, none, none, some 1927, some 1908, none, some 1866, some 1930, some 1866, some 1927, some 1908, some 1916],
      [none, some 1918, some 1918, some 1937, some 1930, some 1866, none, none, some 1930, some 1866, some 1944, some 1944, some 1866, some 1902, some 1903, some 1904],
      [some 1904, some 1903, some 1907, some 1908, some 1909, some 1910, some 1907, some 1908, some 1910, some 1910, some 1908, some 1921, some 1922, some 1923, some 1923, some 1922],
      [some 1930, some 1866, some 1927, some 1908, some 1930, some 1866, some 1944, some 1944, some 1866, some 1921, some 1922, some 1923, some 1923, some 1922, some 1927, some 1908],
      [some 1944, some 1866, some 1927, some 1908, some 1866, some 1866, some 1908, none, none, none, some 1994, some 1993, none, none, none, none],
      [some 1997, some 1998, some 2000, some 2000, some 1998, none, none, none, some 2008, some 2007, none, none, none, some 1998, some 2011, some 2012],
      [none, some 2017, some 2012, some 2006, none, some 2008, some 2008, some 2021, some 2013, some 1998, some 2017, some 2012, some 2013, some 1998, some 2012, some 2012],
      [some 1998, none, none, none, some 2036, some 2035, none, some 478, none, none, some 2039, some 478, some 2042, some 2042, some 478, none],
      [some 487, none, some 2050, some 487, none, none, none, some 2055, some 2054, none, none, some 2059, some 478, none, some 1998, some 2062],
      [some 1998, some 2059, some 478, some 2048, none, some 2050, some 2050, some 2069, some 2062, some 1998, none, none, some 2062, some 1998, some 2076, some 2076],
      [some 1998, some 2034, some 2035, some 2036, some 2036, some 2035, some 2039, some 478, some 2041, some 2042, some 2039, some 478, some 2042, some 2042, some 478, some 2053],
      [some 2054, some 2055, some 2055, some 2054, some 2062, some 1998, some 2059, some 478, some 2062, some 1998, some 2076, some 2076, some 1998, some 2053, some 2054, some 2055],
      [some 2055, some 2054, some 2059, some 478, some 2076, some 1998, some 2059, some 478, some 1998, some 1998, some 478, none, none, none, some 2126, some 2125],
      [none, some 1866, none, none, some 2129, some 1866, some 2132, some 2132, some 1866, none, none, none, some 2140, some 2139, none, none],
      [none, some 1866, some 2143, some 2144, none, some 2149, some 2144, some 2138, none, some 2140, some 2140, some 2153, some 2145, some 1866, some 2149, some 2144],
      [some 2145, some 1866, some 2144, some 2144, some 1866, none, none, none, some 2168, some 2167, none, some 1908, none, none, some 2171, some 1908],
      [some 2174, some 2174, some 1908, none, none, none, some 2182, some 2181, none, none, none, some 1908, some 2185, some 2186, none, some 2191],
      [some 2186, some 2180, none, some 2182, some 2182, some 2195, some 2187, some 1908, some 2191, some 2186, some 2187, some 1908, some 2186, some 2186, some 1908, none],
      [none, none, some 2210, some 2209, none, none, none, none, some 2213, some 2214, some 2216, some 2216, some 2214, none, none, none],
      [some 2224, some 2223, none, none, none, some 2214, some 2227, some 2228, none, some 2233, some 2228, some 2222, none, some 2224, some 2224, some 2237],
      [some 2229, some 2214, some 2233, some 2228, some 2229, some 2214, some 2228, some 2228, some 2214, some 2208, some 2209, some 2210, some 2210, some 2209, some 2213, some 2214],
      [some 2215, some 2216, some 2213, some 2214, some 2216, some 2216, some 2214, some 2222, some 2223, some 2224, some 2224, some 2223, some 2227, some 2228, some 2229, some 2214],
      [some 2227, some 2228, some 2233, some 2233, some 2228, some 2222, some 2237, some 2224, some 2224, some 2237, some 2229, some 2214, some 2233, some 2228, some 2229, some 2214],
      [some 2228, some 2228, some 2214, some 2166, some 2167, some 2168, some 2168, some 2167, some 2171, some 1908, some 2173, some 2174, some 2171, some 1908, some 2174, some 2174],
      [some 1908, some 2180, some 2181, some 2182, some 2182, some 2181, some 2185, some 2186, some 2187, some 1908, some 2185, some 2186, some 2191, some 2191, some 2186, some 2180],
      [some 2195, some 2182, some 2182, some 2195, some 2187, some 1908, some 2191, some 2186, some 2187, some 1908, some 2186, some 2186, some 1908, none, none, none],
      [some 2336, some 2335, none, some 1437, none, none, some 2339, some 1437, some 2342, some 2342, some 1437, none, none, none, some 2350, some 2349],
      [none, none, none, none, some 2353, some 2354, some 2356, some 2356, some 2354, none, none, none, some 2364, some 2363, none, some 1569],
      [none, none, some 2367, some 1569, some 2370, some 2370, some 1569, some 2362, some 2363, some 2364, some 2364, some 2363, some 2367, some 1569, some 2369, some 2370],
      [some 2367, some 1569, some 2370, some 2370, some 1569, some 2348, some 2349, some 2350, some 2350, some 2349, some 2353, some 2354, some 2355, some 2356, some 2353, some 2354],
      [some 2356, some 2356, some 2354, none, none, none, some 2406, some 2405, none, some 1998, none, some 478, some 2409, some 1998, some 478, some 478],
      [some 1998, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478, some 610, some 610, some 478, none],
      [none, none, some 2434, some 2433, none, some 2214, none, none, some 2437, some 2214, some 2440, some 2440, some 2214, none, none, none],
      [some 2448, some 2447, none, some 1908, none, none, some 2451, some 1908, some 2454, some 2454, some 1908, some 2404, some 2405, some 2406, some 2406, some 2405],
      [some 2409, some 1998, some 2411, some 478, some 2409, some 1998, some 478, some 478, some 1998, some 7, some 49, some 139, some 139, some 49, some 436, some 478],
      [some 568, some 610, some 436, some 478, some 610, some 610, some 478, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454],
      [some 2451, some 1908, some 2454, some 2454, some 1908, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454, some 2451, some 1908],
      [some 2454, some 2454, some 1908, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478, some 610, some 610],
      [some 478, some 2334, none, some 2362, some 2362, some 2531, some 2335, none, some 2363, some 2363, some 2536, some 2336, none, some 2364, some 2364, some 2541],
      [some 2336, some 2541, some 2364, some 2364, some 2541, some 2335, some 2536, some 2363, some 2363, some 2536, some 2339, none, some 2367, some 2367, some 2556, some 1437],
      [some 1479, some 1569, some 1569, some 1479, some 2341, none, some 2369, some 2369, some 2566, some 2342, none, some 2370, some 2370, some 2571, some 2339, some 2556],
      [some 2367, some 2367, some 2556, some 1437, some 1479, some 1569, some 1569, some 1479, some 2342, some 2571, some 2370, some 2370, some 2571, some 2342, some 2571, some 2370],
      [some 2370, some 2571, some 1437, some 1479, some 1569, some 1569, some 1479, none, none, none, some 2602, some 2601, some 2601, none, none, some 2607],
      [some 2606, some 2602, some 2607, none, some 2612, some 2607, some 2602, some 2607, some 2612, some 2612, some 2607, some 2601, some 2606, some 2607, some 2607, some 2606],
      [none, some 58, none, some 2627, some 58, none, some 487, none, some 2632, some 487, none, none, none, some 2637, some 2636, some 1437],
      [some 1479, some 1569, some 1569, some 1479, some 2625, some 58, some 2627, some 2627, some 58, some 2630, some 487, some 2632, some 2632, some 487, none, some 1488],
      [none, some 2657, some 1488, some 2655, some 1488, some 2657, some 2657, some 1488, some 2630, some 487, some 2632, some 2632, some 487, some 2600, some 2601, some 2602],
      [some 2602, some 2601, none, none, none, some 2677, some 2676, some 2602, some 2607, some 2612, some 2612, some 2607, some 2602, some 2607, some 2612, some 2612],
      [some 2607, some 2675, some 2676, some 2677, some 2677, some 2676, some 2635, some 2636, some 2637, some 2637, some 2636, some 1437, some 1479, some 1569, some 1569, some 1479],
      [some 2655, some 1488, some 2657, some 2657, some 1488, some 2630, some 487, some 2632, some 2632, some 487, some 2635, some 2636, some 2637, some 2637, some 2636, some 1437],
      [some 1479, some 1569, some 1569, some 1479, some 2630, some 487, some 2632, some 2632, some 487, some 2630, some 487, some 2632, some 2632, some 487, some 1437, some 1479],
      [some 1569, some 1569, some 1479, some 2124, some 2166, some 2125, some 2167, some 2126, some 2168, some 2126, some 2168, some 2125, some 2167, some 2129, some 2171, some 1866],
      [some 1908, some 2131, some 2173, some 2132, some 2174, some 2129, some 2171, some 1866, some 1908, some 2132, some 2174, some 2132, some 2174, some 1866, some 1908, some 2138],
      [some 2180, some 2139, some 2181, some 2140, some 2182, some 2140, some 2182, some 2139, some 2181, some 2143, some 2185, some 2144, some 2186, some 2145, some 2187, some 1866],
      [some 1908, some 2143, some 2185, some 2144, some 2186, some 2149, some 2191, some 2149, some 2191, some 2144, some 2186, some 2138, some 2180, some 2153, some 2195, some 2140],
      [some 2182, some 2140, some 2182, some 2153, some 2195, some 2145, some 2187, some 1866, some 1908, some 2149, some 2191, some 2144, some 2186, some 2145, some 2187, some 1866],
      [some 1908, some 2144, some 2186, some 2144, some 2186, some 1866, some 1908, some 2404, some 7, some 2405, some 49, some 2406, some 139, some 2406, some 139, some 2405],
      [some 49, some 2409, some 436, some 1998, some 478, some 2411, some 568, some 478, some 610, some 2409, some 436, some 1998, some 478, some 478, some 610, some 478],
      [some 610, some 1998, some 478, some 2625, some 2630, some 58, some 487, some 2627, some 2632, some 2627, some 2632, some 58, some 487, some 2635, some 1437, none],
      [some 2354, some 2637, some 1569, some 2637, some 1569, some 2864, some 2354, none, none, some 2873, some 1998, some 2873, some 1998, some 1998, some 478, none],
      [some 1866, some 1866, some 1908, some 2880, some 1866, some 1866, some 1908, some 2873, some 1998, some 1998, some 478, some 2625, some 2630, none, none, some 2627],
      [some 2632, some 2627, some 2632, some 2894, some 2895, some 2880, some 1866, some 1866, some 1908, none, none, none, some 2214, some 2880, some 1866, some 1866],
      [some 1908, some 2908, some 2214, some 2908, some 2214, some 1866, some 1908, some 2404, some 7, some 2405, some 49, some 2406, some 139, some 2406, some 139, some 2405],
      [some 49, some 2409, some 436, some 1998, some 478, some 2411, some 568, some 478, some 610, some 2409, some 436, some 1998, some 478, some 478, some 610, some 478],
      [some 610, some 1998, some 478, some 2635, some 1437, some 2864, some 2354, some 2637, some 1569, some 2637, some 1569, some 2864, some 2354, some 2880, some 1866, some 1866],
      [some 1908, some 2873, some 1998, some 1998, some 478, some 2880, some 1866, some 1866, some 1908, some 2908, some 2214, some 2908, some 2214, some 1866, some 1908, some 2635],
      [some 1437, some 2864, some 2354, some 2637, some 1569, some 2637, some 1569, some 2864, some 2354, some 2873, some 1998, some 1998, some 478, some 2908, some 2214, some 1866],
      [some 1908, some 2873, some 1998, some 1998, some 478, some 1866, some 1908, some 1866, some 1908, some 1998, some 478, some 1860, some 1861, some 1862, some 1862, some 1861],
      [some 1865, some 1866, some 1867, some 1868, some 1865, some 1866, some 1868, some 1868, some 1866, none, some 1875, some 1876, some 1876, some 1875, some 1879, some 1880],
      [none, some 1866, some 1879, some 1880, some 1885, some 1885, some 1880, some 3018, some 1889, some 1876, some 1876, some 1889, some 3025, some 1866, some 1885, some 1880],
      [some 3025, some 1866, some 1880, some 1880, some 1866, some 1902, some 1903, some 1904, some 1904, some 1903, some 1907, some 1908, some 1909, some 1910, some 1907, some 1908],
      [some 1910, some 1910, some 1908, some 1916, some 1488, some 1918, some 1918, some 1488, none, some 1922, some 1923, some 1923, some 1922, some 1926, none, some 3071],
      [some 1908, some 1930, some 1866, some 1930, some 1866, some 3071, some 1908, some 1916, some 1937, some 1918, some 1918, some 1937, some 1930, some 1866, some 1943, some 1944],
      [some 1930, some 1866, some 1944, some 1944, some 1866, some 1902, some 1903, some 1904, some 1904, some 1903, some 1907, some 1908, some 1909, some 1910, some 1907, some 1908],
      [some 1910, some 1910, some 1908, some 3065, some 1922, some 1923, some 1923, some 1922, some 1930, some 1866, some 3071, some 1908, some 1930, some 1866, some 1944, some 1944],
      [some 1866, some 3065, some 1922, some 1923, some 1923, some 1922, some 3071, some 1908, some 1944, some 1866, some 3071, some 1908, some 1866, some 1866, some 1908, some 2208],
      [some 2209, some 2210, some 2210, some 2209, some 2213, some 2214, some 2215, some 2216, some 2213, some 2214, some 2216, some 2216, some 2214, some 2222, some 2223, some 2224],
      [some 2224, some 2223, some 2227, some 2228, some 2229, some 2214, some 2227, some 2228, some 2233, some 2233, some 2228, some 2222, some 2237, some 2224, some 2224, some 2237],
      [some 2229, some 2214, some 2233, some 2228, some 2229, some 2214, some 2228, some 2228, some 2214, some 2432, some 2433, some 2434, some 2434, some 2433, some 2437, some 2214],
      [some 2439, some 2440, some 2437, some 2214, some 2440, some 2440, some 2214, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454],
      [some 2451, some 1908, some 2454, some 2454, some 1908, some 2625, none, some 2627, some 2627, some 3207, some 2630, some 487, some 2632, some 2632, some 487, some 2655],
      [some 1488, some 2657, some 2657, some 1488, some 2655, some 1488, some 2657, some 2657, some 1488, some 2630, some 487, some 2632, some 2632, some 487, some 2625, some 2630],
      [some 2894, some 2895, some 2627, some 2632, some 2627, some 2632, some 2894, some 2895, some 2880, some 1866, some 1866, some 1908, some 2906, some 2907, some 2908, some 2214],
      [some 2880, some 1866, some 1866, some 1908, some 2908, some 2214, some 2908, some 2214, some 1866, some 1908, some 2432, some 2433, some 2434, some 2434, some 2433, some 2437],
      [some 2214, some 2439, some 2440, some 2437, some 2214, some 2440, some 2440, some 2214, some 2655, some 1488, some 2657, some 2657, some 1488, some 2906, some 2907, some 2908],
      [some 2214, some 2906, some 2907, none, some 3284, some 2907, some 2655, none, some 2657, some 2657, some 3288, some 2908, some 2214, some 3284, some 2907, some 2908],
      [some 2214, some 2907, some 2907, some 2214, some 2208, some 2209, some 2210, some 2210, some 2209, some 2213, some 2214, some 2215, some 2216, some 2213, some 2214, some 2216],
      [some 2216, some 2214, some 2222, some 2223, some 2224, some 2224, some 2223, some 2227, some 2228, some 2229, some 2214, some 2227, some 2228, some 2233, some 2233, some 2228],
      [some 2222, some 2237, some 2224, some 2224, some 2237, some 2229, some 2214, some 2233, some 2228, some 2229, some 2214, some 2228, some 2228, some 2214, some 2446, some 2447],
      [some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454, some 2451, some 1908, some 2454, some 2454, some 1908, some 2655, some 1488, some 2657, some 2657],
      [some 1488, some 2630, some 2895, some 2632, some 2632, some 2895, some 2880, some 1866, some 1866, some 1908, some 2908, some 2214, some 2908, some 2214, some 1866, some 1908],
      [some 2655, some 3288, some 2657, some 2657, some 3288, some 2908, some 2214, some 3284, some 2907, some 2908, some 2214, some 2907, some 2907, some 2214, some 2446, some 2447],
      [some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454, some 2451, some 1908, some 2454, some 2454, some 1908, some 2630, some 2895, some 2632, some 2632],
      [some 2895, some 2908, some 2214, some 1866, some 1908, some 2908, some 2214, some 2907, some 2907, some 2214, some 2630, some 2895, some 2632, some 2632, some 2895, some 1866],
      [some 1908, some 2907, some 2214, some 1866, some 1908, some 2214, some 2214, some 1908, some 1431, some 1432, some 1433, some 1433, some 1432, some 1436, some 1437, some 1438],
      [some 1439, some 1436, some 1437, some 1439, some 1439, some 1437, some 1445, some 1446, some 1447, some 1447, some 1446, some 1450, some 1451, some 1452, some 1437, some 1450],
      [some 1451, some 1456, some 1456, some 1451, some 1445, some 1460, some 1447, some 1447, some 1460, some 1452, some 1437, some 1456, some 1451, some 1452, some 1437, some 1451],
      [some 1451, some 1437, some 1473, none, none, some 3477, some 3476, some 1478, some 2354, some 1480, some 1481, some 1478, some 2354, some 1481, some 1481, some 2354],
      [some 1487, some 1488, some 1489, some 1489, some 1488, some 1492, none, none, some 3496, some 3495, some 1497, some 1498, some 1498, some 2354, some 1501, some 1437],
      [some 1501, some 1437, some 1498, some 2354, some 1487, some 1508, some 1489, some 1489, some 1508, some 1501, some 1437, some 1514, some 1515, some 1501, some 1437, some 1515],
      [some 1515, some 1437, some 1473, some 3476, some 3477, some 3477, some 3476, some 1478, some 2354, some 1480, some 1481, some 1478, some 2354, some 1481, some 1481, some 2354],
      [some 1492, some 3495, some 3496, some 3496, some 3495, some 1501, some 1437, some 1498, some 2354, some 1501, some 1437, some 1515, some 1515, some 1437, some 1492, some 3495],
      [some 3496, some 3496, some 3495, some 1498, some 2354, some 1515, some 1437, some 1498, some 2354, some 1437, some 1437, some 2354, some 1563, some 1564, some 1565, some 1565],
      [some 1564, some 1568, some 1569, some 1570, some 1571, some 1568, some 1569, some 1571, some 1571, some 1569, some 1577, some 1578, some 1579, some 1579, some 1578, some 1582],
      [some 1583, some 1584, some 1569, some 1582, some 1583, some 1588, some 1588, some 1583, some 1577, some 1592, some 1579, some 1579, some 1592, some 1584, some 1569, some 1588],
      [some 1583, some 1584, some 1569, some 1583, some 1583, some 1569, some 1605, some 1606, some 1607, some 1607, some 1606, some 1610, some 1569, some 1612, some 1613, some 1610],
      [some 1569, some 1613, some 1613, some 1569, some 1619, none, none, some 3623, some 3622, some 1624, some 2354, some 1626, some 1627, some 1624, some 2354, some 1627],
      [some 1627, some 2354, some 1633, some 1634, some 1635, some 1635, some 1634, some 1638, none, none, some 3642, some 3641, some 1643, some 1488, some 1645, some 1645],
      [some 1488, some 1643, some 1488, some 1645, some 1645, some 1488, some 1638, some 3641, some 3642, some 3642, some 3641, some 1633, some 1638, some 1660, none, some 1635],
      [some 3642, some 1635, some 3642, some 1660, some 3663, some 1668, some 1437, some 1437, some 2354, some 1672, some 1673, some 1674, some 1569, some 1668, some 1437, some 1437],
      [some 2354, some 1674, some 1569, some 1674, some 1569, some 1437, some 2354, some 1605, some 1606, some 1607, some 1607, some 1606, some 1610, some 1569, some 1612, some 1613],
      [some 1610, some 1569, some 1613, some 1613, some 1569, some 1643, some 1488, some 1645, some 1645, some 1488, some 1672, some 1673, some 1674, some 1569, some 1672, some 1673],
      [some 1711, some 1711, some 1673, some 1643, some 1715, some 1645, some 1645, some 1715, some 1674, some 1569, some 1711, some 1673, some 1674, some 1569, some 1673, some 1673],
      [some 1569, some 1563, some 1564, some 1565, some 1565, some 1564, some 1568, some 1569, some 1570, some 1571, some 1568, some 1569, some 1571, some 1571, some 1569, some 1577],
      [some 1578, some 1579, some 1579, some 1578, some 1582, some 1583, some 1584, some 1569, some 1582, some 1583, some 1588, some 1588, some 1583, some 1577, some 1592, some 1579],
      [some 1579, some 1592, some 1584, some 1569, some 1588, some 1583, some 1584, some 1569, some 1583, some 1583, some 1569, some 1619, some 3622, some 3623, some 3623, some 3622],
      [some 1624, some 2354, some 1626, some 1627, some 1624, some 2354, some 1627, some 1627, some 2354, some 1643, some 1488, some 1645, some 1645, some 1488, some 1638, some 3663],
      [some 3642, some 3642, some 3663, some 1668, some 1437, some 1437, some 2354, some 1674, some 1569, some 1674, some 1569, some 1437, some 2354, some 1643, some 1715, some 1645],
      [some 1645, some 1715, some 1674, some 1569, some 1711, some 1673, some 1674, some 1569, some 1673, some 1673, some 1569, some 1619, some 3622, some 3623, some 3623, some 3622],
      [some 1624, some 2354, some 1626, some 1627, some 1624, some 2354, some 1627, some 1627, some 2354, some 1638, some 3663, some 3642, some 3642, some 3663, some 1674, some 1569],
      [some 1437, some 2354, some 1674, some 1569, some 1673, some 1673, some 1569, some 1638, some 3663, some 3642, some 3642, some 3663, some 1437, some 2354, some 1673, some 1569],
      [some 1437, some 2354, some 1569, some 1569, some 2354, some 1992, some 1993, some 1994, some 1994, some 1993, some 1997, some 1998, some 1999, some 2000, some 1997, some 1998],
      [some 2000, some 2000, some 1998, none, some 2007, some 2008, some 2008, some 2007, some 2011, some 2012, none, some 1998, some 2011, some 2012, some 2017, some 2017],
      [some 2012, some 3876, some 2021, some 2008, some 2008, some 2021, some 3883, some 1998, some 2017, some 2012, some 3883, some 1998, some 2012, some 2012, some 1998, some 2034],
      [some 2035, some 2036, some 2036, some 2035, some 2039, some 478, some 2041, some 2042, some 2039, some 478, some 2042, some 2042, some 478, some 2048, some 487, some 2050],
      [some 2050, some 487, some 2053, some 2054, some 2055, some 2055, some 2054, some 2058, none, some 3929, some 478, some 2062, some 1998, some 2062, some 1998, some 3929],
      [some 478, some 2048, some 2069, some 2050, some 2050, some 2069, some 2062, some 1998, some 2075, some 2076, some 2062, some 1998, some 2076, some 2076, some 1998, some 2034],
      [some 2035, some 2036, some 2036, some 2035, some 2039, some 478, some 2041, some 2042, some 2039, some 478, some 2042, some 2042, some 478, some 2053, some 2054, some 2055],
      [some 2055, some 2054, some 2062, some 1998, some 3929, some 478, some 2062, some 1998, some 2076, some 2076, some 1998, some 2053, some 2054, some 2055, some 2055, some 2054],
      [some 3929, some 478, some 2076, some 1998, some 3929, some 478, some 1998, some 1998, some 478, some 2208, some 2209, some 2210, some 2210, some 2209, some 2213, some 2214],
      [some 2215, some 2216, some 2213, some 2214, some 2216, some 2216, some 2214, some 2222, some 2223, some 2224, some 2224, some 2223, some 2227, some 2228, some 2229, some 2214],
      [some 2227, some 2228, some 2233, some 2233, some 2228, some 2222, some 2237, some 2224, some 2224, some 2237, some 2229, some 2214, some 2233, some 2228, some 2229, some 2214],
      [some 2228, some 2228, some 2214, some 2166, some 2167, some 2168, some 2168, some 2167, some 2171, some 1908, some 2173, some 2174, some 2171, some 1908, some 2174, some 2174],
      [some 1908, some 2180, some 2181, some 2182, some 2182, some 2181, some 2185, some 2186, some 2187, some 1908, some 2185, some 2186, some 2191, some 2191, some 2186, some 2180],
      [some 2195, some 2182, some 2182, some 2195, some 2187, some 1908, some 2191, some 2186, some 2187, some 1908, some 2186, some 2186, some 1908, some 2404, some 2405, some 2406],
      [some 2406, some 2405, some 2409, some 1998, some 2411, some 478, some 2409, some 1998, some 478, some 478, some 1998, some 7, some 49, some 139, some 139, some 49],
      [some 436, some 478, some 568, some 610, some 436, some 478, some 610, some 610, some 478, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908],
      [some 2453, some 2454, some 2451, some 1908, some 2454, some 2454, some 1908, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454],
      [some 2451, some 1908, some 2454, some 2454, some 1908, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478],
      [some 610, some 610, some 478, some 2600, some 2601, some 2602, some 2602, some 2601, some 2675, none, some 2677, some 2677, some 4154, some 2602, none, some 2612],
      [some 2612, some 4159, some 2602, some 4159, some 2612, some 2612, some 4159, some 2675, some 4154, some 2677, some 2677, some 4154, some 2635, some 2636, some 2637, some 2637],
      [some 2636, some 1437, some 2354, some 1569, some 1569, some 2354, some 2655, some 1488, some 2657, some 2657, some 1488, some 2630, some 487, some 2632, some 2632, some 487],
      [some 2635, some 2636, some 2637, some 2637, some 2636, some 1437, some 2354, some 1569, some 1569, some 2354, some 2630, some 487, some 2632, some 2632, some 487, some 2630],
      [some 487, some 2632, some 2632, some 487, some 1437, some 2354, some 1569, some 1569, some 2354, some 2404, some 7, some 2405, some 49, some 2406, some 139, some 2406],
      [some 139, some 2405, some 49, some 2409, some 436, some 1998, some 478, some 2411, some 568, some 478, some 610, some 2409, some 436, some 1998, some 478, some 478],
      [some 610, some 478, some 610, some 1998, some 478, some 2635, some 1437, some 2636, some 2354, some 2637, some 1569, some 2637, some 1569, some 2636, some 2354, some 2880],
      [some 1866, some 1866, some 1908, some 2873, some 1998, some 1998, some 478, some 2880, some 1866, some 1866, some 1908, some 2908, some 2214, some 2908, some 2214, some 1866],
      [some 1908, some 2635, some 1437, some 2864, some 2354, some 2637, some 1569, some 2637, some 1569, some 2864, some 2354, some 2873, some 1998, some 1998, some 478, some 2908],
      [some 2214, some 1866, some 1908, some 2873, some 1998, some 1998, some 478, some 1866, some 1908, some 1866, some 1908, some 1998, some 478, some 2208, some 2209, some 2210],
      [some 2210, some 2209, some 2213, some 2214, some 2215, some 2216, some 2213, some 2214, some 2216, some 2216, some 2214, some 2222, some 2223, some 2224, some 2224, some 2223],
      [some 2227, some 2228, some 2229, some 2214, some 2227, some 2228, some 2233, some 2233, some 2228, some 2222, some 2237, some 2224, some 2224, some 2237, some 2229, some 2214],
      [some 2233, some 2228, some 2229, some 2214, some 2228, some 2228, some 2214, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454],
      [some 2451, some 1908, some 2454, some 2454, some 1908, some 2655, some 1488, some 2657, some 2657, some 1488, some 2630, some 2895, some 2632, some 2632, some 2895, some 2880],
      [some 1866, some 1866, some 1908, some 2908, some 2214, some 2908, some 2214, some 1866, some 1908, some 2655, some 3288, some 2657, some 2657, some 3288, some 2908, some 2214],
      [some 3284, some 2907, some 2908, some 2214, some 2907, some 2907, some 2214, some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454],
      [some 2451, some 1908, some 2454, some 2454, some 1908, some 2630, some 2895, some 2632, some 2632, some 2895, some 2908, some 2214, some 1866, some 1908, some 2908, some 2214],
      [some 2907, some 2907, some 2214, some 2630, some 2895, some 2632, some 2632, some 2895, some 1866, some 1908, some 2907, some 2214, some 1866, some 1908, some 2214, some 2214],
      [some 1908, some 1992, some 1993, some 1994, some 1994, some 1993, some 1997, some 1998, some 1999, some 2000, some 1997, some 1998, some 2000, some 2000, some 1998, some 3876],
      [some 2007, some 2008, some 2008, some 2007, some 2011, some 2012, some 3883, some 1998, some 2011, some 2012, some 2017, some 2017, some 2012, some 3876, some 2021, some 2008],
      [some 2008, some 2021, some 3883, some 1998, some 2017, some 2012, some 3883, some 1998, some 2012, some 2012, some 1998, some 2034, some 2035, some 2036, some 2036, some 2035],
      [some 2039, some 478, some 2041, some 2042, some 2039, some 478, some 2042, some 2042, some 478, some 2048, some 487, some 2050, some 2050, some 487, some 2053, some 2054],
      [some 2055, some 2055, some 2054, some 2058, some 3929, some 3929, some 478, some 2062, some 1998, some 2062, some 1998, some 3929, some 478, some 2048, some 2069, some 2050],
      [some 2050, some 2069, some 2062, some 1998, some 2075, some 2076, some 2062, some 1998, some 2076, some 2076, some 1998, some 2034, some 2035, some 2036, some 2036, some 2035],
      [some 2039, some 478, some 2041, some 2042, some 2039, some 478, some 2042, some 2042, some 478, some 2053, some 2054, some 2055, some 2055, some 2054, some 2062, some 1998],
      [some 3929, some 478, some 2062, some 1998, some 2076, some 2076, some 1998, some 2053, some 2054, some 2055, some 2055, some 2054, some 3929, some 478, some 2076, some 1998],
      [some 3929, some 478, some 1998, some 1998, some 478, some 2166, some 2167, some 2168, some 2168, some 2167, some 2171, some 1908, some 2173, some 2174, some 2171, some 1908],
      [some 2174, some 2174, some 1908, some 2180, some 2181, some 2182, some 2182, some 2181, some 2185, some 2186, some 2187, some 1908, some 2185, some 2186, some 2191, some 2191],
      [some 2186, some 2180, some 2195, some 2182, some 2182, some 2195, some 2187, some 1908, some 2191, some 2186, some 2187, some 1908, some 2186, some 2186, some 1908, some 2446],
      [some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454, some 2451, some 1908, some 2454, some 2454, some 1908, some 7, some 49, some 139],
      [some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478, some 610, some 610, some 478, some 2635, some 2636, some 2637, some 2637, some 2636],
      [some 1437, some 2354, some 1569, some 1569, some 2354, some 2630, some 487, some 2632, some 2632, some 487, some 2630, some 487, some 2632, some 2632, some 487, some 1437],
      [some 2354, some 1569, some 1569, some 2354, some 2635, some 1437, some 2864, some 2354, some 2637, some 1569, some 2637, some 1569, some 2864, some 2354, some 2873, some 1998],
      [some 1998, some 478, some 2908, some 2214, some 1866, some 1908, some 2873, some 1998, some 1998, some 478, some 1866, some 1908, some 1866, some 1908, some 1998, some 478],
      [some 2446, some 2447, some 2448, some 2448, some 2447, some 2451, some 1908, some 2453, some 2454, some 2451, some 1908, some 2454, some 2454, some 1908, some 2630, some 487],
      [some 2632, some 2632, some 487, some 2908, some 2214, some 1866, some 1908, some 2908, some 2214, some 2907, some 2907, some 2214, some 2630, some 2895, some 2632, some 2632],
      [some 2895, some 1866, some 1908, some 2907, some 2214, some 1866, some 1908, some 2214, some 2214, some 1908, some 2166, some 2167, some 2168, some 2168, some 2167, some 2171],
      [some 1908, some 2173, some 2174, some 2171, some 1908, some 2174, some 2174, some 1908, some 2180, some 2181, some 2182, some 2182, some 2181, some 2185, some 2186, some 2187],
      [some 1908, some 2185, some 2186, some 2191, some 2191, some 2186, some 2180, some 2195, some 2182, some 2182, some 2195, some 2187, some 1908, some 2191, some 2186, some 2187],
      [some 1908, some 2186, some 2186, some 1908, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478, some 610],
      [some 610, some 478, some 2630, some 487, some 2632, some 2632, some 487, some 1437, some 2354, some 1569, some 1569, some 2354, some 2873, some 1998, some 1998, some 478],
      [some 1866, some 1908, some 1866, some 1908, some 1998, some 478, some 2630, some 2895, some 2632, some 2632, some 2895, some 1866, some 1908, some 2907, some 2214, some 1866],
      [some 1908, some 2214, some 2214, some 1908, some 7, some 49, some 139, some 139, some 49, some 436, some 478, some 568, some 610, some 436, some 478, some 610],
      [some 610, some 478, some 1437, some 2354, some 1569, some 1569, some 2354, some 1866, some 1908, some 1998, some 478, some 1866, some 1908, some 2214, some 2214, some 1908],
      [some 1437, some 2354, some 1569, some 1569, some 2354, some 1998, some 478, some 2214, some 1908, some 1998, some 478, some 1908, some 1908, some 478]
    ]

/-- The n = 10 row data reconstruct exactly the normalized label certificate. -/
theorem rows_ten_reconstruct_labels :
    labelsFromRows rowsTen = some A198683Schoenfield.labelsTen := by
  native_decide

/-- Row-level Schoenfield table certificate for `A198683(10) = 462`. -/
theorem schoenfield_rows_a198683_ten :
    rowCertificateOk rowsTen 4862 462 = true := by
  native_decide

end A198683SchoenfieldRows

end LeanProofs
