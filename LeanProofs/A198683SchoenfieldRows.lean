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

end A198683SchoenfieldRows

end LeanProofs
