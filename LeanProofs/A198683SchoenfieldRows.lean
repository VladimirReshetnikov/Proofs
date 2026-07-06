import LeanProofs.A198683Schoenfield

/-!
# Row-level Schoenfield certificate for OEIS A198683 at n = 7

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

end A198683SchoenfieldRows

end LeanProofs
