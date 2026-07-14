import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof034.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof034.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof034.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof034.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append034 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids034_parts :
    explicitMids034Part0 ++
      (explicitMids034Part1 ++
        (explicitMids034Part2 ++ explicitMids034Part3)) =
      explicitMids034 := by
  decide

theorem explicitMidLengths034 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids034 := by
  have h := explicitAll_append034 explicitMidLengths034Part0
    (explicitAll_append034 explicitMidLengths034Part1
      (explicitAll_append034 explicitMidLengths034Part2
        explicitMidLengths034Part3))
  rw [explicitMids034_parts] at h
  exact h

theorem explicitClosed034 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids034 := by
  have h := explicitAll_append034 explicitClosed034Part0
    (explicitAll_append034 explicitClosed034Part1
      (explicitAll_append034 explicitClosed034Part2
        explicitClosed034Part3))
  rw [explicitMids034_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
