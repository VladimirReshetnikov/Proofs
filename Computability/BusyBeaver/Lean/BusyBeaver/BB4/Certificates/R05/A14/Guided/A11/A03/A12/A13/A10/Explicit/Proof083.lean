import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof083.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof083.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof083.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof083.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append083 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids083_parts :
    explicitMids083Part0 ++
      (explicitMids083Part1 ++
        (explicitMids083Part2 ++ explicitMids083Part3)) =
      explicitMids083 := by
  decide

theorem explicitMidLengths083 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids083 := by
  have h := explicitAll_append083 explicitMidLengths083Part0
    (explicitAll_append083 explicitMidLengths083Part1
      (explicitAll_append083 explicitMidLengths083Part2
        explicitMidLengths083Part3))
  rw [explicitMids083_parts] at h
  exact h

theorem explicitClosed083 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids083 := by
  have h := explicitAll_append083 explicitClosed083Part0
    (explicitAll_append083 explicitClosed083Part1
      (explicitAll_append083 explicitClosed083Part2
        explicitClosed083Part3))
  rw [explicitMids083_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
