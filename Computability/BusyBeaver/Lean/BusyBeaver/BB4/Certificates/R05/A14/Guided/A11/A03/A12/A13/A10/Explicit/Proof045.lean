import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof045.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof045.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof045.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof045.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append045 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids045_parts :
    explicitMids045Part0 ++
      (explicitMids045Part1 ++
        (explicitMids045Part2 ++ explicitMids045Part3)) =
      explicitMids045 := by
  decide

theorem explicitMidLengths045 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids045 := by
  have h := explicitAll_append045 explicitMidLengths045Part0
    (explicitAll_append045 explicitMidLengths045Part1
      (explicitAll_append045 explicitMidLengths045Part2
        explicitMidLengths045Part3))
  rw [explicitMids045_parts] at h
  exact h

theorem explicitClosed045 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids045 := by
  have h := explicitAll_append045 explicitClosed045Part0
    (explicitAll_append045 explicitClosed045Part1
      (explicitAll_append045 explicitClosed045Part2
        explicitClosed045Part3))
  rw [explicitMids045_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
