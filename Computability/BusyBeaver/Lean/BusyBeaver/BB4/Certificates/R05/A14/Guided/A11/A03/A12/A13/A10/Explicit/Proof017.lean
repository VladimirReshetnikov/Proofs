import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof017.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof017.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof017.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof017.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append017 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids017_parts :
    explicitMids017Part0 ++
      (explicitMids017Part1 ++
        (explicitMids017Part2 ++ explicitMids017Part3)) =
      explicitMids017 := by
  decide

theorem explicitMidLengths017 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids017 := by
  have h := explicitAll_append017 explicitMidLengths017Part0
    (explicitAll_append017 explicitMidLengths017Part1
      (explicitAll_append017 explicitMidLengths017Part2
        explicitMidLengths017Part3))
  rw [explicitMids017_parts] at h
  exact h

theorem explicitClosed017 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids017 := by
  have h := explicitAll_append017 explicitClosed017Part0
    (explicitAll_append017 explicitClosed017Part1
      (explicitAll_append017 explicitClosed017Part2
        explicitClosed017Part3))
  rw [explicitMids017_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
