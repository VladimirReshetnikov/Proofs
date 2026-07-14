import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof040.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof040.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof040.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof040.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append040 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids040_parts :
    explicitMids040Part0 ++
      (explicitMids040Part1 ++
        (explicitMids040Part2 ++ explicitMids040Part3)) =
      explicitMids040 := by
  decide

theorem explicitMidLengths040 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids040 := by
  have h := explicitAll_append040 explicitMidLengths040Part0
    (explicitAll_append040 explicitMidLengths040Part1
      (explicitAll_append040 explicitMidLengths040Part2
        explicitMidLengths040Part3))
  rw [explicitMids040_parts] at h
  exact h

theorem explicitClosed040 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids040 := by
  have h := explicitAll_append040 explicitClosed040Part0
    (explicitAll_append040 explicitClosed040Part1
      (explicitAll_append040 explicitClosed040Part2
        explicitClosed040Part3))
  rw [explicitMids040_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
