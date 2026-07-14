import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof035.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof035.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof035.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof035.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append035 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids035_parts :
    explicitMids035Part0 ++
      (explicitMids035Part1 ++
        (explicitMids035Part2 ++ explicitMids035Part3)) =
      explicitMids035 := by
  decide

theorem explicitMidLengths035 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids035 := by
  have h := explicitAll_append035 explicitMidLengths035Part0
    (explicitAll_append035 explicitMidLengths035Part1
      (explicitAll_append035 explicitMidLengths035Part2
        explicitMidLengths035Part3))
  rw [explicitMids035_parts] at h
  exact h

theorem explicitClosed035 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids035 := by
  have h := explicitAll_append035 explicitClosed035Part0
    (explicitAll_append035 explicitClosed035Part1
      (explicitAll_append035 explicitClosed035Part2
        explicitClosed035Part3))
  rw [explicitMids035_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
