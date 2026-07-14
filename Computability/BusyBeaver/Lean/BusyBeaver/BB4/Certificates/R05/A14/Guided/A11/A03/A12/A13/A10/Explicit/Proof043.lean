import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof043.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof043.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof043.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof043.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append043 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids043_parts :
    explicitMids043Part0 ++
      (explicitMids043Part1 ++
        (explicitMids043Part2 ++ explicitMids043Part3)) =
      explicitMids043 := by
  decide

theorem explicitMidLengths043 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids043 := by
  have h := explicitAll_append043 explicitMidLengths043Part0
    (explicitAll_append043 explicitMidLengths043Part1
      (explicitAll_append043 explicitMidLengths043Part2
        explicitMidLengths043Part3))
  rw [explicitMids043_parts] at h
  exact h

theorem explicitClosed043 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids043 := by
  have h := explicitAll_append043 explicitClosed043Part0
    (explicitAll_append043 explicitClosed043Part1
      (explicitAll_append043 explicitClosed043Part2
        explicitClosed043Part3))
  rw [explicitMids043_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
