import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof055.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof055.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof055.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof055.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append055 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids055_parts :
    explicitMids055Part0 ++
      (explicitMids055Part1 ++
        (explicitMids055Part2 ++ explicitMids055Part3)) =
      explicitMids055 := by
  decide

theorem explicitMidLengths055 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids055 := by
  have h := explicitAll_append055 explicitMidLengths055Part0
    (explicitAll_append055 explicitMidLengths055Part1
      (explicitAll_append055 explicitMidLengths055Part2
        explicitMidLengths055Part3))
  rw [explicitMids055_parts] at h
  exact h

theorem explicitClosed055 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids055 := by
  have h := explicitAll_append055 explicitClosed055Part0
    (explicitAll_append055 explicitClosed055Part1
      (explicitAll_append055 explicitClosed055Part2
        explicitClosed055Part3))
  rw [explicitMids055_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
