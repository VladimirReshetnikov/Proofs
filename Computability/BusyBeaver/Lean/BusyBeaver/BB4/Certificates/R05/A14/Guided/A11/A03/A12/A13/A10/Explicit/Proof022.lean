import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof022.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof022.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof022.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof022.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append022 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids022_parts :
    explicitMids022Part0 ++
      (explicitMids022Part1 ++
        (explicitMids022Part2 ++ explicitMids022Part3)) =
      explicitMids022 := by
  decide

theorem explicitMidLengths022 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids022 := by
  have h := explicitAll_append022 explicitMidLengths022Part0
    (explicitAll_append022 explicitMidLengths022Part1
      (explicitAll_append022 explicitMidLengths022Part2
        explicitMidLengths022Part3))
  rw [explicitMids022_parts] at h
  exact h

theorem explicitClosed022 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids022 := by
  have h := explicitAll_append022 explicitClosed022Part0
    (explicitAll_append022 explicitClosed022Part1
      (explicitAll_append022 explicitClosed022Part2
        explicitClosed022Part3))
  rw [explicitMids022_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
