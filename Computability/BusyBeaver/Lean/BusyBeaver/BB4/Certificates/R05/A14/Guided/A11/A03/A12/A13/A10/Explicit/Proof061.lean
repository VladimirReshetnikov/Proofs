import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof061.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof061.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof061.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof061.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append061 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids061_parts :
    explicitMids061Part0 ++
      (explicitMids061Part1 ++
        (explicitMids061Part2 ++ explicitMids061Part3)) =
      explicitMids061 := by
  decide

theorem explicitMidLengths061 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids061 := by
  have h := explicitAll_append061 explicitMidLengths061Part0
    (explicitAll_append061 explicitMidLengths061Part1
      (explicitAll_append061 explicitMidLengths061Part2
        explicitMidLengths061Part3))
  rw [explicitMids061_parts] at h
  exact h

theorem explicitClosed061 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids061 := by
  have h := explicitAll_append061 explicitClosed061Part0
    (explicitAll_append061 explicitClosed061Part1
      (explicitAll_append061 explicitClosed061Part2
        explicitClosed061Part3))
  rw [explicitMids061_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
