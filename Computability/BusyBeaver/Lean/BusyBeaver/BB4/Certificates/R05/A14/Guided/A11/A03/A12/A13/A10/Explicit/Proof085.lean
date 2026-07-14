import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof085.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof085.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof085.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof085.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append085 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids085_parts :
    explicitMids085Part0 ++
      (explicitMids085Part1 ++
        (explicitMids085Part2 ++ explicitMids085Part3)) =
      explicitMids085 := by
  decide

theorem explicitMidLengths085 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids085 := by
  have h := explicitAll_append085 explicitMidLengths085Part0
    (explicitAll_append085 explicitMidLengths085Part1
      (explicitAll_append085 explicitMidLengths085Part2
        explicitMidLengths085Part3))
  rw [explicitMids085_parts] at h
  exact h

theorem explicitClosed085 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids085 := by
  have h := explicitAll_append085 explicitClosed085Part0
    (explicitAll_append085 explicitClosed085Part1
      (explicitAll_append085 explicitClosed085Part2
        explicitClosed085Part3))
  rw [explicitMids085_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
