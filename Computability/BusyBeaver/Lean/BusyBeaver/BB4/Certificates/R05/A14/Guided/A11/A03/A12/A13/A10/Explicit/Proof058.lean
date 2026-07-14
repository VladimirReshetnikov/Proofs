import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof058.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof058.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof058.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof058.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append058 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids058_parts :
    explicitMids058Part0 ++
      (explicitMids058Part1 ++
        (explicitMids058Part2 ++ explicitMids058Part3)) =
      explicitMids058 := by
  decide

theorem explicitMidLengths058 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids058 := by
  have h := explicitAll_append058 explicitMidLengths058Part0
    (explicitAll_append058 explicitMidLengths058Part1
      (explicitAll_append058 explicitMidLengths058Part2
        explicitMidLengths058Part3))
  rw [explicitMids058_parts] at h
  exact h

theorem explicitClosed058 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids058 := by
  have h := explicitAll_append058 explicitClosed058Part0
    (explicitAll_append058 explicitClosed058Part1
      (explicitAll_append058 explicitClosed058Part2
        explicitClosed058Part3))
  rw [explicitMids058_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
