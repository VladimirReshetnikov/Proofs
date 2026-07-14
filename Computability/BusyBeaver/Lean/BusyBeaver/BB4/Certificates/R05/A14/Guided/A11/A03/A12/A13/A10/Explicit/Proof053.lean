import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof053.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof053.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof053.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof053.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append053 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids053_parts :
    explicitMids053Part0 ++
      (explicitMids053Part1 ++
        (explicitMids053Part2 ++ explicitMids053Part3)) =
      explicitMids053 := by
  decide

theorem explicitMidLengths053 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids053 := by
  have h := explicitAll_append053 explicitMidLengths053Part0
    (explicitAll_append053 explicitMidLengths053Part1
      (explicitAll_append053 explicitMidLengths053Part2
        explicitMidLengths053Part3))
  rw [explicitMids053_parts] at h
  exact h

theorem explicitClosed053 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids053 := by
  have h := explicitAll_append053 explicitClosed053Part0
    (explicitAll_append053 explicitClosed053Part1
      (explicitAll_append053 explicitClosed053Part2
        explicitClosed053Part3))
  rw [explicitMids053_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
