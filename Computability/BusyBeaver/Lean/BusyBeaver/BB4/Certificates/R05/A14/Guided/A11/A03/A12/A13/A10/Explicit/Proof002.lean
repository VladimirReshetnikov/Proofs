import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof002.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof002.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof002.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof002.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append002 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids002_parts :
    explicitMids002Part0 ++
      (explicitMids002Part1 ++
        (explicitMids002Part2 ++ explicitMids002Part3)) =
      explicitMids002 := by
  decide

theorem explicitMidLengths002 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids002 := by
  have h := explicitAll_append002 explicitMidLengths002Part0
    (explicitAll_append002 explicitMidLengths002Part1
      (explicitAll_append002 explicitMidLengths002Part2
        explicitMidLengths002Part3))
  rw [explicitMids002_parts] at h
  exact h

theorem explicitClosed002 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids002 := by
  have h := explicitAll_append002 explicitClosed002Part0
    (explicitAll_append002 explicitClosed002Part1
      (explicitAll_append002 explicitClosed002Part2
        explicitClosed002Part3))
  rw [explicitMids002_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
