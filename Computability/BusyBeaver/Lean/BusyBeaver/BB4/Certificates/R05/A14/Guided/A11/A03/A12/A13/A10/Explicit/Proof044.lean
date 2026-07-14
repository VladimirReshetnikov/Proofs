import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof044.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof044.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof044.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof044.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append044 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids044_parts :
    explicitMids044Part0 ++
      (explicitMids044Part1 ++
        (explicitMids044Part2 ++ explicitMids044Part3)) =
      explicitMids044 := by
  decide

theorem explicitMidLengths044 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids044 := by
  have h := explicitAll_append044 explicitMidLengths044Part0
    (explicitAll_append044 explicitMidLengths044Part1
      (explicitAll_append044 explicitMidLengths044Part2
        explicitMidLengths044Part3))
  rw [explicitMids044_parts] at h
  exact h

theorem explicitClosed044 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids044 := by
  have h := explicitAll_append044 explicitClosed044Part0
    (explicitAll_append044 explicitClosed044Part1
      (explicitAll_append044 explicitClosed044Part2
        explicitClosed044Part3))
  rw [explicitMids044_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
