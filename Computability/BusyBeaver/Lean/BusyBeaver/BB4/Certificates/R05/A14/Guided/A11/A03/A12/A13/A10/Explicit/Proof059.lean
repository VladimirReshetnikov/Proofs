import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof059.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof059.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof059.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof059.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append059 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids059_parts :
    explicitMids059Part0 ++
      (explicitMids059Part1 ++
        (explicitMids059Part2 ++ explicitMids059Part3)) =
      explicitMids059 := by
  decide

theorem explicitMidLengths059 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids059 := by
  have h := explicitAll_append059 explicitMidLengths059Part0
    (explicitAll_append059 explicitMidLengths059Part1
      (explicitAll_append059 explicitMidLengths059Part2
        explicitMidLengths059Part3))
  rw [explicitMids059_parts] at h
  exact h

theorem explicitClosed059 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids059 := by
  have h := explicitAll_append059 explicitClosed059Part0
    (explicitAll_append059 explicitClosed059Part1
      (explicitAll_append059 explicitClosed059Part2
        explicitClosed059Part3))
  rw [explicitMids059_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
