import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof036.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof036.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof036.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof036.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append036 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids036_parts :
    explicitMids036Part0 ++
      (explicitMids036Part1 ++
        (explicitMids036Part2 ++ explicitMids036Part3)) =
      explicitMids036 := by
  decide

theorem explicitMidLengths036 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids036 := by
  have h := explicitAll_append036 explicitMidLengths036Part0
    (explicitAll_append036 explicitMidLengths036Part1
      (explicitAll_append036 explicitMidLengths036Part2
        explicitMidLengths036Part3))
  rw [explicitMids036_parts] at h
  exact h

theorem explicitClosed036 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids036 := by
  have h := explicitAll_append036 explicitClosed036Part0
    (explicitAll_append036 explicitClosed036Part1
      (explicitAll_append036 explicitClosed036Part2
        explicitClosed036Part3))
  rw [explicitMids036_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
