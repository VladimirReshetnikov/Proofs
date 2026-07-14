import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof065.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof065.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof065.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof065.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append065 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids065_parts :
    explicitMids065Part0 ++
      (explicitMids065Part1 ++
        (explicitMids065Part2 ++ explicitMids065Part3)) =
      explicitMids065 := by
  decide

theorem explicitMidLengths065 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids065 := by
  have h := explicitAll_append065 explicitMidLengths065Part0
    (explicitAll_append065 explicitMidLengths065Part1
      (explicitAll_append065 explicitMidLengths065Part2
        explicitMidLengths065Part3))
  rw [explicitMids065_parts] at h
  exact h

theorem explicitClosed065 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids065 := by
  have h := explicitAll_append065 explicitClosed065Part0
    (explicitAll_append065 explicitClosed065Part1
      (explicitAll_append065 explicitClosed065Part2
        explicitClosed065Part3))
  rw [explicitMids065_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
