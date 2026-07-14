import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof004.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof004.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof004.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof004.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append004 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids004_parts :
    explicitMids004Part0 ++
      (explicitMids004Part1 ++
        (explicitMids004Part2 ++ explicitMids004Part3)) =
      explicitMids004 := by
  decide

theorem explicitMidLengths004 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids004 := by
  have h := explicitAll_append004 explicitMidLengths004Part0
    (explicitAll_append004 explicitMidLengths004Part1
      (explicitAll_append004 explicitMidLengths004Part2
        explicitMidLengths004Part3))
  rw [explicitMids004_parts] at h
  exact h

theorem explicitClosed004 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids004 := by
  have h := explicitAll_append004 explicitClosed004Part0
    (explicitAll_append004 explicitClosed004Part1
      (explicitAll_append004 explicitClosed004Part2
        explicitClosed004Part3))
  rw [explicitMids004_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
