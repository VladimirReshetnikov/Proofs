import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof005.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof005.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof005.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof005.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append005 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids005_parts :
    explicitMids005Part0 ++
      (explicitMids005Part1 ++
        (explicitMids005Part2 ++ explicitMids005Part3)) =
      explicitMids005 := by
  decide

theorem explicitMidLengths005 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids005 := by
  have h := explicitAll_append005 explicitMidLengths005Part0
    (explicitAll_append005 explicitMidLengths005Part1
      (explicitAll_append005 explicitMidLengths005Part2
        explicitMidLengths005Part3))
  rw [explicitMids005_parts] at h
  exact h

theorem explicitClosed005 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids005 := by
  have h := explicitAll_append005 explicitClosed005Part0
    (explicitAll_append005 explicitClosed005Part1
      (explicitAll_append005 explicitClosed005Part2
        explicitClosed005Part3))
  rw [explicitMids005_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
