import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof076.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof076.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof076.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof076.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append076 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids076_parts :
    explicitMids076Part0 ++
      (explicitMids076Part1 ++
        (explicitMids076Part2 ++ explicitMids076Part3)) =
      explicitMids076 := by
  decide

theorem explicitMidLengths076 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids076 := by
  have h := explicitAll_append076 explicitMidLengths076Part0
    (explicitAll_append076 explicitMidLengths076Part1
      (explicitAll_append076 explicitMidLengths076Part2
        explicitMidLengths076Part3))
  rw [explicitMids076_parts] at h
  exact h

theorem explicitClosed076 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids076 := by
  have h := explicitAll_append076 explicitClosed076Part0
    (explicitAll_append076 explicitClosed076Part1
      (explicitAll_append076 explicitClosed076Part2
        explicitClosed076Part3))
  rw [explicitMids076_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
