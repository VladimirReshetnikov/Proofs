import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof082.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof082.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof082.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof082.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append082 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids082_parts :
    explicitMids082Part0 ++
      (explicitMids082Part1 ++
        (explicitMids082Part2 ++ explicitMids082Part3)) =
      explicitMids082 := by
  decide

theorem explicitMidLengths082 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids082 := by
  have h := explicitAll_append082 explicitMidLengths082Part0
    (explicitAll_append082 explicitMidLengths082Part1
      (explicitAll_append082 explicitMidLengths082Part2
        explicitMidLengths082Part3))
  rw [explicitMids082_parts] at h
  exact h

theorem explicitClosed082 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids082 := by
  have h := explicitAll_append082 explicitClosed082Part0
    (explicitAll_append082 explicitClosed082Part1
      (explicitAll_append082 explicitClosed082Part2
        explicitClosed082Part3))
  rw [explicitMids082_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
