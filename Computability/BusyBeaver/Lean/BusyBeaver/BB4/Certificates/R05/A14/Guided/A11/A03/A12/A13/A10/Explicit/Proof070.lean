import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof070.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof070.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof070.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof070.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append070 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids070_parts :
    explicitMids070Part0 ++
      (explicitMids070Part1 ++
        (explicitMids070Part2 ++ explicitMids070Part3)) =
      explicitMids070 := by
  decide

theorem explicitMidLengths070 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids070 := by
  have h := explicitAll_append070 explicitMidLengths070Part0
    (explicitAll_append070 explicitMidLengths070Part1
      (explicitAll_append070 explicitMidLengths070Part2
        explicitMidLengths070Part3))
  rw [explicitMids070_parts] at h
  exact h

theorem explicitClosed070 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids070 := by
  have h := explicitAll_append070 explicitClosed070Part0
    (explicitAll_append070 explicitClosed070Part1
      (explicitAll_append070 explicitClosed070Part2
        explicitClosed070Part3))
  rw [explicitMids070_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
