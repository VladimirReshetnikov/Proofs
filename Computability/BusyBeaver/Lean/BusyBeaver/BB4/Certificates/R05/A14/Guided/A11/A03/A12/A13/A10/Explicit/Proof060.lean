import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof060.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof060.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof060.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof060.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append060 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids060_parts :
    explicitMids060Part0 ++
      (explicitMids060Part1 ++
        (explicitMids060Part2 ++ explicitMids060Part3)) =
      explicitMids060 := by
  decide

theorem explicitMidLengths060 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids060 := by
  have h := explicitAll_append060 explicitMidLengths060Part0
    (explicitAll_append060 explicitMidLengths060Part1
      (explicitAll_append060 explicitMidLengths060Part2
        explicitMidLengths060Part3))
  rw [explicitMids060_parts] at h
  exact h

theorem explicitClosed060 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids060 := by
  have h := explicitAll_append060 explicitClosed060Part0
    (explicitAll_append060 explicitClosed060Part1
      (explicitAll_append060 explicitClosed060Part2
        explicitClosed060Part3))
  rw [explicitMids060_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
