import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof013.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof013.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof013.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof013.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append013 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids013_parts :
    explicitMids013Part0 ++
      (explicitMids013Part1 ++
        (explicitMids013Part2 ++ explicitMids013Part3)) =
      explicitMids013 := by
  decide

theorem explicitMidLengths013 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids013 := by
  have h := explicitAll_append013 explicitMidLengths013Part0
    (explicitAll_append013 explicitMidLengths013Part1
      (explicitAll_append013 explicitMidLengths013Part2
        explicitMidLengths013Part3))
  rw [explicitMids013_parts] at h
  exact h

theorem explicitClosed013 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids013 := by
  have h := explicitAll_append013 explicitClosed013Part0
    (explicitAll_append013 explicitClosed013Part1
      (explicitAll_append013 explicitClosed013Part2
        explicitClosed013Part3))
  rw [explicitMids013_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
