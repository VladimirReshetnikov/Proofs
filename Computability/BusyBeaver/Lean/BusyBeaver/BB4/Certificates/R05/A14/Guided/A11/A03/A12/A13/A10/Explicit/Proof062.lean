import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof062.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof062.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof062.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof062.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append062 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids062_parts :
    explicitMids062Part0 ++
      (explicitMids062Part1 ++
        (explicitMids062Part2 ++ explicitMids062Part3)) =
      explicitMids062 := by
  decide

theorem explicitMidLengths062 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids062 := by
  have h := explicitAll_append062 explicitMidLengths062Part0
    (explicitAll_append062 explicitMidLengths062Part1
      (explicitAll_append062 explicitMidLengths062Part2
        explicitMidLengths062Part3))
  rw [explicitMids062_parts] at h
  exact h

theorem explicitClosed062 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids062 := by
  have h := explicitAll_append062 explicitClosed062Part0
    (explicitAll_append062 explicitClosed062Part1
      (explicitAll_append062 explicitClosed062Part2
        explicitClosed062Part3))
  rw [explicitMids062_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
