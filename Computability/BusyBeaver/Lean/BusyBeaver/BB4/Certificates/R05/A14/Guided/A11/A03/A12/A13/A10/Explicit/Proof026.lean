import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof026.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof026.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof026.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof026.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append026 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids026_parts :
    explicitMids026Part0 ++
      (explicitMids026Part1 ++
        (explicitMids026Part2 ++ explicitMids026Part3)) =
      explicitMids026 := by
  decide

theorem explicitMidLengths026 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids026 := by
  have h := explicitAll_append026 explicitMidLengths026Part0
    (explicitAll_append026 explicitMidLengths026Part1
      (explicitAll_append026 explicitMidLengths026Part2
        explicitMidLengths026Part3))
  rw [explicitMids026_parts] at h
  exact h

theorem explicitClosed026 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids026 := by
  have h := explicitAll_append026 explicitClosed026Part0
    (explicitAll_append026 explicitClosed026Part1
      (explicitAll_append026 explicitClosed026Part2
        explicitClosed026Part3))
  rw [explicitMids026_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
