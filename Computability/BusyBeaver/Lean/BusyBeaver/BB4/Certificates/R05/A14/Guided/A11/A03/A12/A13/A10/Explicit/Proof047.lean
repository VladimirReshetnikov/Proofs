import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof047.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof047.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof047.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof047.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append047 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids047_parts :
    explicitMids047Part0 ++
      (explicitMids047Part1 ++
        (explicitMids047Part2 ++ explicitMids047Part3)) =
      explicitMids047 := by
  decide

theorem explicitMidLengths047 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids047 := by
  have h := explicitAll_append047 explicitMidLengths047Part0
    (explicitAll_append047 explicitMidLengths047Part1
      (explicitAll_append047 explicitMidLengths047Part2
        explicitMidLengths047Part3))
  rw [explicitMids047_parts] at h
  exact h

theorem explicitClosed047 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids047 := by
  have h := explicitAll_append047 explicitClosed047Part0
    (explicitAll_append047 explicitClosed047Part1
      (explicitAll_append047 explicitClosed047Part2
        explicitClosed047Part3))
  rw [explicitMids047_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
