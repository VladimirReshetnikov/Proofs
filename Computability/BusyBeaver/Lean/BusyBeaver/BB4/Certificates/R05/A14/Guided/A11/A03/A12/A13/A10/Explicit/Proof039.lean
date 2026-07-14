import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof039.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof039.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof039.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof039.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append039 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids039_parts :
    explicitMids039Part0 ++
      (explicitMids039Part1 ++
        (explicitMids039Part2 ++ explicitMids039Part3)) =
      explicitMids039 := by
  decide

theorem explicitMidLengths039 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids039 := by
  have h := explicitAll_append039 explicitMidLengths039Part0
    (explicitAll_append039 explicitMidLengths039Part1
      (explicitAll_append039 explicitMidLengths039Part2
        explicitMidLengths039Part3))
  rw [explicitMids039_parts] at h
  exact h

theorem explicitClosed039 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids039 := by
  have h := explicitAll_append039 explicitClosed039Part0
    (explicitAll_append039 explicitClosed039Part1
      (explicitAll_append039 explicitClosed039Part2
        explicitClosed039Part3))
  rw [explicitMids039_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
