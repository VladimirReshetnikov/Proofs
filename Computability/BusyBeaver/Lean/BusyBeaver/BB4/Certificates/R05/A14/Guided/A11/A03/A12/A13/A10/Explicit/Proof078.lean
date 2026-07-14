import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof078.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof078.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof078.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof078.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append078 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids078_parts :
    explicitMids078Part0 ++
      (explicitMids078Part1 ++
        (explicitMids078Part2 ++ explicitMids078Part3)) =
      explicitMids078 := by
  decide

theorem explicitMidLengths078 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids078 := by
  have h := explicitAll_append078 explicitMidLengths078Part0
    (explicitAll_append078 explicitMidLengths078Part1
      (explicitAll_append078 explicitMidLengths078Part2
        explicitMidLengths078Part3))
  rw [explicitMids078_parts] at h
  exact h

theorem explicitClosed078 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids078 := by
  have h := explicitAll_append078 explicitClosed078Part0
    (explicitAll_append078 explicitClosed078Part1
      (explicitAll_append078 explicitClosed078Part2
        explicitClosed078Part3))
  rw [explicitMids078_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
