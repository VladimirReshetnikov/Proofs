import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof019.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof019.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof019.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof019.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append019 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids019_parts :
    explicitMids019Part0 ++
      (explicitMids019Part1 ++
        (explicitMids019Part2 ++ explicitMids019Part3)) =
      explicitMids019 := by
  decide

theorem explicitMidLengths019 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids019 := by
  have h := explicitAll_append019 explicitMidLengths019Part0
    (explicitAll_append019 explicitMidLengths019Part1
      (explicitAll_append019 explicitMidLengths019Part2
        explicitMidLengths019Part3))
  rw [explicitMids019_parts] at h
  exact h

theorem explicitClosed019 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids019 := by
  have h := explicitAll_append019 explicitClosed019Part0
    (explicitAll_append019 explicitClosed019Part1
      (explicitAll_append019 explicitClosed019Part2
        explicitClosed019Part3))
  rw [explicitMids019_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
