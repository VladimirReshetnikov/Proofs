import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof069.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof069.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof069.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof069.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append069 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids069_parts :
    explicitMids069Part0 ++
      (explicitMids069Part1 ++
        (explicitMids069Part2 ++ explicitMids069Part3)) =
      explicitMids069 := by
  decide

theorem explicitMidLengths069 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids069 := by
  have h := explicitAll_append069 explicitMidLengths069Part0
    (explicitAll_append069 explicitMidLengths069Part1
      (explicitAll_append069 explicitMidLengths069Part2
        explicitMidLengths069Part3))
  rw [explicitMids069_parts] at h
  exact h

theorem explicitClosed069 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids069 := by
  have h := explicitAll_append069 explicitClosed069Part0
    (explicitAll_append069 explicitClosed069Part1
      (explicitAll_append069 explicitClosed069Part2
        explicitClosed069Part3))
  rw [explicitMids069_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
