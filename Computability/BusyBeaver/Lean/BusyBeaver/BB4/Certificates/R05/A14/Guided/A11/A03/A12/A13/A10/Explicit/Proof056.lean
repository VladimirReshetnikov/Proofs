import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof056.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof056.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof056.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof056.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append056 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids056_parts :
    explicitMids056Part0 ++
      (explicitMids056Part1 ++
        (explicitMids056Part2 ++ explicitMids056Part3)) =
      explicitMids056 := by
  decide

theorem explicitMidLengths056 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids056 := by
  have h := explicitAll_append056 explicitMidLengths056Part0
    (explicitAll_append056 explicitMidLengths056Part1
      (explicitAll_append056 explicitMidLengths056Part2
        explicitMidLengths056Part3))
  rw [explicitMids056_parts] at h
  exact h

theorem explicitClosed056 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids056 := by
  have h := explicitAll_append056 explicitClosed056Part0
    (explicitAll_append056 explicitClosed056Part1
      (explicitAll_append056 explicitClosed056Part2
        explicitClosed056Part3))
  rw [explicitMids056_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
