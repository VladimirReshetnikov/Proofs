import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof016.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof016.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof016.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof016.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append016 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids016_parts :
    explicitMids016Part0 ++
      (explicitMids016Part1 ++
        (explicitMids016Part2 ++ explicitMids016Part3)) =
      explicitMids016 := by
  decide

theorem explicitMidLengths016 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids016 := by
  have h := explicitAll_append016 explicitMidLengths016Part0
    (explicitAll_append016 explicitMidLengths016Part1
      (explicitAll_append016 explicitMidLengths016Part2
        explicitMidLengths016Part3))
  rw [explicitMids016_parts] at h
  exact h

theorem explicitClosed016 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids016 := by
  have h := explicitAll_append016 explicitClosed016Part0
    (explicitAll_append016 explicitClosed016Part1
      (explicitAll_append016 explicitClosed016Part2
        explicitClosed016Part3))
  rw [explicitMids016_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
