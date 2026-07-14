import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof003.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof003.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof003.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof003.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append003 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids003_parts :
    explicitMids003Part0 ++
      (explicitMids003Part1 ++
        (explicitMids003Part2 ++ explicitMids003Part3)) =
      explicitMids003 := by
  decide

theorem explicitMidLengths003 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids003 := by
  have h := explicitAll_append003 explicitMidLengths003Part0
    (explicitAll_append003 explicitMidLengths003Part1
      (explicitAll_append003 explicitMidLengths003Part2
        explicitMidLengths003Part3))
  rw [explicitMids003_parts] at h
  exact h

theorem explicitClosed003 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids003 := by
  have h := explicitAll_append003 explicitClosed003Part0
    (explicitAll_append003 explicitClosed003Part1
      (explicitAll_append003 explicitClosed003Part2
        explicitClosed003Part3))
  rw [explicitMids003_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
