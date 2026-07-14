import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof042.Part0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof042.Part1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof042.Part2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof042.Part3

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

theorem explicitAll_append042 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids042_parts :
    explicitMids042Part0 ++
      (explicitMids042Part1 ++
        (explicitMids042Part2 ++ explicitMids042Part3)) =
      explicitMids042 := by
  decide

theorem explicitMidLengths042 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids042 := by
  have h := explicitAll_append042 explicitMidLengths042Part0
    (explicitAll_append042 explicitMidLengths042Part1
      (explicitAll_append042 explicitMidLengths042Part2
        explicitMidLengths042Part3))
  rw [explicitMids042_parts] at h
  exact h

theorem explicitClosed042 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids042 := by
  have h := explicitAll_append042 explicitClosed042Part0
    (explicitAll_append042 explicitClosed042Part1
      (explicitAll_append042 explicitClosed042Part2
        explicitClosed042Part3))
  rw [explicitMids042_parts] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
