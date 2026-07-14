import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom3
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom4
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom5
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom6
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof028.Part1.Atom7

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

def explicitMids028Part1 : List (NGram.MidWord NGram.HistorySymbol) :=
  (explicitMids028.drop 8).take 8

theorem explicitAll_append028Part1 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids028Part1_atoms :
    explicitMids028Part1Atom0 ++ (explicitMids028Part1Atom1 ++ (explicitMids028Part1Atom2 ++ (explicitMids028Part1Atom3 ++ (explicitMids028Part1Atom4 ++ (explicitMids028Part1Atom5 ++ (explicitMids028Part1Atom6 ++ (explicitMids028Part1Atom7))))))) =
      explicitMids028Part1 := by
  decide

theorem explicitMidLengths028Part1 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids028Part1 := by
  have h := explicitAll_append028Part1 explicitMidLengths028Part1Atom0 (explicitAll_append028Part1 explicitMidLengths028Part1Atom1 (explicitAll_append028Part1 explicitMidLengths028Part1Atom2 (explicitAll_append028Part1 explicitMidLengths028Part1Atom3 (explicitAll_append028Part1 explicitMidLengths028Part1Atom4 (explicitAll_append028Part1 explicitMidLengths028Part1Atom5 (explicitAll_append028Part1 explicitMidLengths028Part1Atom6 (explicitMidLengths028Part1Atom7)))))))
  rw [explicitMids028Part1_atoms] at h
  exact h

theorem explicitClosed028Part1 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids028Part1 := by
  have h := explicitAll_append028Part1 explicitClosed028Part1Atom0 (explicitAll_append028Part1 explicitClosed028Part1Atom1 (explicitAll_append028Part1 explicitClosed028Part1Atom2 (explicitAll_append028Part1 explicitClosed028Part1Atom3 (explicitAll_append028Part1 explicitClosed028Part1Atom4 (explicitAll_append028Part1 explicitClosed028Part1Atom5 (explicitAll_append028Part1 explicitClosed028Part1Atom6 (explicitClosed028Part1Atom7)))))))
  rw [explicitMids028Part1_atoms] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
