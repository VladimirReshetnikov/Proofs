import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom0
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom1
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom2
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom3
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom4
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom5
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom6
import BusyBeaver.BB4.Certificates.R05.A14.Guided.A11.A03.A12.A13.A10.Explicit.Proof063.Part1.Atom7

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open BB3

def explicitMids063Part1 : List (NGram.MidWord NGram.HistorySymbol) :=
  (explicitMids063.drop 8).take 8

theorem explicitAll_append063Part1 {P : alpha -> Prop} {left right : List alpha}
    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :
    NGramCPS.All P (left ++ right) := by
  induction left with
  | nil => exact hRight
  | cons head tail ih =>
      exact And.intro hLeft.1 (ih hLeft.2)

theorem explicitMids063Part1_atoms :
    explicitMids063Part1Atom0 ++ (explicitMids063Part1Atom1 ++ (explicitMids063Part1Atom2 ++ (explicitMids063Part1Atom3 ++ (explicitMids063Part1Atom4 ++ (explicitMids063Part1Atom5 ++ (explicitMids063Part1Atom6 ++ (explicitMids063Part1Atom7))))))) =
      explicitMids063Part1 := by
  decide

theorem explicitMidLengths063Part1 :
    NGramCPS.All (fun mid => mid.left.length = 2 /\ mid.right.length = 2)
      explicitMids063Part1 := by
  have h := explicitAll_append063Part1 explicitMidLengths063Part1Atom0 (explicitAll_append063Part1 explicitMidLengths063Part1Atom1 (explicitAll_append063Part1 explicitMidLengths063Part1Atom2 (explicitAll_append063Part1 explicitMidLengths063Part1Atom3 (explicitAll_append063Part1 explicitMidLengths063Part1Atom4 (explicitAll_append063Part1 explicitMidLengths063Part1Atom5 (explicitAll_append063Part1 explicitMidLengths063Part1Atom6 (explicitMidLengths063Part1Atom7)))))))
  rw [explicitMids063Part1_atoms] at h
  exact h

theorem explicitClosed063Part1 :
    NGramCPS.All
      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)
        2 2 explicitBlank explicitCertificate)
      explicitMids063Part1 := by
  have h := explicitAll_append063Part1 explicitClosed063Part1Atom0 (explicitAll_append063Part1 explicitClosed063Part1Atom1 (explicitAll_append063Part1 explicitClosed063Part1Atom2 (explicitAll_append063Part1 explicitClosed063Part1Atom3 (explicitAll_append063Part1 explicitClosed063Part1Atom4 (explicitAll_append063Part1 explicitClosed063Part1Atom5 (explicitAll_append063Part1 explicitClosed063Part1Atom6 (explicitClosed063Part1Atom7)))))))
  rw [explicitMids063Part1_atoms] at h
  exact h

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
