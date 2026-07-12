import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a11_a07_a02 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 16
    ((((PTable.empty.set (0 : Fin 3) false a11).set a11.next false a07).set
      a07.next true a02).set a07.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (stepGo (initial 3) a11) a07) a02) a07)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates
