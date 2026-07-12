import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a07_a11_a05 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a07).set a07.next false a11).set
      a11.next true a05).set a05.next false fourth)
    (stepGo (stepGo (stepGo (stepGo (initial 3) a07) a11) a05) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
