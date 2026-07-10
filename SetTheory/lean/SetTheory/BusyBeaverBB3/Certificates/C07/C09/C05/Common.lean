import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a07_a09_a05 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a07).set a07.next false a09).set
      a09.next true a05).set a05.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a07) a09) a05) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
