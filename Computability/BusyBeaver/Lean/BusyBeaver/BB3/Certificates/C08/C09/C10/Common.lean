import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a08_a09_a10 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a09).set
      a09.next true a10).set a10.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a08) a09) a10) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
