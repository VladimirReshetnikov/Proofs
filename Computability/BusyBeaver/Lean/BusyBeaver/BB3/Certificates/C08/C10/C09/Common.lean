import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a08_a10_a09 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 16
    ((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a10).set
      a10.next true a09).set a08.next true fourth)
    (stepGo
      (stepGo
        (stepGo (stepGo (stepGo (initial 3) a08) a10) a09) a08)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates
