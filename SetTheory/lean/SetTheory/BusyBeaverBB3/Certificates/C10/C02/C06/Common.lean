import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a10_a02_a06 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 16
    ((((PTable.empty.set (0 : Fin 3) false a10).set a10.next false a02).set
      a02.next true a06).set a10.next true fourth)
    (stepGo
      (stepGo
        (stepGo (stepGo (stepGo (initial 3) a10) a02) a06) a10)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates
