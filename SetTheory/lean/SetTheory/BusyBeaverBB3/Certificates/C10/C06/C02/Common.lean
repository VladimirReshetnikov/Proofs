import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a10_a06_a02 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a10).set a10.next false a06).set
      a06.next true a02).set a02.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a10) a06) a02)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates
