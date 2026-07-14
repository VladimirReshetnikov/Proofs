import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a05_a10_a06 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a05).set a05.next false a10).set
      a10.next false a06).set a06.next true fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a05) a10) a06) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
