import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a04_a11_a06 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a04).set a04.next false a11).set
      a11.next false a06).set a06.next true fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a04) a11) a06) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
