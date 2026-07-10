import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a11_a06_a01 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a11).set a11.next false a06).set
      a06.next true a01).set a01.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a11) a06) a01) fourth)

end SetTheory.BusyBeaver.BB3.Certificates

