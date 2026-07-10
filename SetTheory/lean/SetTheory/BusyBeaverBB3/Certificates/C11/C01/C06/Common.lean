import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a11_a01_a06 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 16
    ((((PTable.empty.set (0 : Fin 3) false a11).set a11.next false a01).set
      a01.next true a06).set a11.next true fourth)
    (stepGo
      (stepGo
        (stepGo (stepGo (stepGo (initial 3) a11) a01) a06) a11)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates

