import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a10_a08_a01 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 16
    ((((PTable.empty.set (0 : Fin 3) false a10).set a10.next false a08).set
      a08.next true a01).set a08.next false fourth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo (stepGo (initial 3) a10) a08)
          a01)
        a08)
      fourth)

end SetTheory.BusyBeaver.BB3.Certificates
