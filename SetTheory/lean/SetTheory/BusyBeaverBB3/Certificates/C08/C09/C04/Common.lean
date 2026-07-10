import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a08_a09_a04 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a09).set
      a09.next true a04).set a04.next false fourth)
    (stepGo
      (stepGo (stepGo (stepGo (initial 3) a08) a09) a04) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
