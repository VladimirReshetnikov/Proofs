import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fourthBranch_a08_a10_a04 (fourth : GoAction) : Bool :=
  checkFrom NGram.leaf 17
    ((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a10).set
      a10.next true a04).set a04.next false fourth)
    (stepGo (stepGo (stepGo (stepGo (initial 3) a08) a10) a04) fourth)

end SetTheory.BusyBeaver.BB3.Certificates
