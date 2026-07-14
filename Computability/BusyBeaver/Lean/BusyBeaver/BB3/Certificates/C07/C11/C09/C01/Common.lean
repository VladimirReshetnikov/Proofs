import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a07_a11_a09_a01 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 13
    (((((PTable.empty.set (0 : Fin 3) false a07).set a07.next false a11).set
      a11.next true a09).set a07.next true a01).set a11.next false fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 3) a07) a11) a09) a07) a01) a01) a11) fifth)

end SetTheory.BusyBeaver.BB3.Certificates
