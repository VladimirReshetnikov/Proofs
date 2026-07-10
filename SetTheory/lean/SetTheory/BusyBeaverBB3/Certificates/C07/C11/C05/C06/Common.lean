import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a07_a11_a05_a06 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 15
    (((((PTable.empty.set (0 : Fin 3) false a07).set a07.next false a11).set
      a11.next true a05).set a05.next false a06).set a07.next true fifth)
    (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 3) a07) a11) a05) a06) a07) fifth)

end SetTheory.BusyBeaver.BB3.Certificates
