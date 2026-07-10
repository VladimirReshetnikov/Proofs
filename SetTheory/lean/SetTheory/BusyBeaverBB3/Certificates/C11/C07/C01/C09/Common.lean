import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a11_a07_a01_a09 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 15
    (((((PTable.empty.set (0 : Fin 3) false a11).set a11.next false a07).set
      a07.next true a01).set a01.next false a09).set a11.next true fifth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a11) a07) a01)
          a09)
        a11)
      fifth)

end SetTheory.BusyBeaver.BB3.Certificates

