import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a10_a08_a02_a09 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 15
    (((((PTable.empty.set (0 : Fin 3) false a10).set a10.next false a08).set
      a08.next true a02).set a02.next false a09).set a10.next true fifth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a10) a08)
            a02)
          a09)
        a10)
      fifth)

end SetTheory.BusyBeaver.BB3.Certificates
