import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a08_a10_a04_a06 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 15
    (((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a10).set
      a10.next true a04).set a04.next false a06).set a08.next true fifth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo (stepGo (initial 3) a08) a10) a04)
          a06)
        a08)
      fifth)

end SetTheory.BusyBeaver.BB3.Certificates
