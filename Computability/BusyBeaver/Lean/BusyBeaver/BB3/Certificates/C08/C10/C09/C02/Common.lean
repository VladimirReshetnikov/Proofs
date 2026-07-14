import BusyBeaver.BB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a08_a10_a09_a02 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 13
    (((((PTable.empty.set (0 : Fin 3) false a08).set a08.next false a10).set
      a10.next true a09).set a08.next true a02).set a10.next false fifth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo
                (stepGo (stepGo (initial 3) a08) a10)
                a09)
              a08)
            a02)
          a02)
        a10)
      fifth)

end SetTheory.BusyBeaver.BB3.Certificates
