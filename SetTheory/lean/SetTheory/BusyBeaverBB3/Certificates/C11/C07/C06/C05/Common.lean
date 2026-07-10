import SetTheory.BusyBeaverBB3.Certificates.Common

namespace SetTheory.BusyBeaver.BB3.Certificates

def fifthBranch_a11_a07_a06_a05 (fifth : GoAction) : Bool :=
  checkFrom NGram.leaf 13
    (((((PTable.empty.set (0 : Fin 3) false a11).set a11.next false a07).set
      a07.next true a06).set a11.next true a05).set a07.next false fifth)
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo
                (stepGo (stepGo (initial 3) a11) a07)
                a06)
              a11)
            a05)
          a05)
        a07)
      fifth)

end SetTheory.BusyBeaver.BB3.Certificates

