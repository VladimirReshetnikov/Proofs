import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def thirdBranch_a13_a01 (third : GoAction) : Bool :=
  TNF.checkFrom leaf 104
    (TNF.grow (TNF.grow (TNF.grow 1 a13) a01) third)
    (((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a01).set
      a01.next true third)
    (stepGo (stepGo (stepGo (initial 4) a13) a01) third)

end SetTheory.BusyBeaver.BB4.Certificates
