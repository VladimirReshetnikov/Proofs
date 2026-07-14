import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def thirdBranch_a13_a09 (third : GoAction) : Bool :=
  TNF.checkFrom leaf 104
    (TNF.grow (TNF.grow (TNF.grow 1 a13) a09) third)
    (((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a09).set
      a09.next true third)
    (stepGo (stepGo (stepGo (initial 4) a13) a09) third)

end SetTheory.BusyBeaver.BB4.Certificates
