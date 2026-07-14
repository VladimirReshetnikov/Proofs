import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def thirdBranch_a13_a06 (third : GoAction) : Bool :=
  TNF.checkFrom leaf 104
    (TNF.grow (TNF.grow (TNF.grow 1 a13) a06) third)
    (((PTable.empty.set (0 : Fin 4) false a13).set a13.next false a06).set
      a06.next false third)
    (stepGo (stepGo (stepGo (initial 4) a13) a06) third)

end SetTheory.BusyBeaver.BB4.Certificates
