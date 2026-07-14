import BusyBeaver.BB4.Certificates.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- The fresh `C,0` transition reached after the `a05, a02` prefix. -/
def thirdBranchA02 (third : GoAction) : Bool :=
  TNF.checkFrom leaf 104
    (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) third)
    (((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
      a02.next false third)
    (stepGo (stepGo (stepGo (initial 4) a05) a02) third)

end SetTheory.BusyBeaver.BB4.Certificates
