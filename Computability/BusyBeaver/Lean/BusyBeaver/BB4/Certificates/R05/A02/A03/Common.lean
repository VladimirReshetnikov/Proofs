import BusyBeaver.BB4.Certificates.R05.A02.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

/-- The fresh `D,0` transition reached after the `a05, a02, a03` prefix. -/
def fourthBranchA02A03 (fourth : GoAction) : Bool :=
  TNF.checkFrom leaf 103
    (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) fourth)
    ((((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
      a02.next false a03).set a03.next false fourth)
    (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) fourth)

end SetTheory.BusyBeaver.BB4.Certificates
