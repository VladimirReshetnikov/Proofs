import BusyBeaver.BB4.Certificates.R05.A02.A03.A08.Common

namespace SetTheory.BusyBeaver.BB4.Certificates

def fifthTableA02A03A08A15 : PTable :=
  ((((PTable.empty.set (0 : Fin 4) false a05).set a05.next false a02).set
    a02.next false a03).set a03.next false a08).set a05.next true a15

def beforeSixthA02A03A08A15 : Config 4 :=
  stepGo
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo (initial 4) a05) a02) a03) a08) a05) a15)
      a08

/-- The fresh `A,1` transition after the `a15` fifth action and known `D,0`. -/
def sixthBranchA02A03A08A15 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a08)
        a15)
      sixth)
    (fifthTableA02A03A08A15.set (0 : Fin 4) true sixth)
    (stepGo beforeSixthA02A03A08A15 sixth)

end SetTheory.BusyBeaver.BB4.Certificates
