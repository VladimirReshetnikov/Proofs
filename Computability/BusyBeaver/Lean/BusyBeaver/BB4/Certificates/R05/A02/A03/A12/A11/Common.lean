import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A03A12A11 : PTable :=
  fourthTableA02A03A12.set a03.next true a11
def beforeSixthA02A03A12A11 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a12) a05) a02) a03) a11) a12
def sixthBranchA02A03A12A11 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 97
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a12)
        a11)
      sixth)
    (fifthTableA02A03A12A11.set (0 : Fin 4) true sixth)
    (stepGo beforeSixthA02A03A12A11 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
