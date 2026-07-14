import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A03A12A13 : PTable :=
  fourthTableA02A03A12.set a03.next true a13
def beforeSixthA02A03A12A13 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a12) a05) a02) a03) a13) a02
def sixthBranchA02A03A12A13 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 97
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a12)
        a13)
      sixth)
    (fifthTableA02A03A12A13.set a02.next true sixth)
    (stepGo beforeSixthA02A03A12A13 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
