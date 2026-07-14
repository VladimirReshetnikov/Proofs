import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A03A13A12 : PTable :=
  fourthTableA02A03A13.set a02.next true a12
def beforeSixthA02A03A13A12 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a13) a02) a12) a05) a02) a03
def sixthBranchA02A03A13A12 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 97
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a13)
        a12)
      sixth)
    (fifthTableA02A03A13A12.set a03.next true sixth)
    (stepGo beforeSixthA02A03A13A12 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
