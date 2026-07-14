import BusyBeaver.BB4.Certificates.R05.A02.A03.A13.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A03A13A11 : PTable :=
  fourthTableA02A03A13.set a02.next true a11
def beforeSixthA02A03A13A11 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a13) a02) a11) a13
def sixthBranchA02A03A13A11 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a13)
        a11)
      sixth)
    (fifthTableA02A03A13A11.set a05.next true sixth)
    (stepGo beforeSixthA02A03A13A11 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
