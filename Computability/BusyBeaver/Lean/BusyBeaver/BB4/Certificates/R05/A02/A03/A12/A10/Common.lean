import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A03A12A10 : PTable :=
  fourthTableA02A03A12.set a03.next true a10
def beforeSixthA02A03A12A10 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a12) a05) a02) a03) a10) a03) a12) a05
def sixthBranchA02A03A12A10 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 95
    (TNF.grow
      (TNF.grow
        (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a12)
        a10)
      sixth)
    (fifthTableA02A03A12A10.set a05.next true sixth)
    (stepGo beforeSixthA02A03A12A10 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
