import BusyBeaver.BB4.Certificates.R05.A02.A07.A13.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A07A13A10 : PTable :=
  fourthTableA02A07A13.set a02.next true a10
def beforeSixthA02A07A13A10 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a13) a02) a10) a07
def sixthBranchA02A07A13A10 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
          a13)
        a10)
      sixth)
    (fifthTableA02A07A13A10.set a07.next true sixth)
    (stepGo beforeSixthA02A07A13A10 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
