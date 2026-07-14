import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A07A10A13 : PTable :=
  fourthTableA02A07A10.set a07.next true a13
def beforeSixthA02A07A10A13 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a10) a07) a13) a02
def sixthBranchA02A07A10A13 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
          a10)
        a13)
      sixth)
    (fifthTableA02A07A10A13.set a02.next true sixth)
    (stepGo beforeSixthA02A07A10A13 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
