import BusyBeaver.BB4.Certificates.R05.A02.A07.A10.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A07A10A08 : PTable :=
  fourthTableA02A07A10.set a07.next true a08
def beforeSixthA02A07A10A08 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a10) a07) a08) a05
def sixthBranchA02A07A10A08 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
          a10)
        a08)
      sixth)
    (fifthTableA02A07A10A08.set a05.next true sixth)
    (stepGo beforeSixthA02A07A10A08 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
