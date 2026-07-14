import BusyBeaver.BB4.Certificates.R05.A02.A07.A08.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def fifthTableA02A07A08A10 : PTable :=
  fourthTableA02A07A08.set a05.next true a10
def beforeSixthA02A07A08A10 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a07) a08) a05) a10) a07
def sixthBranchA02A07A08A10 (sixth : GoAction) : Bool :=
  TNF.checkFrom leaf 99
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a07)
          a08)
        a10)
      sixth)
    (fifthTableA02A07A08A10.set a07.next true sixth)
    (stepGo beforeSixthA02A07A08A10 sixth)
end SetTheory.BusyBeaver.BB4.Certificates
