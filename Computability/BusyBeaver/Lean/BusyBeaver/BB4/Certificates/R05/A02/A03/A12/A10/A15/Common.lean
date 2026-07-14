import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def sixthTableA02A03A12A10A15 : PTable :=
  fifthTableA02A03A12A10.set a05.next true a15
def beforeSeventhA02A03A12A10A15 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a12) a05) a02) a03) a10) a03) a12) a05) a15) a12) a05) a02) a03) a10
def seventhBranchA02A03A12A10A15 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 89
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a12)
          a10)
        a15)
      seventh)
    (sixthTableA02A03A12A10A15.set a02.next true seventh)
    (stepGo beforeSeventhA02A03A12A10A15 seventh)
end SetTheory.BusyBeaver.BB4.Certificates
