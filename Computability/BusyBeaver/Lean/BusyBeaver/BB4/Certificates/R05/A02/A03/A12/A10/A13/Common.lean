import BusyBeaver.BB4.Certificates.R05.A02.A03.A12.A10.Common
namespace SetTheory.BusyBeaver.BB4.Certificates
def sixthTableA02A03A12A10A13 : PTable :=
  fifthTableA02A03A12A10.set a05.next true a13
def beforeSeventhA02A03A12A10A13 : Config 4 :=
  stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (stepGo (initial 4) a05) a02) a03) a12) a05) a02) a03) a10) a03) a12) a05) a13) a02
def seventhBranchA02A03A12A10A13 (seventh : GoAction) : Bool :=
  TNF.checkFrom leaf 93
    (TNF.grow
      (TNF.grow
        (TNF.grow
          (TNF.grow (TNF.grow (TNF.grow (TNF.grow 1 a05) a02) a03) a12)
          a10)
        a13)
      seventh)
    (sixthTableA02A03A12A10A13.set a02.next true seventh)
    (stepGo beforeSeventhA02A03A12A10A13 seventh)
end SetTheory.BusyBeaver.BB4.Certificates
