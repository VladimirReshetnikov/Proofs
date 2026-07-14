import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a08_a05_a00 : Guided.Work :=
  after [a03, a08, a05, a00]

def certificate_a03_a08_a05_a00 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a03_a08_a05_a00 :
    work_a03_a08_a05_a00.check certificate_a03_a08_a05_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
