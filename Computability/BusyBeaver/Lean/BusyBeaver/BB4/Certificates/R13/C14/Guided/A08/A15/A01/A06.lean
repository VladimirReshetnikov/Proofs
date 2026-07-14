import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a15_a01_a06 : Guided.Work :=
  after [a08, a15, a01, a06]

def certificate_a08_a15_a01_a06 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a08_a15_a01_a06 :
    work_a08_a15_a01_a06.check certificate_a08_a15_a01_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
