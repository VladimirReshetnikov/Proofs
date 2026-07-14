import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a15_a08_a08_a04 : Guided.Work :=
  after [a15, a08, a08, a04]

def certificate_a15_a08_a08_a04 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a15_a08_a08_a04 :
    work_a15_a08_a08_a04.check certificate_a15_a08_a08_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
