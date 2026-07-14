import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a08_a15_a13 : Guided.Work :=
  after [a00, a08, a15, a13]

def certificate_a00_a08_a15_a13 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a00_a08_a15_a13 :
    work_a00_a08_a15_a13.check certificate_a00_a08_a15_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
