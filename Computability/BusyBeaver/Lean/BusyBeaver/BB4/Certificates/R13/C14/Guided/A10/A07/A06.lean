import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a10_a07_a06 : Guided.Work :=
  after [a10, a07, a06]

def certificate_a10_a07_a06 : Guided.Certificate :=
  Guided.Certificate.history2x3

set_option maxHeartbeats 1600000 in
theorem verified_a10_a07_a06 :
    work_a10_a07_a06.check certificate_a10_a07_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
