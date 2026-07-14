import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a11_a10_a05_a04 : Guided.Work :=
  after [a08, a11, a10, a05, a04]

def certificate_a08_a11_a10_a05_a04 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a08_a11_a10_a05_a04 :
    work_a08_a11_a10_a05_a04.check certificate_a08_a11_a10_a05_a04 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
