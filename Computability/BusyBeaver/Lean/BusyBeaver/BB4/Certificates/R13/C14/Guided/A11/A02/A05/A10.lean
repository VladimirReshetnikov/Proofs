import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a02_a05_a10 : Guided.Work :=
  after [a11, a02, a05, a10]

def certificate_a11_a02_a05_a10 : Guided.Certificate :=
  Guided.Certificate.history2x3

set_option maxHeartbeats 1600000 in
theorem verified_a11_a02_a05_a10 :
    work_a11_a02_a05_a10.check certificate_a11_a02_a05_a10 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
