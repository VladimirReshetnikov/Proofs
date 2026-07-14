import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a11_a10_a01_a13 : Guided.Work :=
  after [a00, a11, a10, a01, a13]

def certificate_a00_a11_a10_a01_a13 : Guided.Certificate :=
  Guided.Certificate.history2x3

set_option maxHeartbeats 1600000 in
theorem verified_a00_a11_a10_a01_a13 :
    work_a00_a11_a10_a01_a13.check certificate_a00_a11_a10_a01_a13 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
