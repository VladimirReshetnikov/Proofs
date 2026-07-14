import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a11_a00_a14_a07 : Guided.Work :=
  after [a11, a00, a14, a07]

def certificate_a11_a00_a14_a07 : Guided.Certificate :=
  Guided.Certificate.history4x2

set_option maxHeartbeats 1600000 in
theorem verified_a11_a00_a14_a07 :
    work_a11_a00_a14_a07.check certificate_a11_a00_a14_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
