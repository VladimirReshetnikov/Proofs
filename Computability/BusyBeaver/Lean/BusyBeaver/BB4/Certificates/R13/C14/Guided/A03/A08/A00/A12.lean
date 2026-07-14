import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a08_a00_a12 : Guided.Work :=
  after [a03, a08, a00, a12]

def certificate_a03_a08_a00_a12 : Guided.Certificate :=
  Guided.Certificate.history4x2

set_option maxHeartbeats 1600000 in
theorem verified_a03_a08_a00_a12 :
    work_a03_a08_a00_a12.check certificate_a03_a08_a00_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
