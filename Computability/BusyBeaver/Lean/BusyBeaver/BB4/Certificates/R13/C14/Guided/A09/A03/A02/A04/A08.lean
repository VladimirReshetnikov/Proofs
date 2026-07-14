import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a09_a03_a02_a04_a08 : Guided.Work :=
  after [a09, a03, a02, a04, a08]

def certificate_a09_a03_a02_a04_a08 : Guided.Certificate :=
  Guided.Certificate.history4x3

set_option maxHeartbeats 1600000 in
theorem verified_a09_a03_a02_a04_a08 :
    work_a09_a03_a02_a04_a08.check certificate_a09_a03_a02_a04_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
