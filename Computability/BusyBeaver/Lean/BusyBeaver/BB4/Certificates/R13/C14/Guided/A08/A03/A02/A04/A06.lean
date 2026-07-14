import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a03_a02_a04_a06 : Guided.Work :=
  after [a08, a03, a02, a04, a06]

def certificate_a08_a03_a02_a04_a06 : Guided.Certificate :=
  Guided.Certificate.history4x3

set_option maxHeartbeats 1600000 in
theorem verified_a08_a03_a02_a04_a06 :
    work_a08_a03_a02_a04_a06.check certificate_a08_a03_a02_a04_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
