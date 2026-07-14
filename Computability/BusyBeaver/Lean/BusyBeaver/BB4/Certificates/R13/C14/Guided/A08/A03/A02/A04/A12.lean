import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a08_a03_a02_a04_a12 : Guided.Work :=
  after [a08, a03, a02, a04, a12]

def certificate_a08_a03_a02_a04_a12 : Guided.Certificate :=
  Guided.Certificate.history2x2

set_option maxHeartbeats 1600000 in
theorem verified_a08_a03_a02_a04_a12 :
    work_a08_a03_a02_a04_a12.check certificate_a08_a03_a02_a04_a12 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
