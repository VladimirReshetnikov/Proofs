import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a09_a13_a06 : Guided.Work :=
  after [a00, a09, a13, a06]

def certificate_a00_a09_a13_a06 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a09_a13_a06 :
    work_a00_a09_a13_a06.check certificate_a00_a09_a13_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
