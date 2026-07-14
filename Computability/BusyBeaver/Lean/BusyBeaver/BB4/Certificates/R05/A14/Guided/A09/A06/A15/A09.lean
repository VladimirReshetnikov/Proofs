import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a06_a15_a09 : Guided.Work :=
  after [a09, a06, a15, a09]

def certificate_a09_a06_a15_a09 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a09_a06_a15_a09 :
    work_a09_a06_a15_a09.check certificate_a09_a06_a15_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
