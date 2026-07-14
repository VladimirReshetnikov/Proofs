import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a11_a04_a11 : Guided.Work :=
  after [a09, a11, a04, a11]

def certificate_a09_a11_a04_a11 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a11_a04_a11 :
    work_a09_a11_a04_a11.check certificate_a09_a11_a04_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
