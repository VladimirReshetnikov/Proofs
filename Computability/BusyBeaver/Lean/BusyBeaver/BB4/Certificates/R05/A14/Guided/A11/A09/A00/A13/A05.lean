import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a09_a00_a13_a05 : Guided.Work :=
  after [a11, a09, a00, a13, a05]

def certificate_a11_a09_a00_a13_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a09_a00_a13_a05 :
    work_a11_a09_a00_a13_a05.check certificate_a11_a09_a00_a13_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
