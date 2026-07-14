import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a08_a00_a13_a08 : Guided.Work :=
  after [a11, a08, a00, a13, a08]

def certificate_a11_a08_a00_a13_a08 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a08_a00_a13_a08 :
    work_a11_a08_a00_a13_a08.check certificate_a11_a08_a00_a13_a08 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
