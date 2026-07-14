import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a02_a06 : Guided.Work :=
  after [a11, a00, a02, a06]

def certificate_a11_a00_a02_a06 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a00_a02_a06 :
    work_a11_a00_a02_a06.check certificate_a11_a00_a02_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
