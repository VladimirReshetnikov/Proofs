import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a01_a01 : Guided.Work :=
  after [a11, a00, a01, a01]

def certificate_a11_a00_a01_a01 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a11_a00_a01_a01 :
    work_a11_a00_a01_a01.check certificate_a11_a00_a01_a01 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
