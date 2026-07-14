import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a10_a00_a05_a09 : Guided.Work :=
  after [a11, a10, a00, a05, a09]

def certificate_a11_a10_a00_a05_a09 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a11_a10_a00_a05_a09 :
    work_a11_a10_a00_a05_a09.check certificate_a11_a10_a00_a05_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
