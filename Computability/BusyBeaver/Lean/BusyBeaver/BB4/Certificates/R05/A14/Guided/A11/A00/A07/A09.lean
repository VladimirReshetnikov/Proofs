import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a07_a09 : Guided.Work :=
  after [a11, a00, a07, a09]

def certificate_a11_a00_a07_a09 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a00_a07_a09 :
    work_a11_a00_a07_a09.check certificate_a11_a00_a07_a09 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
