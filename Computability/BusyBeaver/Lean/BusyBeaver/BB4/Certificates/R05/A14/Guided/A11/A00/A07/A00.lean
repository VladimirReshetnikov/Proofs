import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a11_a00_a07_a00 : Guided.Work :=
  after [a11, a00, a07, a00]

def certificate_a11_a00_a07_a00 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a11_a00_a07_a00 :
    work_a11_a00_a07_a00.check certificate_a11_a00_a07_a00 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
