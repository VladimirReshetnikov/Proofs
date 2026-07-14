import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a07_a11_a02 : Guided.Work :=
  after [a07, a11, a02]

def certificate_a07_a11_a02 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a07_a11_a02 :
    work_a07_a11_a02.check certificate_a07_a11_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
