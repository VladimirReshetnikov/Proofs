import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a00_a07_a07 : Guided.Work :=
  after [a00, a07, a07]

def certificate_a00_a07_a07 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a07_a07 :
    work_a00_a07_a07.check certificate_a00_a07_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
