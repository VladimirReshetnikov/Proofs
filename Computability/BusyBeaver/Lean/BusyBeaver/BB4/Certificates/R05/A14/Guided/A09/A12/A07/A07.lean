import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a12_a07_a07 : Guided.Work :=
  after [a09, a12, a07, a07]

def certificate_a09_a12_a07_a07 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a09_a12_a07_a07 :
    work_a09_a12_a07_a07.check certificate_a09_a12_a07_a07 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
