import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a08_a07_a06 : Guided.Work :=
  after [a00, a08, a07, a06]

def certificate_a00_a08_a07_a06 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a00_a08_a07_a06 :
    work_a00_a08_a07_a06.check certificate_a00_a08_a07_a06 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
