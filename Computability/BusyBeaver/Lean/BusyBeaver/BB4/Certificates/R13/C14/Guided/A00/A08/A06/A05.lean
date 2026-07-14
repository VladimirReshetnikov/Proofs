import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a08_a06_a05 : Guided.Work :=
  after [a00, a08, a06, a05]

def certificate_a00_a08_a06_a05 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a08_a06_a05 :
    work_a00_a08_a06_a05.check certificate_a00_a08_a06_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
