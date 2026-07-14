import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a03_a09_a00_a05 : Guided.Work :=
  after [a03, a09, a00, a05]

def certificate_a03_a09_a00_a05 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a03_a09_a00_a05 :
    work_a03_a09_a00_a05.check certificate_a03_a09_a00_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
