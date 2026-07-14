import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a03_a05_a11 : Guided.Work :=
  after [a00, a03, a05, a11]

def certificate_a00_a03_a05_a11 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a00_a03_a05_a11 :
    work_a00_a03_a05_a11.check certificate_a00_a03_a05_a11 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
