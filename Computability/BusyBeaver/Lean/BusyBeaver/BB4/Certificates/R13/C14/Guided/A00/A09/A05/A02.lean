import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a00_a09_a05_a02 : Guided.Work :=
  after [a00, a09, a05, a02]

def certificate_a00_a09_a05_a02 : Guided.Certificate :=
  Guided.Certificate.bool1

theorem verified_a00_a09_a05_a02 :
    work_a00_a09_a05_a02.check certificate_a00_a09_a05_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
