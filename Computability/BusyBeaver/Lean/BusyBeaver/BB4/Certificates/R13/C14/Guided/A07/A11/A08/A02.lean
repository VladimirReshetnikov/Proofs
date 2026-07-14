import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided

open Certificates

def work_a07_a11_a08_a02 : Guided.Work :=
  after [a07, a11, a08, a02]

def certificate_a07_a11_a08_a02 : Guided.Certificate :=
  Guided.Certificate.bool3

theorem verified_a07_a11_a08_a02 :
    work_a07_a11_a08_a02.check certificate_a07_a11_a08_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.C14Guided
