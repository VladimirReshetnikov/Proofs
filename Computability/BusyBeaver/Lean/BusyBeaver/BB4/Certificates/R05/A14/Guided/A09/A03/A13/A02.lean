import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a09_a03_a13_a02 : Guided.Work :=
  after [a09, a03, a13, a02]

def certificate_a09_a03_a13_a02 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a09_a03_a13_a02 :
    work_a09_a03_a13_a02.check certificate_a09_a03_a13_a02 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
