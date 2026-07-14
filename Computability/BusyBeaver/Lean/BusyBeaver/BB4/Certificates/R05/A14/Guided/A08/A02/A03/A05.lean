import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

set_option maxRecDepth 10000

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided

open Certificates

def work_a08_a02_a03_a05 : Guided.Work :=
  after [a08, a02, a03, a05]

def certificate_a08_a02_a03_a05 : Guided.Certificate :=
  Guided.Certificate.bool2

theorem verified_a08_a02_a03_a05 :
    work_a08_a02_a03_a05.check certificate_a08_a02_a03_a05 = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided
