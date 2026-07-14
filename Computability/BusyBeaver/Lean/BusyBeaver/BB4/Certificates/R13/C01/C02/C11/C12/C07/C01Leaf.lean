import BusyBeaver.BB4.Certificates.R13.AssignedReplay

namespace SetTheory.BusyBeaver.BB4.Certificates

def table_a13_a01_a02_a11_a12_a07_a01 : PTable :=
  (((((((PTable.empty.set (0 : Fin 4) false a13).set
    (1 : Fin 4) false a01).set (1 : Fin 4) true a02).set
    (2 : Fin 4) false a11).set (3 : Fin 4) false a12).set
    (0 : Fin 4) true a07).set (2 : Fin 4) true a01)

def start_a13_a01_a02_a11_a12_a07_a01 : Config 4 :=
  stepGo
    (stepGo
      (stepGo
        (stepGo
          (stepGo
            (stepGo
              (stepGo
                (stepGo
                  (stepGo
                    (stepGo (stepGo (initial 4) a13) a01)
                    a02)
                  a11)
                a12)
              a07)
            a12)
          a13)
        a01)
      a02)
    a01

def endpoint_a13_a01_a02_a11_a12_a07_a01 : Config 4 :=
  (runAssigned? 96 table_a13_a01_a02_a11_a12_a07_a01
    start_a13_a01_a02_a11_a12_a07_a01).getD
      start_a13_a01_a02_a11_a12_a07_a01

set_option maxRecDepth 10000 in
theorem replay_a13_a01_a02_a11_a12_a07_a01 :
    runAssigned? 96 table_a13_a01_a02_a11_a12_a07_a01
      start_a13_a01_a02_a11_a12_a07_a01 =
        some endpoint_a13_a01_a02_a11_a12_a07_a01 := by
  decide

theorem endpoint_state_a13_a01_a02_a11_a12_a07_a01 :
    endpoint_a13_a01_a02_a11_a12_a07_a01.state = some (0 : Fin 4) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem history_a13_a01_a02_a11_a12_a07_a01 :
    (NGram.Pass.history 2 2 1600).check
      table_a13_a01_a02_a11_a12_a07_a01 = true := by
  decide

theorem nGramLeaf_a13_a01_a02_a11_a12_a07_a01 (cfg : Config 4) :
    NGram.nGramLeaf table_a13_a01_a02_a11_a12_a07_a01 cfg = true := by
  change NGram.runPasses table_a13_a01_a02_a11_a12_a07_a01 NGram.passes = true
  simp only [NGram.passes, NGram.runPasses]
  rw [history_a13_a01_a02_a11_a12_a07_a01]
  simp

theorem leaf_a13_a01_a02_a11_a12_a07_a01 (cfg : Config 4) :
    leaf table_a13_a01_a02_a11_a12_a07_a01 cfg = true := by
  unfold leaf
  rw [nGramLeaf_a13_a01_a02_a11_a12_a07_a01]
  simp

end SetTheory.BusyBeaver.BB4.Certificates
