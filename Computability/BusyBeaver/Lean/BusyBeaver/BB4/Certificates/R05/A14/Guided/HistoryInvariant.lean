/- A single guided-search leaf covering the two bespoke R05/A14 invariants. -/

import BusyBeaver.BB4.Certificates.R05.A14.Guided.HistoryInvariantA00
import BusyBeaver.BB4.Certificates.R05.A14.Guided.HistoryInvariantA09

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariant

def leaf (table : PTable) (cfg : Config 4) : Bool :=
  R05A14HistoryInvariantA00.leaf table cfg ||
    R05A14HistoryInvariantA09.leaf table cfg

theorem leaf_sound : LeafSound leaf := by
  intro table cfg machine hAgree hCheck steps
  rcases Bool.or_eq_true_iff.mp hCheck with hA00 | hA09
  · exact R05A14HistoryInvariantA00.leaf_sound table cfg machine
      hAgree hA00 steps
  · exact R05A14HistoryInvariantA09.leaf_sound table cfg machine
      hAgree hA09 steps

end SetTheory.BusyBeaver.BB4.Certificates.R05A14HistoryInvariant
