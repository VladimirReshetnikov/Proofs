/-
  BusyBeaverBB4/Leaf.lean

  Prototype sound leaf pipeline: complete tables, declaratively checked
  Boolean/history n-gram CPS passes, and the two explicit sporadic machines.
-/

import SetTheory.BusyBeaverBB4.NGramBuilder

namespace SetTheory
namespace BusyBeaver
namespace BB4

open BB3

namespace NGram

inductive Pass
  | bool (width gas : Nat)
  | history (depth width gas : Nat)
  deriving DecidableEq, Repr

def Pass.check : Pass -> PTable -> Bool
  | .bool width gas, table => boolCheck table width gas
  | .history depth width gas, table =>
      historyCheck table depth width gas

theorem Pass.check_nonhalts {pass : Pass} {table : PTable}
    (h : pass.check table = true) :
    table.toPTM.Nonhalts (0 : Fin 4) false := by
  cases pass with
  | bool width gas => exact boolCheck_nonhalts h
  | history depth width gas => exact historyCheck_nonhalts h

/-- Parameters mirroring the n-gram stages of the upstream BB4 pipeline. -/
def passes : List Pass :=
  [ .bool 1 100,
    .bool 2 200,
    .bool 3 400,
    .history 2 2 1600,
    .history 2 3 1600,
    .history 4 2 600,
    .history 4 3 1600,
    .history 6 2 3200,
    .history 6 3 3200,
    .history 8 2 1600,
    .history 8 3 1600,
    .history 10 4 10000 ]

def runPasses (table : PTable) : List Pass -> Bool
  | [] => false
  | pass :: rest => pass.check table || runPasses table rest

theorem runPasses_nonhalts {table : PTable} : forall passList,
    runPasses table passList = true ->
    table.toPTM.Nonhalts (0 : Fin 4) false
  | [], h => by simp [runPasses] at h
  | pass :: rest, h => by
      have hCases :
          pass.check table = true ∨ runPasses table rest = true := by
        simpa [runPasses] using Bool.or_eq_true_iff.mp h
      rcases hCases with hPass | hRest
      · exact Pass.check_nonhalts hPass
      · exact runPasses_nonhalts rest hRest

def nGramLeaf (table : PTable) (_cfg : Config 4) : Bool :=
  runPasses table passes

theorem nGramLeaf_sound : LeafSound nGramLeaf := by
  intro table _cfg machine hAgree hCheck steps
  exact PTable.nonhalts_machine_of_agrees
    (runPasses_nonhalts passes hCheck) hAgree steps

end NGram

/-- Sound prototype leaf.  Its eventual coverage is a separate computational
question and is deliberately not asserted here. -/
def leaf (table : PTable) (cfg : Config 4) : Bool :=
  completeLeaf table cfg ||
    (NGram.nGramLeaf table cfg || sporadicLeaf table cfg)

theorem leaf_sound : LeafSound leaf := by
  intro table cfg machine hAgree hLeaf steps
  have hOuter := Bool.or_eq_true_iff.mp hLeaf
  rcases hOuter with hComplete | hRest
  · exact completeLeaf_sound table cfg machine hAgree hComplete steps
  · have hInner := Bool.or_eq_true_iff.mp hRest
    rcases hInner with hNGram | hSporadic
    · exact NGram.nGramLeaf_sound table cfg machine hAgree hNGram steps
    · exact sporadicLeaf_sound table cfg machine hAgree hSporadic steps

end BB4
end BusyBeaver
end SetTheory
