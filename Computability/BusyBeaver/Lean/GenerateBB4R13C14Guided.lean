/-
  Untrusted generator for the guided R13/C14 proof certificate.

  Generated modules contain only concrete certificate data and ordinary
  `by decide` checks against `BusyBeaver/BB4/Guided.lean`.  This executable is
  deliberately outside the proof boundary and is removed after generation.
-/

import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common

namespace SetTheory.BusyBeaver.BB4.GenerateR13C14Guided

open Certificates

def indexedPasses : List (Nat × NGram.Pass) :=
  NGram.passes.zipIdx.map fun (pass, index) => (index + 1, pass)

def firstPass (table : PTable) : List (Nat × NGram.Pass) → Option Nat
  | [] => none
  | (index, pass) :: rest =>
      if pass.check table then some index else firstPass table rest

def firstHint (table : PTable) (cfg : Config 4) : Option Nat :=
  if completeLeaf table cfg then
    some 0
  else if Certificates.C14Uncovered.leaf table cfg then
    some 14
  else
    match firstPass table indexedPasses with
    | some index => some index
    | none => if sporadicLeaf table cfg then some 13 else none

inductive Tree where
  | close (hint : Nat)
  | halted
  | branch (children : List Tree)

partial def build (work : CertWork) : Except String Tree :=
  match firstHint work.table work.cfg with
  | some hint => .ok (.close hint)
  | none =>
      match work.fuel, work.cfg.state with
      | _, none =>
          if decide (work.cfg.tape.length <= 13) then
            .ok .halted
          else
            .error "halted configuration exceeds score 13"
      | 0, some _ => .error "uncovered active fuel-zero leaf"
      | _fuel + 1, some state =>
          let bit := Tape.read work.cfg.tape work.cfg.head
          match work.table state bit with
          | some _ => build work.normalize
          | none =>
              if !haltWritesSafe work.cfg then
                .error "unsafe halting write"
              else
                let actions := TNF.canonicalActions work.used
                if actions.length != 16 then
                  .error s!"expected 16 canonical actions, got {actions.length}"
                else
                  .branch <$> actions.mapM fun action => build (work.choose action)

def hintName : Nat → String
  | 0 => "Guided.Certificate.complete"
  | 1 => "Guided.Certificate.bool1"
  | 2 => "Guided.Certificate.bool2"
  | 3 => "Guided.Certificate.bool3"
  | 4 => "Guided.Certificate.history2x2"
  | 5 => "Guided.Certificate.history2x3"
  | 6 => "Guided.Certificate.history4x2"
  | 7 => "Guided.Certificate.history4x3"
  | 8 => "Guided.Certificate.history6x2"
  | 9 => "Guided.Certificate.history6x3"
  | 10 => "Guided.Certificate.history8x2"
  | 11 => "Guided.Certificate.history8x3"
  | 12 => "Guided.Certificate.history10x4"
  | 13 => "Guided.Certificate.sporadic"
  | _ => "Guided.Certificate.c14Uncovered"

def indent (level : Nat) : String :=
  String.ofList (List.replicate level ' ')

partial def render (level : Nat) : Tree → String
  | .close hint => hintName hint
  | .halted => "Guided.Certificate.branch16 " ++
      String.intercalate " " (List.replicate 16 "Guided.Certificate.complete")
  | .branch children =>
      let childIndent := indent (level + 2)
      "Guided.Certificate.branch16\n" ++
        String.intercalate "\n" (children.map fun child =>
          childIndent ++ "(" ++ render (level + 2) child ++ ")")

partial def branchCount : Tree → Nat
  | .close _ | .halted => 0
  | .branch children =>
      1 + children.foldl (fun count child => count + branchCount child) 0

/-- Number of `branch16` constructors in rendered certificate data.  A halted
search node renders as one dummy branch (whose children are ignored), so the
packed-module resource budget counts it even though it is not a search branch. -/
partial def renderedBranchCount : Tree → Nat
  | .close _ => 0
  | .halted => 1
  | .branch children =>
      1 + children.foldl (fun count child =>
        count + renderedBranchCount child) 0

partial def hasHistoryHint : Tree → Bool
  | .close hint => 4 <= hint && hint <= 12
  | .halted => false
  | .branch children => children.any hasHistoryHint

def parseChoice (text : String) : Option GoAction := do
  let index ← text.toNat?
  actionList[index]?

def actionName (action : GoAction) : String :=
  match actionList.findIdx? (· = action) with
  | some index => s!"a{if index < 10 then "0" else ""}{index}"
  | none => "a00"

def component (action : GoAction) : String :=
  let name := actionName action
  "A" ++ name.drop 1

def stem (choices : List GoAction) : String :=
  String.intercalate "_" (choices.map actionName)

def leanList (choices : List GoAction) : String :=
  "[" ++ String.intercalate ", " (choices.map actionName) ++ "]"

def moduleSuffix (choices : List GoAction) : String :=
  String.intercalate "." (choices.map component)

def directorySuffix (choices : List GoAction) : String :=
  String.intercalate "/" (choices.dropLast.map component)

def directDeclarations (choices : List GoAction) (tree : Tree) : String :=
  let name := stem choices
  let heartbeatPrefix := if hasHistoryHint tree then
      "set_option maxHeartbeats 1600000 in\n"
    else ""
  s!"def work_{name} : Guided.Work :=\n" ++
  s!"  after {leanList choices}\n\n" ++
  s!"def certificate_{name} : Guided.Certificate :=\n" ++
  s!"  {render 2 tree}\n\n" ++
  heartbeatPrefix ++ s!"theorem verified_{name} :\n" ++
  s!"    work_{name}.check certificate_{name} = true := by\n" ++
  s!"  decide\n"

def sourceHeader : String :=
  "import BusyBeaver.BB4.Certificates.R13.C14.Guided.Common\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided\n\n" ++
  "open Certificates\n\n"

def sourceFooter : String :=
  s!"end SetTheory.BusyBeaver.BB4.Certificates.C14Guided\n"

def outputSource (choices : List GoAction) (tree : Tree) : String :=
  sourceHeader ++ directDeclarations choices tree ++ "\n" ++ sourceFooter

def moduleName (choices : List GoAction) : String :=
  "BusyBeaver.BB4.Certificates.R13.C14.Guided." ++
    moduleSuffix choices

def childChoices (choices : List GoAction) : List (List GoAction) :=
  actionList.map fun action => choices ++ [action]

def parentSourceWithImports (choices : List GoAction) (used : Nat)
    (importModules : List String) : String :=
  let name := stem choices
  let children := childChoices choices
  let imports := String.intercalate "\n"
    (importModules.map fun moduleName' => "import " ++ moduleName')
  let childNames := children.map stem
  let certificates := childNames.map fun child => "certificate_" ++ child
  let certificateArgs := String.intercalate "\n"
    (certificates.map fun child => "    " ++ child)
  let helperCertificateArgs := String.intercalate "\n"
    (certificates.map fun child => "      " ++ child)
  let haves := String.intercalate "\n" <| (List.range 16).map fun index =>
    let suffix := if index < 10 then "0" ++ toString index else toString index
    let child := childNames[index]!
    let certificate := certificates[index]!
    s!"    have h{suffix} :\n" ++
    s!"        ((after {leanList choices}).assign a{suffix}).check\n" ++
    s!"          {certificate} = true := by\n" ++
    s!"      rw [assign_check_eq_pathAppend]\n" ++
    s!"      exact verified_{child}"
  let helperHypothesisArgs := String.intercalate "\n" <|
    (List.range 16).map fun index =>
      s!"      h{if index < 10 then "0" else ""}{index}"
  let canonical := if used = 3 then
      "Certificates.canonicalActions_three_eq"
    else
      "Certificates.canonicalActions_four_eq"
  imports ++ "\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.C14Guided\n\n" ++
  "open Certificates\n\n" ++
  s!"def certificate_{name} : Guided.Certificate :=\n" ++
  "  Guided.Certificate.branch16\n" ++ certificateArgs ++ "\n\n" ++
  s!"theorem verified_{name} :\n" ++
  s!"    pathCheck {leanList choices} certificate_{name} = true := by\n" ++
  "  have hAll :\n" ++
  s!"      (TNF.canonicalActions (after {leanList choices}).used).all\n" ++
  "        (fun action =>\n" ++
  s!"          ((after {leanList choices}).assign action).check\n" ++
  "            (Guided.Certificate.children16\n" ++ certificateArgs ++
  " action)) = true := by\n" ++ haves ++ "\n" ++
  s!"    rw [show (after {leanList choices}).used = {used} by decide,\n" ++
  s!"      {canonical}]\n" ++
  "    exact all_children16\n" ++
  "      (fun action certificate =>\n" ++
  s!"        ((after {leanList choices}).assign action).check certificate)\n" ++
  helperCertificateArgs ++ "\n" ++
  helperHypothesisArgs ++ "\n" ++
  "  change\n" ++
  s!"    (haltWritesSafe (after {leanList choices}).cfg &&\n" ++
  s!"      (TNF.canonicalActions (after {leanList choices}).used).all\n" ++
  "        (fun action =>\n" ++
  s!"          ((after {leanList choices}).assign action).check\n" ++
  "            (Guided.Certificate.children16\n" ++ certificateArgs ++
  " action))) = true\n" ++
  "  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.C14Guided\n"

def parentSource (choices : List GoAction) (used : Nat) : String :=
  parentSourceWithImports choices used ((childChoices choices).map moduleName)

/-! ## Packed sibling modules

Packing changes only Lake's module granularity.  Every direct certificate keeps
its own definition and ordinary `by decide` theorem; a batch merely places
several such sibling declarations in one source file. -/

abbrev DirectObligation := List GoAction × Tree
abbrev DirectBatch := List DirectObligation

def batchBranchCount (batch : DirectBatch) : Nat :=
  batch.foldl (fun count obligation =>
    count + renderedBranchCount obligation.2) 0

def batchHasHistory (batch : DirectBatch) : Bool :=
  batch.any fun obligation => hasHistoryHint obligation.2

def batchHistoryCount (batch : DirectBatch) : Nat :=
  batch.foldl (fun count obligation =>
    if hasHistoryHint obligation.2 then count + 1 else count) 0

def batchValid (threshold : Nat) (batch : DirectBatch) : Bool :=
  !batch.isEmpty && decide (batchBranchCount batch <= threshold) &&
    decide (batchHistoryCount batch <= 1)

def canPack (threshold : Nat) (obligation : DirectObligation)
    (batch : DirectBatch) : Bool :=
  decide (batchBranchCount batch + renderedBranchCount obligation.2 <= threshold) &&
    !(hasHistoryHint obligation.2 && batchHasHistory batch)

/-- Deterministic first-fit packing in action order.  Appending within a batch
preserves sibling order, the aggregate structural budget never exceeds the
ordinary direct-decision threshold, and no batch has two history checks. -/
def insertPacked (threshold : Nat) (obligation : DirectObligation) :
    List DirectBatch → List DirectBatch
  | [] => [[obligation]]
  | batch :: rest =>
      if canPack threshold obligation batch then
        (batch ++ [obligation]) :: rest
      else
        batch :: insertPacked threshold obligation rest

def packDirects (threshold : Nat)
    (obligations : List DirectObligation) : List DirectBatch :=
  obligations.foldl (fun batches obligation =>
    insertPacked threshold obligation batches) []

def batchSource (batch : DirectBatch) : String :=
  sourceHeader ++
    String.intercalate "\n" (batch.map fun obligation =>
      directDeclarations obligation.1 obligation.2) ++
    "\n" ++ sourceFooter

def batchComponent (index : Nat) : String :=
  s!"Batch{if index < 10 then "0" else ""}{index}"

def batchModuleName (choices : List GoAction) (index : Nat) : String :=
  moduleName choices ++ "." ++ batchComponent index

def outputBase : String :=
  "BusyBeaver/BB4/Certificates/R13/C14/Guided"

def choicesDirectory (choices : List GoAction) : String :=
  let suffix := String.intercalate "/" (choices.map component)
  if suffix.isEmpty then outputBase else outputBase ++ "/" ++ suffix

def outputPath (choices : List GoAction) : String × String :=
  let relativeDirectory := directorySuffix choices
  let directory := if relativeDirectory.isEmpty then outputBase
    else outputBase ++ "/" ++ relativeDirectory
  let last := choices.getLast?.getD a00
  (directory, directory ++ "/" ++ component last ++ ".lean")

def batchOutputPath (choices : List GoAction) (index : Nat) : String × String :=
  let directory := choicesDirectory choices
  (directory, directory ++ "/" ++ batchComponent index ++ ".lean")

def writeOutput (choices : List GoAction) (source : String) : IO Unit := do
  let (directory, file) := outputPath choices
  IO.FS.createDirAll directory
  IO.FS.writeFile file source

def writeBatchOutput (choices : List GoAction) (index : Nat)
    (source : String) : IO Unit := do
  let (directory, file) := batchOutputPath choices index
  IO.FS.createDirAll directory
  IO.FS.writeFile file source

def removeFileIfExists (file : String) : IO Unit := do
  let path : System.FilePath := file
  if ← path.pathExists then
    IO.FS.removeFile path

def removeDirectoryIfExists (directory : String) : IO Unit := do
  let path : System.FilePath := directory
  if ← path.isDir then
    IO.FS.removeDirAll path

def removeOutput (choices : List GoAction) : IO Unit := do
  let (_, file) := outputPath choices
  removeFileIfExists file

def removeDescendantOutputs (choices : List GoAction) : IO Unit :=
  removeDirectoryIfExists (choicesDirectory choices)

def removeBatchOutput (choices : List GoAction) (index : Nat) : IO Unit := do
  let (_, file) := batchOutputPath choices index
  removeFileIfExists file

partial def emitPlan (threshold : Nat) (choices : List GoAction)
    (tree : Tree) : IO Unit := do
  if branchCount tree <= threshold then
    writeOutput choices (outputSource choices tree)
  else
    match tree with
    | .branch children =>
        if children.length != 16 then
          throw <| IO.userError "guided branch does not have 16 children"
        for pair in (childChoices choices).zip children do
          emitPlan threshold pair.1 pair.2
        let used := (CertWork.after choices).used
        writeOutput choices (parentSource choices used)
    | _ =>
        throw <| IO.userError "non-branch certificate exceeds threshold"

/-- The current generated forest contains these additional, deliberately
proactive splits below the normal threshold.  Recording them here makes
`pack` preserve every existing direct `by decide` boundary instead of merging
one of those decisions back into a larger theorem. -/
def forcedPackedSplits : List (List GoAction) :=
  [ [a00, a08, a15, a06],
    [a00, a11, a10, a01],
    [a08, a03, a02, a04],
    [a08, a11, a10, a05],
    [a09, a00, a14, a15],
    [a09, a03, a02, a04],
    [a11, a00, a01, a04],
    [a11, a01, a03],
    [a11, a01, a03, a04],
    [a11, a01, a03, a09],
    [a11, a01, a03, a12],
    [a11, a03, a05, a12],
    [a11, a03, a06, a12],
    [a11, a03, a09, a04],
    [a11, a10, a08, a05] ]

def isForcedPackedSplit (choices : List GoAction) : Bool :=
  forcedPackedSplits.any fun path => decide (path = choices)

def shouldSplitPacked (threshold : Nat) (choices : List GoAction)
    (tree : Tree) : Bool :=
  decide (threshold < renderedBranchCount tree) || isForcedPackedSplit choices

/-- Emit the same direct proof obligations as the current plan, but colocate
siblings in deterministic batch modules.  Parent modules import recursive
children individually and direct children through their batch modules. -/
partial def emitPackedPlan (threshold : Nat) (choices : List GoAction)
    (tree : Tree) : IO Unit := do
  if shouldSplitPacked threshold choices tree then
    match tree with
    | .branch children =>
        if children.length != 16 then
          throw <| IO.userError "guided branch does not have 16 children"
        let pairs := (childChoices choices).zip children
        let splitChildren := pairs.filter fun pair =>
          shouldSplitPacked threshold pair.1 pair.2
        let directChildren := pairs.filter fun pair =>
          !shouldSplitPacked threshold pair.1 pair.2
        for pair in splitChildren do
          emitPackedPlan threshold pair.1 pair.2
        let batches := packDirects threshold directChildren
        if !batches.all (batchValid threshold) then
          throw <| IO.userError "invalid guided sibling batch"
        for pair in batches.zipIdx do
          writeBatchOutput choices pair.2 (batchSource pair.1)
        let recursiveImports := splitChildren.map fun pair => moduleName pair.1
        let batchImports := batches.zipIdx.map fun (_batch, index) =>
          batchModuleName choices index
        let used := (CertWork.after choices).used
        writeOutput choices <|
          parentSourceWithImports choices used (recursiveImports ++ batchImports)
        -- The declarations now live in their batch modules.  Delete the old
        -- standalone siblings only after both batches and parent were written.
        for pair in directChildren do
          removeOutput pair.1
          removeDescendantOutputs pair.1
        -- A parent has only sixteen children, hence at most sixteen batches.
        -- Remove leftovers from an earlier packing run with a larger count.
        for index in List.range 16 do
          if batches.length <= index then
            removeBatchOutput choices index
    | _ =>
        throw <| IO.userError "packed split is not a certificate branch"
  else
    writeOutput choices (outputSource choices tree)
    -- If a formerly split node has become direct, its replacement is the
    -- sibling `.lean` file just written; all files below its directory are
    -- stale generated descendants.
    removeDescendantOutputs choices

/-- Keep direct kernel decisions below the empirically validated structural
limit.  Larger trees are assembled from separately checked child theorems. -/
def planningThreshold : Nat := 20

def _root_.main (args : List String) : IO Unit := do
  if args = ["plan", "all"] then
    for action in actionList do
      let choices := [action]
      let tree ← match build (CertWork.after choices) with
        | .ok tree => pure tree
        | .error message => throw <| IO.userError message
      emitPlan planningThreshold choices tree
      IO.println s!"generated {moduleSuffix choices} ({branchCount tree} branches)"
    return
  if args = ["pack", "all"] then
    for action in actionList do
      let choices := [action]
      let tree ← match build (CertWork.after choices) with
        | .ok tree => pure tree
        | .error message => throw <| IO.userError message
      emitPackedPlan planningThreshold choices tree
      IO.println s!"packed {moduleSuffix choices} ({branchCount tree} branches)"
    return
  let planning := args.head? = some "plan"
  let splitting := args.head? = some "split"
  let packing := args.head? = some "pack"
  let choiceArgs := if planning || splitting || packing then args.drop 1 else args
  let choices := choiceArgs.filterMap parseChoice
  if choices.isEmpty || choices.length != choiceArgs.length then
    throw <| IO.userError "expected one or more action indices in 0..15"
  let tree ← match build (CertWork.after choices) with
    | .ok tree => pure tree
    | .error message => throw <| IO.userError message
  if packing then
    emitPackedPlan planningThreshold choices tree
  else if planning || splitting then
    emitPlan (if splitting then 1 else planningThreshold) choices tree
  else
    writeOutput choices (outputSource choices tree)
  IO.println <| s!"{if packing then "packed" else "generated"} " ++
    s!"{moduleSuffix choices} ({branchCount tree} branches)"

end SetTheory.BusyBeaver.BB4.GenerateR13C14Guided
