/-
  Untrusted generator for guided R05/A14 proof certificates.

  The output contains only data plus an ordinary `by decide` theorem checked
  by `BusyBeaver/BB4/Guided.lean`; this program is not in the proof boundary.
-/

import BusyBeaver.BB4.Guided
import BusyBeaver.BB4.Certificates.R05.A14.Common
import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common

namespace SetTheory.BusyBeaver.BB4.GenerateR05A14Guided

open Certificates
open Certificates.R05A14

def indexedPasses : List (Nat × NGram.Pass) :=
  NGram.passes.zipIdx.map fun (pass, index) => (index + 1, pass)

/-- Prefer the two-cell history passes before the much more expensive
three-cell `history4x3` pass.  The numeric indices remain the canonical
`NGram.passes` indices used by `hintName`; only certificate selection order
changes. -/
def preferredPasses : List (Nat × NGram.Pass) :=
  [1, 2, 3, 4, 5, 6, 8, 10, 7, 9, 11, 12].filterMap fun wanted =>
    indexedPasses.find? fun pair => pair.1 == wanted

def firstPass (table : PTable) : List (Nat × NGram.Pass) -> Option Nat
  | [] => none
  | (index, pass) :: rest =>
      if pass.check table then some index else firstPass table rest

/-- Exact tables for which the first otherwise-selected pass is substantially
more expensive in the kernel than the also-valid history-4x2 certificate.
This untrusted preference only chooses the hint; `Guided.verify` still checks
the selected pass semantically. -/
def preferHistory4x2 (table : PTable) : Bool :=
  (decide (table (0 : Fin 4) false = some a05) &&
    decide (table (0 : Fin 4) true = some a10) &&
    decide (table (1 : Fin 4) false = some a14) &&
    decide (table (1 : Fin 4) true = some a13) &&
    decide (table (2 : Fin 4) false = some a08) &&
    decide (table (2 : Fin 4) true = some a03) &&
    decide (table (3 : Fin 4) false = none) &&
    decide (table (3 : Fin 4) true = some a08)) ||
  (decide (table (0 : Fin 4) false = some a05) &&
    decide (table (0 : Fin 4) true = none) &&
    decide (table (1 : Fin 4) false = some a14) &&
    decide (table (1 : Fin 4) true = some a04) &&
    decide (table (2 : Fin 4) false = some a11) &&
    decide (table (2 : Fin 4) true = some a02) &&
    decide (table (3 : Fin 4) false = some a13) &&
    decide (table (3 : Fin 4) true = some a03)) ||
  (decide (table (0 : Fin 4) false = some a05) &&
    decide (table (0 : Fin 4) true = some a06) &&
    decide (table (1 : Fin 4) false = some a14) &&
    decide (table (1 : Fin 4) true = none) &&
    decide (table (2 : Fin 4) false = some a11) &&
    decide (table (2 : Fin 4) true = some a03) &&
    decide (table (3 : Fin 4) false = some a12) &&
    decide (table (3 : Fin 4) true = some a02)) ||
  (decide (table (0 : Fin 4) false = some a05) &&
    decide (table (0 : Fin 4) true = none) &&
    decide (table (1 : Fin 4) false = some a14) &&
    decide (table (1 : Fin 4) true = some a15) &&
    decide (table (2 : Fin 4) false = some a11) &&
    decide (table (2 : Fin 4) true = some a12) &&
    decide (table (3 : Fin 4) false = some a09) &&
    decide (table (3 : Fin 4) true = some a03)) ||
  (decide (table (0 : Fin 4) false = some a05) &&
    decide (table (0 : Fin 4) true = none) &&
    decide (table (1 : Fin 4) false = some a14) &&
    decide (table (1 : Fin 4) true = some a13) &&
    decide (table (2 : Fin 4) false = some a11) &&
    decide (table (2 : Fin 4) true = some a02) &&
    decide (table (3 : Fin 4) false = some a12) &&
    decide (table (3 : Fin 4) true = some a03))

def firstHint (table : PTable) (cfg : Config 4) : Option Nat :=
  if completeLeaf table cfg then
    some 0
  else if preferHistory4x2 table then
    some 6
  else if Certificates.R05A14HistoryInvariantA15A09A03A02A04.leaf table cfg then
    some 15
  else if Certificates.R05A14HistoryInvariant.leaf table cfg then
    some 14
  else
    match firstPass table preferredPasses with
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

def hintName : Nat -> String
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
  | 14 => "Guided.Certificate.r05A14HistoryInvariant"
  | _ => "Guided.Certificate.r05A14A15Pump"

def indent (level : Nat) : String := String.ofList (List.replicate level ' ')

partial def render (level : Nat) : Tree -> String
  | .close hint => hintName hint
  | .halted => "Guided.Certificate.branch16 " ++
      String.intercalate " " (List.replicate 16 "Guided.Certificate.complete")
  | .branch children =>
      let childIndent := indent (level + 2)
      "Guided.Certificate.branch16\n" ++
        String.intercalate "\n" (children.map fun child =>
          childIndent ++ "(" ++ render (level + 2) child ++ ")")

partial def branchCount : Tree -> Nat
  | .close _ | .halted => 0
  | .branch children =>
      1 + children.foldl (fun count child => count + branchCount child) 0

partial def hasHistoryHint : Tree -> Bool
  | .close hint => 4 <= hint && hint <= 12
  | .halted => false
  | .branch children => children.any hasHistoryHint

partial def historyHintCount : Tree -> Nat
  | .close hint => if 4 <= hint && hint <= 12 then 1 else 0
  | .halted => 0
  | .branch children =>
      children.foldl (fun count child => count + historyHintCount child) 0

def parseChoice (text : String) : Option GoAction := do
  let index <- text.toNat?
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

def usesSuppliedHistoryCertificate (choices : List GoAction) : Bool :=
  decide (choices = [a11, a03, a12, a13, a10])

def suppliedHistoryOutputSource (choices : List GoAction) : String :=
  let name := stem choices
  let explicitModule :=
    "BusyBeaver.BB4.Certificates.R05.A14.Guided." ++
      moduleSuffix choices ++ ".Explicit.Proof"
  s!"import {explicitModule}\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open Certificates\n\n" ++
  s!"def work_{name} : Guided.Work :=\n" ++
  s!"  after {leanList choices}\n\n" ++
  s!"def certificate_{name} : Guided.Certificate :=\n" ++
  "  Guided.Certificate.suppliedHistory 4 2 explicitCertificate\n\n" ++
  s!"theorem verified_{name} :\n" ++
  s!"    work_{name}.check certificate_{name} = true := by\n" ++
  "  change NGram.historyCertificateCheck\n" ++
  s!"    work_{name}.table 4 2 explicitCertificate = true\n" ++
  "  apply NGram.historyCertificateCheck_of_valid\n" ++
  s!"  simpa [work_{name}, explicitTable, explicitBlank] using explicitValid\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def outputSource (choices : List GoAction) (tree : Tree) : String :=
  if usesSuppliedHistoryCertificate choices then
    suppliedHistoryOutputSource choices
  else
    let name := stem choices
    let heartbeatPrefix := if hasHistoryHint tree then
        "set_option maxHeartbeats 1600000 in\n"
      else ""
    s!"import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common\n\n" ++
    s!"set_option maxRecDepth 10000\n\n" ++
    s!"namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
    s!"open Certificates\n\n" ++
    s!"def work_{name} : Guided.Work :=\n" ++
    s!"  after {leanList choices}\n\n" ++
    s!"def certificate_{name} : Guided.Certificate :=\n" ++
    s!"  {render 2 tree}\n\n" ++
    heartbeatPrefix ++ s!"theorem verified_{name} :\n" ++
    s!"    work_{name}.check certificate_{name} = true := by\n" ++
    s!"  decide\n\n" ++
    s!"end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def moduleName (choices : List GoAction) : String :=
  "BusyBeaver.BB4.Certificates.R05.A14.Guided." ++
    moduleSuffix choices

def childChoices (choices : List GoAction) : List (List GoAction) :=
  actionList.map fun action => choices ++ [action]

def parentSource (choices : List GoAction) (used : Nat) : String :=
  let name := stem choices
  let children := childChoices choices
  let imports := String.intercalate "\n"
    (children.map fun child => "import " ++ moduleName child)
  let childNames := children.map stem
  let certificates := childNames.map fun child => "certificate_" ++ child
  let certificateArgs := String.intercalate "\n"
    (certificates.map fun child => "    " ++ child)
  let haves := String.intercalate "\n" <| (List.range 16).map fun index =>
    let suffix := if index < 10 then "0" ++ toString index else toString index
    let child := childNames[index]!
    let certificate := certificates[index]!
    s!"    have h{suffix} :\n" ++
    s!"        ((after {leanList choices}).assign a{suffix}).check\n" ++
    s!"          {certificate} = true := by\n" ++
    s!"      rw [assign_check_eq_pathAppend]\n" ++
    s!"      exact verified_{child}"
  let hNames := String.intercalate ", " <| (List.range 16).map fun index =>
    s!"h{if index < 10 then "0" else ""}{index}"
  let canonical := if used = 3 then
      "Certificates.canonicalActions_three_eq"
    else
      "Certificates.canonicalActions_four_eq"
  imports ++ "\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
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
  "    simp [" ++ hNames ++ "]\n" ++
  "  change\n" ++
  s!"    (haltWritesSafe (after {leanList choices}).cfg &&\n" ++
  s!"      (TNF.canonicalActions (after {leanList choices}).used).all\n" ++
  "        (fun action =>\n" ++
  s!"          ((after {leanList choices}).assign action).check\n" ++
  "            (Guided.Certificate.children16\n" ++ certificateArgs ++
  " action))) = true\n" ++
  "  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def outputPath (choices : List GoAction) : String × String :=
  let base := "BusyBeaver/BB4/Certificates/R05/A14/Guided"
  let relativeDirectory := directorySuffix choices
  let directory := if relativeDirectory.isEmpty then base
    else base ++ "/" ++ relativeDirectory
  let last := choices.getLast?.getD a00
  (directory, directory ++ "/" ++ component last ++ ".lean")

def writeOutput (choices : List GoAction) (source : String) : IO Unit := do
  let (directory, file) := outputPath choices
  IO.FS.createDirAll directory
  IO.FS.writeFile file source

def renderList (renderValue : α -> String) (values : List α) : String :=
  "[" ++ String.intercalate ", " (values.map renderValue) ++ "]"

def renderFin4 (value : Fin 4) : String :=
  s!"({value.val} : Fin 4)"

def renderHistoryEntry (entry : Fin 4 × Bool) : String :=
  s!"({renderFin4 entry.1}, {entry.2})"

def renderHistorySymbol (symbol : NGram.HistorySymbol) : String :=
  "{ bit := " ++ toString symbol.bit ++ ", history := " ++
    renderList renderHistoryEntry symbol.history ++ " }"

def renderHistoryWord (word : List NGram.HistorySymbol) : String :=
  renderList renderHistorySymbol word

def renderHistoryMid
    (mid : NGram.MidWord NGram.HistorySymbol) : String :=
  "{ left := " ++ renderHistoryWord mid.left ++
    ", right := " ++ renderHistoryWord mid.right ++
    ", center := " ++ renderHistorySymbol mid.center ++
    ", state := " ++ renderFin4 mid.state ++ " }"

partial def chunkList (size : Nat) (values : List α) : List (List α) :=
  if values.isEmpty then []
  else values.take size :: chunkList size (values.drop size)

def pad3 (index : Nat) : String :=
  let digits := toString index
  String.ofList (List.replicate (3 - digits.length) '0') ++ digits

def explicitModulePrefix (choices : List GoAction) : String :=
  "BusyBeaver.BB4.Certificates.R05.A14.Guided." ++
    moduleSuffix choices ++ ".Explicit"

def explicitDirectory (choices : List GoAction) : String :=
  "BusyBeaver/BB4/Certificates/R05/A14/Guided/" ++
    String.intercalate "/" (choices.map component) ++ "/Explicit"

def explicitDataSource (index : Nat)
    (mids : List (NGram.MidWord NGram.HistorySymbol)) : String :=
  let suffix := pad3 index
  "import BusyBeaver.BB4.NGramBuilder\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  s!"def explicitMids{suffix} : List (NGram.MidWord NGram.HistorySymbol) :=\n  " ++
    renderList renderHistoryMid mids ++ "\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def appendNames (names : List String) : String :=
  match names with
  | [] => "[]"
  | first :: rest => rest.foldl (fun value name => value ++ " ++ " ++ name) first

def explicitCertificateSource (choices : List GoAction)
    (certificate : NGram.AbstractState NGram.HistorySymbol)
    (chunkCount : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let names := (List.range chunkCount).map fun index => s!"explicitMids{pad3 index}"
  let imports := String.intercalate "\n" <|
    ["import BusyBeaver.BB4.Certificates.R05.A14.Guided.Common"] ++
      (List.range chunkCount).map fun index =>
        s!"import {modulePrefix}.Data{pad3 index}"
  imports ++ "\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open Certificates\n\n" ++
  s!"def explicitTable : PTable := (after {leanList choices}).table\n\n" ++
  "def explicitBlank : NGram.HistorySymbol :=\n" ++
  "  { bit := false, history := [] }\n\n" ++
  "def explicitLeftWords : List (List NGram.HistorySymbol) :=\n  " ++
    renderList renderHistoryWord certificate.leftWords ++ "\n\n" ++
  "def explicitRightWords : List (List NGram.HistorySymbol) :=\n  " ++
    renderList renderHistoryWord certificate.rightWords ++ "\n\n" ++
  "def explicitMids : List (NGram.MidWord NGram.HistorySymbol) :=\n  " ++
    appendNames names ++ "\n\n" ++
  "def explicitCertificate : NGram.AbstractState NGram.HistorySymbol :=\n" ++
  "  { leftWords := explicitLeftWords\n" ++
  "    rightWords := explicitRightWords\n" ++
  "    mids := explicitMids }\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def explicitProofShardSource (choices : List GoAction) (index : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let suffix := pad3 index
  s!"import {modulePrefix}.Certificate\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  s!"theorem explicitMidLengths{suffix} :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  s!"      explicitMids{suffix} := by\n  decide\n\n" ++
  "set_option maxHeartbeats 1600000 in\n" ++
  s!"theorem explicitClosed{suffix} :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  s!"      explicitMids{suffix} := by\n  decide\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def explicitProofPartSource (choices : List GoAction) (index part : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let suffix := pad3 index
  let offset := part * 8
  s!"import {modulePrefix}.Certificate\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  s!"def explicitMids{suffix}Part{part} : List (NGram.MidWord NGram.HistorySymbol) :=\n" ++
  s!"  (explicitMids{suffix}.drop {offset}).take 8\n\n" ++
  s!"theorem explicitMidLengths{suffix}Part{part} :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  s!"      explicitMids{suffix}Part{part} := by\n  decide\n\n" ++
  "set_option maxHeartbeats 1600000 in\n" ++
  s!"theorem explicitClosed{suffix}Part{part} :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  s!"      explicitMids{suffix}Part{part} := by\n  decide\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

/- A small number of history-4x2 eight-mid subshards exceeded the laptop's
memory, while their one-mid checks stay comfortably bounded.  This is only a
generation preference: every emitted atom is still checked by ordinary kernel
`decide`, and each parent theorem is assembled propositionally. -/
def atomizeExplicitPart (choices : List GoAction) (index part : Nat) : Bool :=
  decide (choices = [a11, a03, a12, a13, a10]) &&
    (index == 28 || index == 63) && part == 1

def explicitProofAtomSource (choices : List GoAction)
    (index part atom : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let suffix := pad3 index
  let offset := part * 8 + atom
  s!"import {modulePrefix}.Certificate\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  s!"def explicitMids{suffix}Part{part}Atom{atom} : " ++
  "List (NGram.MidWord NGram.HistorySymbol) :=\n" ++
  s!"  (explicitMids{suffix}.drop {offset}).take 1\n\n" ++
  s!"theorem explicitMidLengths{suffix}Part{part}Atom{atom} :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  s!"      explicitMids{suffix}Part{part}Atom{atom} := by\n  decide\n\n" ++
  "set_option maxHeartbeats 1600000 in\n" ++
  s!"theorem explicitClosed{suffix}Part{part}Atom{atom} :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  s!"      explicitMids{suffix}Part{part}Atom{atom} := by\n  decide\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

partial def rightAssociatedCombine (functionName : String) : List String -> String
  | [] => "by decide"
  | [name] => name
  | name :: names =>
      functionName ++ " " ++ name ++ " (" ++
        rightAssociatedCombine functionName names ++ ")"

partial def rightAssociatedAppend : List String -> String
  | [] => "[]"
  | [name] => name
  | name :: names => name ++ " ++ (" ++ rightAssociatedAppend names ++ ")"

def explicitAtomizedPartSource (choices : List GoAction)
    (index part atomCount : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let suffix := pad3 index
  let atomNames := (List.range atomCount).map fun atom =>
    s!"explicitMids{suffix}Part{part}Atom{atom}"
  let midLengthNames := (List.range atomCount).map fun atom =>
    s!"explicitMidLengths{suffix}Part{part}Atom{atom}"
  let closedNames := (List.range atomCount).map fun atom =>
    s!"explicitClosed{suffix}Part{part}Atom{atom}"
  let imports := String.intercalate "\n" <|
    (List.range atomCount).map fun atom =>
      s!"import {modulePrefix}.Proof{suffix}.Part{part}.Atom{atom}"
  let helper := s!"explicitAll_append{suffix}Part{part}"
  imports ++ "\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  s!"def explicitMids{suffix}Part{part} : " ++
  "List (NGram.MidWord NGram.HistorySymbol) :=\n" ++
  s!"  (explicitMids{suffix}.drop {part * 8}).take 8\n\n" ++
  "theorem " ++ helper ++ " {P : alpha -> Prop} {left right : List alpha}\n" ++
  "    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :\n" ++
  "    NGramCPS.All P (left ++ right) := by\n" ++
  "  induction left with\n" ++
  "  | nil => exact hRight\n" ++
  "  | cons head tail ih =>\n" ++
  "      exact And.intro hLeft.1 (ih hLeft.2)\n\n" ++
  s!"theorem explicitMids{suffix}Part{part}_atoms :\n" ++
  "    " ++ rightAssociatedAppend atomNames ++ " =\n" ++
  s!"      explicitMids{suffix}Part{part} := by\n  decide\n\n" ++
  s!"theorem explicitMidLengths{suffix}Part{part} :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  s!"      explicitMids{suffix}Part{part} := by\n" ++
  "  have h := " ++ rightAssociatedCombine helper midLengthNames ++ "\n" ++
  s!"  rw [explicitMids{suffix}Part{part}_atoms] at h\n  exact h\n\n" ++
  s!"theorem explicitClosed{suffix}Part{part} :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  s!"      explicitMids{suffix}Part{part} := by\n" ++
  "  have h := " ++ rightAssociatedCombine helper closedNames ++ "\n" ++
  s!"  rw [explicitMids{suffix}Part{part}_atoms] at h\n  exact h\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def explicitSplitProofSource (choices : List GoAction) (index : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let suffix := pad3 index
  let imports := String.intercalate "\n" <|
    (List.range 4).map fun part => s!"import {modulePrefix}.Proof{suffix}.Part{part}"
  imports ++ "\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  "theorem explicitAll_append" ++ suffix ++ " {P : alpha -> Prop} " ++
  "{left right : List alpha}\n" ++
  "    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :\n" ++
  "    NGramCPS.All P (left ++ right) := by\n" ++
  "  induction left with\n" ++
  "  | nil => exact hRight\n" ++
  "  | cons head tail ih =>\n" ++
  "      exact And.intro hLeft.1 (ih hLeft.2)\n\n" ++
  s!"theorem explicitMids{suffix}_parts :\n" ++
  s!"    explicitMids{suffix}Part0 ++\n" ++
  s!"      (explicitMids{suffix}Part1 ++\n" ++
  s!"        (explicitMids{suffix}Part2 ++ explicitMids{suffix}Part3)) =\n" ++
  s!"      explicitMids{suffix} := by\n  decide\n\n" ++
  s!"theorem explicitMidLengths{suffix} :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  s!"      explicitMids{suffix} := by\n" ++
  s!"  have h := explicitAll_append{suffix} explicitMidLengths{suffix}Part0\n" ++
  s!"    (explicitAll_append{suffix} explicitMidLengths{suffix}Part1\n" ++
  s!"      (explicitAll_append{suffix} explicitMidLengths{suffix}Part2\n" ++
  s!"        explicitMidLengths{suffix}Part3))\n" ++
  s!"  rw [explicitMids{suffix}_parts] at h\n  exact h\n\n" ++
  s!"theorem explicitClosed{suffix} :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  s!"      explicitMids{suffix} := by\n" ++
  s!"  have h := explicitAll_append{suffix} explicitClosed{suffix}Part0\n" ++
  s!"    (explicitAll_append{suffix} explicitClosed{suffix}Part1\n" ++
  s!"      (explicitAll_append{suffix} explicitClosed{suffix}Part2\n" ++
  s!"        explicitClosed{suffix}Part3))\n" ++
  s!"  rw [explicitMids{suffix}_parts] at h\n  exact h\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

partial def balancedCombine (functionName : String) : List String -> String
  | [] => "by decide"
  | [name] => name
  | names =>
      let half := names.length / 2
      functionName ++ " (" ++ balancedCombine functionName (names.take half) ++
        ") (" ++ balancedCombine functionName (names.drop half) ++ ")"

def explicitProofSource (choices : List GoAction) (chunkCount : Nat) : String :=
  let modulePrefix := explicitModulePrefix choices
  let imports := String.intercalate "\n" <|
    (List.range chunkCount).map fun index => s!"import {modulePrefix}.Proof{pad3 index}"
  let midLengthNames := (List.range chunkCount).map fun index =>
    s!"explicitMidLengths{pad3 index}"
  let closedNames := (List.range chunkCount).map fun index =>
    s!"explicitClosed{pad3 index}"
  let lastSuffix := pad3 (chunkCount - 1)
  imports ++ "\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "open BB3\n\n" ++
  "theorem explicitAll_append {P : alpha -> Prop} {left right : List alpha}\n" ++
  "    (hLeft : NGramCPS.All P left) (hRight : NGramCPS.All P right) :\n" ++
  "    NGramCPS.All P (left ++ right) := by\n" ++
  "  induction left with\n" ++
  "  | nil => exact hRight\n" ++
  "  | cons head tail ih =>\n" ++
  "      exact And.intro hLeft.1 (ih hLeft.2)\n\n" ++
  "theorem explicitMidLengths :\n" ++
  "    NGramCPS.All (fun mid => mid.left.length = 2 /\\ mid.right.length = 2)\n" ++
  "      explicitMids := by\n" ++
  "  unfold explicitMids\n" ++
  "  have h := " ++ balancedCombine "explicitAll_append" midLengthNames ++ "\n" ++
  "  simpa only [List.append_assoc] using h\n\n" ++
  "theorem explicitAllClosed :\n" ++
  "    NGramCPS.All\n" ++
  "      (NGramCPS.ClosedAt (NGram.historyTransition 4 explicitTable)\n" ++
  "        2 2 explicitBlank explicitCertificate)\n" ++
  "      explicitMids := by\n" ++
  "  unfold explicitMids\n" ++
  "  have h := " ++ balancedCombine "explicitAll_append" closedNames ++ "\n" ++
  "  simpa only [List.append_assoc] using h\n\n" ++
  "theorem explicitValid :\n" ++
  "    NGramCPS.Valid (NGram.historyTransition 4 explicitTable) (0 : Fin 4)\n" ++
  "      explicitBlank 2 2 explicitCertificate := by\n" ++
  "  refine And.intro (by decide) <| And.intro (by decide) <|\n" ++
  "    And.intro (by decide) <| And.intro (by decide) <|\n" ++
  "    And.intro ?_ <| And.intro ?_ <| And.intro ?_ <|\n" ++
  "    And.intro ?_ ?_\n" ++
  "  · simpa [explicitCertificate] using explicitMidLengths\n" ++
  "  · simp [explicitCertificate, explicitLeftWords, explicitBlank]\n" ++
  "  · simp [explicitCertificate, explicitRightWords, explicitBlank]\n" ++
  s!"  · simp [explicitCertificate, explicitMids, explicitMids{lastSuffix},\n" ++
  "      explicitBlank]\n" ++
  "  · simpa [explicitCertificate] using explicitAllClosed\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def explicitBuildSource (choices : List GoAction) : String :=
  let modulePrefix := explicitModulePrefix choices
  s!"import {modulePrefix}.Proof\n\n" ++
  "set_option maxRecDepth 10000\n\n" ++
  "namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n\n" ++
  "set_option maxHeartbeats 1600000 in\n" ++
  "theorem explicitBuild :\n" ++
  "    NGram.buildCandidate explicitBlank\n" ++
  "      (NGram.historyTransition 4 explicitTable) 2 2 600 =\n" ++
  "      some explicitCertificate := by\n" ++
  "  rfl\n\n" ++
  "end SetTheory.BusyBeaver.BB4.Certificates.R05A14Guided\n"

def emitExplicitAtomizedPart (choices : List GoAction)
    (index part atomCount : Nat) : IO Unit := do
  let directory := explicitDirectory choices
  let suffix := pad3 index
  let partDirectory := directory ++ s!"/Proof{suffix}"
  let atomDirectory := partDirectory ++ s!"/Part{part}"
  IO.FS.createDirAll atomDirectory
  for atom in List.range atomCount do
    IO.FS.writeFile (atomDirectory ++ s!"/Atom{atom}.lean")
      (explicitProofAtomSource choices index part atom)
  IO.FS.writeFile (partDirectory ++ s!"/Part{part}.lean")
    (explicitAtomizedPartSource choices index part atomCount)

def emitExplicitProof (choices : List GoAction) (chunkCount : Nat) : IO Unit := do
  let directory := explicitDirectory choices
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory ++ "/Proof.lean")
    (explicitProofSource choices chunkCount)

def emitExplicitProofSplits (choices : List GoAction) (chunkCount : Nat) : IO Unit := do
  let directory := explicitDirectory choices
  IO.FS.createDirAll directory
  for index in List.range chunkCount do
    let suffix := pad3 index
    let partDirectory := directory ++ s!"/Proof{suffix}"
    IO.FS.createDirAll partDirectory
    for part in List.range 4 do
      if atomizeExplicitPart choices index part then
        emitExplicitAtomizedPart choices index part 8
      else
        IO.FS.writeFile (partDirectory ++ s!"/Part{part}.lean")
          (explicitProofPartSource choices index part)
    IO.FS.writeFile (directory ++ s!"/Proof{suffix}.lean")
      (explicitSplitProofSource choices index)
  emitExplicitProof choices chunkCount
  IO.FS.writeFile (directory ++ "/Build.lean")
    (explicitBuildSource choices)
  IO.println s!"emitted {chunkCount * 4} explicit proof subshards"

def emitExplicitCertificate (choices : List GoAction)
    (certificate : NGram.AbstractState NGram.HistorySymbol) : IO Unit := do
  let directory := explicitDirectory choices
  IO.FS.createDirAll directory
  let midChunks := chunkList 32 certificate.mids
  for (mids, index) in midChunks.zipIdx do
    IO.FS.writeFile (directory ++ s!"/Data{pad3 index}.lean")
      (explicitDataSource index mids)
  IO.FS.writeFile (directory ++ "/Certificate.lean")
    (explicitCertificateSource choices certificate midChunks.length)
  emitExplicitProofSplits choices midChunks.length
  IO.println s!"emitted {midChunks.length} explicit certificate shards"

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

/-! ## Memory-safe serial plans

The ordinary plan limits structural branching per direct kernel decision.  On
this machine a direct theorem containing multiple history passes can still be
an expensive all-or-nothing reduction.  The smart plan keeps the same branch
budget, but also splits until every direct theorem has at most one history
pass.  Previously diagnosed split boundaries are retained even when their
regenerated trees would otherwise fit the generic limits. -/

def forcedSmartSplits : List (List GoAction) :=
  [ [a11, a00, a07, a01],
    [a11, a02, a12, a06],
    [a11, a02, a15],
    [a11, a02, a15, a08],
    [a11, a02, a15, a09],
    [a11, a02, a15, a12],
    [a11, a02, a15, a13],
    [a11, a03, a09, a12],
    [a11, a03, a09, a12, a00],
    [a11, a03, a09, a12, a06],
    [a11, a03, a09, a12, a09],
    [a11, a03, a09, a12, a10],
    [a11, a03, a09, a12, a12],
    [a11, a03, a12, a01],
    [a11, a03, a12, a01, a00],
    [a11, a03, a12, a01, a06],
    [a11, a03, a12, a01, a08],
    [a11, a03, a12, a13],
    [a11, a03, a12, a13, a00],
    [a11, a03, a12, a13, a06],
    [a11, a03, a12, a13, a08],
    [a11, a03, a13, a02] ]

def isForcedSmartSplit (choices : List GoAction) : Bool :=
  forcedSmartSplits.any fun path => decide (path = choices)

def shouldSmartSplit (threshold : Nat) (choices : List GoAction)
    (tree : Tree) : Bool :=
  decide (threshold < branchCount tree) ||
    decide (1 < historyHintCount tree) ||
    isForcedSmartSplit choices

partial def emitSmartPlan (threshold : Nat) (choices : List GoAction)
    (tree : Tree) : IO Unit := do
  if shouldSmartSplit threshold choices tree then
    match tree with
    | .branch children =>
        if children.length != 16 then
          throw <| IO.userError "guided branch does not have 16 children"
        for pair in (childChoices choices).zip children do
          emitSmartPlan threshold pair.1 pair.2
        let used := (CertWork.after choices).used
        writeOutput choices (parentSource choices used)
    | _ =>
        throw <| IO.userError "smart split is not a certificate branch"
  else
    writeOutput choices (outputSource choices tree)

def planningThreshold : Nat := 20

def _root_.main (args : List String) : IO Unit := do
  if args.head? = some "atomize-explicit" then
    let index <- match args[1]?.bind String.toNat? with
      | some value => pure value
      | none => throw <| IO.userError "expected an explicit shard index"
    let part <- match args[2]?.bind String.toNat? with
      | some value => pure value
      | none => throw <| IO.userError "expected an explicit part index"
    let choiceArgs := args.drop 3
    let choices := choiceArgs.filterMap parseChoice
    if choices.isEmpty || choices.length != choiceArgs.length then
      throw <| IO.userError "expected one or more action indices in 0..15"
    if part >= 4 then
      throw <| IO.userError "expected an explicit part index in 0..3"
    if !atomizeExplicitPart choices index part then
      throw <| IO.userError
        "explicit part is not registered in atomizeExplicitPart"
    let dataPath := System.FilePath.mk <|
      explicitDirectory choices ++ s!"/Data{pad3 index}.lean"
    let dataExists <- dataPath.pathExists
    if !dataExists then
      throw <| IO.userError
        s!"explicit shard data does not exist: {dataPath.toString}"
    emitExplicitAtomizedPart choices index part 8
    IO.println s!"atomized explicit shard {pad3 index} part {part}"
    return
  if args.head? = some "assemble-explicit" then
    let chunkCount <- match args[1]?.bind String.toNat? with
      | some count => pure count
      | none => throw <| IO.userError "expected an explicit shard count"
    if chunkCount = 0 then
      throw <| IO.userError "expected a positive explicit shard count"
    let choiceArgs := args.drop 2
    let choices := choiceArgs.filterMap parseChoice
    if choices.isEmpty || choices.length != choiceArgs.length then
      throw <| IO.userError "expected one or more action indices in 0..15"
    emitExplicitProof choices chunkCount
    IO.println s!"assembled explicit proof from {chunkCount} shards"
    return
  if args.head? = some "split-explicit" then
    let chunkCount <- match args[1]?.bind String.toNat? with
      | some count => pure count
      | none => throw <| IO.userError "expected an explicit shard count"
    if chunkCount = 0 then
      throw <| IO.userError "expected a positive explicit shard count"
    let choiceArgs := args.drop 2
    let choices := choiceArgs.filterMap parseChoice
    if choices.isEmpty || choices.length != choiceArgs.length then
      throw <| IO.userError "expected one or more action indices in 0..15"
    emitExplicitProofSplits choices chunkCount
    return
  if args.head? = some "emit-explicit" then
    let choiceArgs := args.drop 1
    let choices := choiceArgs.filterMap parseChoice
    if choices.isEmpty || choices.length != choiceArgs.length then
      throw <| IO.userError "expected one or more action indices in 0..15"
    let table := (CertWork.after choices).table
    let blank : NGram.HistorySymbol := { bit := false, history := [] }
    match NGram.buildCandidate blank (NGram.historyTransition 4 table) 2 2 600 with
    | none => throw <| IO.userError "history-4x2 candidate construction failed"
    | some certificate => emitExplicitCertificate choices certificate
    return
  if args.head? = some "cert-stats" then
    let choiceArgs := args.drop 1
    let choices := choiceArgs.filterMap parseChoice
    if choices.isEmpty || choices.length != choiceArgs.length then
      throw <| IO.userError "expected one or more action indices in 0..15"
    let table := (CertWork.after choices).table
    let blank : NGram.HistorySymbol := { bit := false, history := [] }
    match NGram.buildCandidate blank (NGram.historyTransition 4 table) 2 2 600 with
    | none => IO.println "no certificate"
    | some certificate =>
        IO.println s!"leftWords: {certificate.leftWords.length}"
        IO.println s!"rightWords: {certificate.rightWords.length}"
        IO.println s!"mids: {certificate.mids.length}"
    return
  if args = ["smart-a11"] then
    for action in actionList do
      let choices := [a11, action]
      let tree <- match build (CertWork.after choices) with
        | .ok tree => pure tree
        | .error message => throw <| IO.userError message
      emitSmartPlan planningThreshold choices tree
      IO.println s!"planned {moduleSuffix choices}"
    let choices := [a11]
    writeOutput choices (parentSource choices (CertWork.after choices).used)
    IO.println "planned A11"
    return
  let planning := args.head? = some "plan"
  let splitting := args.head? = some "split"
  let atomizing := args.head? = some "atoms"
  let smartPlanning := args.head? = some "smart"
  let listingPasses := args.head? = some "passes"
  let listingTable := args.head? = some "table"
  let checkingPass := args.head? = some "pass"
  let requestedPass := if checkingPass then args[1]?.bind String.toNat? else none
  let choiceArgs :=
    if checkingPass then args.drop 2
    else if planning || splitting || atomizing || smartPlanning ||
        listingPasses || listingTable then
      args.drop 1
    else args
  let choices := choiceArgs.filterMap parseChoice
  if choices.isEmpty || choices.length != choiceArgs.length then
    throw <| IO.userError "expected one or more action indices in 0..15"
  if listingPasses then
    let table := (CertWork.after choices).table
    for (index, pass) in indexedPasses do
      if pass.check table then
        IO.println s!"{index}: {hintName index}"
    return
  if listingTable then
    let work := CertWork.after choices
    for state in List.finRange 4 do
      for bit in [false, true] do
        let value := match work.table state bit with
          | none => "--"
          | some action => actionName action
        IO.println s!"{state.val},{bit}: {value}"
    return
  if checkingPass then
    let work := CertWork.after choices
    let table := work.table
    for (index, pass) in indexedPasses do
      if requestedPass = some index then
        IO.println s!"{index}: {hintName index}: {pass.check table}"
        return
    if requestedPass = some 13 then
      IO.println s!"13: Guided.Certificate.sporadic: {sporadicLeaf table work.cfg}"
      return
    if requestedPass = some 14 then
      let result := Certificates.R05A14HistoryInvariant.leaf table work.cfg
      IO.println s!"14: Guided.Certificate.r05A14HistoryInvariant: {result}"
      return
    if requestedPass = some 15 then
      let result :=
        Certificates.R05A14HistoryInvariantA15A09A03A02A04.leaf table work.cfg
      IO.println s!"15: Guided.Certificate.r05A14A15Pump: {result}"
      return
    throw <| IO.userError "expected a pass index in 1..15"
  let tree <- match build (CertWork.after choices) with
    | .ok tree => pure tree
    | .error message => throw <| IO.userError message
  if smartPlanning then
    emitSmartPlan planningThreshold choices tree
  else if planning || splitting || atomizing then
    emitPlan (if atomizing then 0 else if splitting then 1 else 20) choices tree
  else
    writeOutput choices (outputSource choices tree)
  IO.println s!"generated {moduleSuffix choices}"

end SetTheory.BusyBeaver.BB4.GenerateR05A14Guided
