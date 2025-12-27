/-
File: UniversalityTheorem/Progress.lean

Purpose:
  Discover *obligations* that are still placeholders:
    (1) anything that depends on `sorryAx`, and
    (2) any `opaque` or `axiom` declaration in the target namespace
        (i.e. a constant with no body/value).
  Then analyze dependencies and print:
    • a prioritized global TODO list, and
    • a target-specific section: “Target theorem X still depends on these obligations”.

Usage:
  Import this file; it will print the reports at compile time.
-/
import UniversalityTheorem.EtterEq
import UniversalityTheorem.Scaffold
import UniversalityTheorem.Universality

import Mathlib.Data.List.Sort  -- for List.mergeSort

open Lean Elab Command Meta

namespace UniversalityTheorem.Progress

/-- Why a declaration is considered incomplete. -/
inductive IncompleteReason where
  | usesSorry
  | isOpaque
  | isAxiom
  deriving Inhabited, BEq

/-- A declaration that is incomplete, along with its dependencies. -/
structure IncompleteDecl where
  name : Name
  reason : IncompleteReason
  /-- Other incomplete declarations this one depends on. -/
  blockedBy : List Name
  /-- Number of other incomplete declarations that depend on this one. -/
  blocking : Nat := 0
  deriving Inhabited

/-- Check if a declaration transitively depends on `sorryAx`. -/
def usesSorry (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some _ =>
    let (_, state) := CollectAxioms.collect n env {}
    state.axioms.contains ``sorryAx

/-- Classify whether `n` is an "obligation placeholder" (axiom/opaque) in the env. -/
def obligationReason? (env : Environment) (n : Name) : Option IncompleteReason :=
  match env.find? n with
  | none => none
  | some cinfo =>
    -- `opaque foo : T` produces `ConstantInfo.opaqueInfo`
    match cinfo with
    | .opaqueInfo _ => some .isOpaque
    -- `axiom foo : T` produces `ConstantInfo.axiomInfo`
    | .axiomInfo _ => some .isAxiom
    | _            => none

/-- Decide if `n` is incomplete, returning the reason. -/
def incompleteReason? (env : Environment) (n : Name) : Option IncompleteReason :=
  if usesSorry env n then
    some .usesSorry
  else
    obligationReason? env n

/-- Get all incomplete declaration names in a namespace (sorry-dependent OR axiom/opaque). -/
def findIncompleteDecls (env : Environment) (ns : Name) : List (Name × IncompleteReason) :=
  env.constants.fold (init := []) fun acc name _ =>
    if ns.isPrefixOf name then
      match incompleteReason? env name with
      | some r => (name, r) :: acc
      | none   => acc
    else
      acc

/-- Get the direct constant dependencies of a declaration. -/
def getDirectDeps (env : Environment) (n : Name) : List Name :=
  match env.find? n with
  | none => []
  | some cinfo =>
    let fromType := cinfo.type.getUsedConstants.toList
    let fromValue := match cinfo.value? with
      | some v => v.getUsedConstants.toList
      | none => []
    (fromType ++ fromValue).eraseDups

/-- Check if a name is in a list. -/
def nameInList (n : Name) (l : List Name) : Bool :=
  l.any (· == n)

/--
Given a set of incomplete declarations, compute which incomplete decls
each one depends on (using fuel to ensure termination).
-/
def computeBlockedBy
    (env : Environment)
    (incomplete : List Name)
    (reasons : Name → IncompleteReason)
    : List IncompleteDecl :=
  incomplete.map fun n =>
    let rec loop (fuel : Nat) (frontier : List Name) (visited : List Name)
                 (found : List Name) : List Name :=
      match fuel with
      | 0 => found
      | fuel' + 1 =>
        match frontier with
        | [] => found
        | d :: rest =>
          if nameInList d visited then
            loop fuel' rest visited found
          else
            let visited' := d :: visited
            let newFound :=
              if nameInList d incomplete && d != n then d :: found else found
            let newDeps := getDirectDeps env d
            loop fuel' (rest ++ newDeps) visited' newFound
    let blockers := loop 2000 (getDirectDeps env n) [] []
    { name := n, reason := reasons n, blockedBy := blockers.eraseDups }

/-- Compute the "blocking" count: how many other incomplete decls depend on each one. -/
def computeBlockingCounts (decls : List IncompleteDecl) : List IncompleteDecl :=
  decls.map fun d =>
    let count := decls.foldl (init := 0) fun acc other =>
      if nameInList d.name other.blockedBy then acc + 1 else acc
    { d with blocking := count }

def reasonTag : IncompleteReason → String
  | .usesSorry => "SORRY"
  | .isOpaque  => "OPAQUE"
  | .isAxiom   => "AXIOM"

/-- Comparator: return true if `a` should come before `b` (higher priority). -/
def higherPriority (a b : IncompleteDecl) : Bool :=
  if a.blockedBy.length != b.blockedBy.length then
    a.blockedBy.length < b.blockedBy.length
  else if a.blocking != b.blocking then
    a.blocking > b.blocking
  else
    a.name.toString < b.name.toString

/--
Sort incomplete declarations so that:
1. Declarations with no blockers come first (can be worked on now)
2. Among those, declarations that block more others have higher priority
3. Then declarations with 1 blocker, etc.
-/
def sortByPriority (decls : List IncompleteDecl) : List IncompleteDecl :=
  decls.mergeSort higherPriority

/-- Format a single TODO item with its dependency info. -/
def formatTodo (idx : Nat) (d : IncompleteDecl) : String :=
  let status :=
    if d.blockedBy.isEmpty then "READY" else s!"blocked by {d.blockedBy.length}"
  let impact := if d.blocking > 0 then s!" (blocks {d.blocking} others)" else ""
  let blockerList :=
    if d.blockedBy.isEmpty then ""
    else "\n      <- " ++ String.intercalate ", " (d.blockedBy.map toString)
  s!"{idx + 1}. {d.name} [{reasonTag d.reason}]{impact}\n      [{status}]{blockerList}"

/-- Enumerate a list with indices. -/
def enumerate {α : Type} (l : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: xs => (i, x) :: go (i + 1) xs
  go 0 l

/-- Format the complete TODO list. -/
def formatTodoList (decls : List IncompleteDecl) : String :=
  if decls.isEmpty then
    "No incomplete declarations found!"
  else
    let ready := decls.filter (·.blockedBy.isEmpty)
    let blocked := decls.filter (·.blockedBy.length > 0)
    let header := s!"=== UniversalityTheorem: \
        {decls.length} obligations/incomplete declarations ===\n"
    let readySection :=
      if ready.isEmpty then ""
      else
        let items := enumerate ready |>.map fun (i, d) => formatTodo i d
        "\n-- Ready to work on --\n" ++ String.intercalate "\n\n" items ++ "\n"
    let blockedSection :=
      if blocked.isEmpty then ""
      else
        let items := enumerate blocked |>.map fun (i, d) =>
          formatTodo (ready.length + i) d
        "\n-- Blocked (in priority order) --\n" ++ String.intercalate "\n\n" items
    header ++ readySection ++ blockedSection

/-- Run the global analysis pipeline. -/
def analyze (env : Environment) (ns : Name) : String :=
  let pairs := findIncompleteDecls env ns
  let names := pairs.map (·.1)
  let reasonMap : Std.HashMap Name IncompleteReason :=
    pairs.foldl (init := {}) fun m (n, r) => m.insert n r
  let reasons : Name → IncompleteReason :=
    fun n => (reasonMap.get? n).getD .usesSorry
  let withBlockedBy := computeBlockedBy env names reasons
  let withCounts := computeBlockingCounts withBlockedBy
  let sorted := sortByPriority withCounts
  formatTodoList sorted

/-- Dependency closure (transitive) of a target declaration. -/
def depClosure (env : Environment) (target : Name) : List Name :=
  let rec loop (fuel : Nat) (frontier : List Name) (visited : List Name) : List Name :=
    match fuel with
    | 0 => visited
    | fuel' + 1 =>
      match frontier with
      | [] => visited
      | d :: rest =>
        if nameInList d visited then
          loop fuel' rest visited
        else
          let visited' := d :: visited
          let deps := getDirectDeps env d
          loop fuel' (rest ++ deps) visited'
  loop 4000 [target] []

/-- Format the target-specific report section. -/
def formatTargetSection
    (target : Name)
    (deps : List Name)
    (incomplete : List Name)
    (reasons : Name → IncompleteReason)
    : String :=
  let hits := deps.filter (fun n => nameInList n incomplete) |>.eraseDups
  if hits.isEmpty then
    -- string gap to keep linters happy if you care
    s!"\n=== Target: {target} ===\n\
       Target does not depend on any tracked obligations.\n"
  else
    let lines :=
      (hits.mergeSort (fun a b => a.toString < b.toString)).map (fun n =>
        s!"- {n} [{reasonTag (reasons n)}]"
      )
    s!"\n=== Target: {target} ===\n\
       Target still depends on these obligations:\n"
      ++ String.intercalate "\n" lines ++ "\n"

/-- Run the full analysis pipeline, plus a target report. -/
def analyzeWithTarget (env : Environment) (ns : Name) (target : Name) : String :=
  let pairs := findIncompleteDecls env ns
  let names := pairs.map (·.1)
  let reasonMap : Std.HashMap Name IncompleteReason :=
    pairs.foldl (init := {}) fun m (n, r) => m.insert n r
  let reasons : Name → IncompleteReason :=
    fun n => (reasonMap.get? n).getD .usesSorry
  let withBlockedBy := computeBlockedBy env names reasons
  let withCounts := computeBlockingCounts withBlockedBy
  let sorted := sortByPriority withCounts
  let global := formatTodoList sorted
  let deps := depClosure env target
  let targetSection := formatTargetSection target deps names reasons
  global ++ targetSection

end UniversalityTheorem.Progress

open UniversalityTheorem.Progress in
/-- Command to run the progress analysis at compile time. -/
elab "#show_progress " ns:ident : command => do
  let env ← getEnv
  let nsName := ns.getId
  let output := analyze env nsName
  logInfo m!"{output}"

open UniversalityTheorem.Progress in
/-- Command to run the progress analysis + a target report at compile time. -/
elab "#show_progress_target " ns:ident "," target:ident : command => do
  let env ← getEnv
  let nsName := ns.getId
  let targetName := target.getId
  let output := analyzeWithTarget env nsName targetName
  logInfo m!"{output}"

-- Run the analysis (global TODO list only)
#show_progress UniversalityTheorem

-- Run the analysis + target report
#show_progress_target UniversalityTheorem, UniversalityTheorem.slang_universality_ZFC
