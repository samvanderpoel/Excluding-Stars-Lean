import Lean
import DenseGraph
import InducedStars

/-!
Audit the actual transitive axioms of every declaration defined by the two
project libraries, including private declarations and generated auxiliaries.
The declaring module, rather than a namespace prefix, identifies project code.

Lean 4.34's collectAxioms uses axiom information computed from kernel declaration
types and bodies during compilation. That computation sees private bodies and
uses a shared cache across a module's declarations; imported dependency results
are stored in the compiled module. Thus this audit does not repeatedly traverse
the same large proof closure, and private intermediary proofs cannot hide axioms.

Run from the repository root: lake env lean verification/Audit.lean
-/

open Lean Elab Command

set_option maxHeartbeats 0

private def isProjectModule (name : Name) : Bool :=
  (`DenseGraph).isPrefixOf name || (`InducedStars).isPrefixOf name

run_cmd do
  let source ← IO.FS.readFile "verification/allowed-axioms.txt"
  let mut allowed : NameSet := {}
  for line in source.splitOn "\n" do
    let entry := line.trimAscii.toString
    if entry.isEmpty || entry.startsWith "#" then continue
    let name := entry.toName
    if name == `sorryAx then
      throwError "sorryAx must never appear in the axiom allowlist"
    if allowed.contains name then
      throwError m!"duplicate allowed axiom: {name}"
    allowed := allowed.insert name
  if allowed.isEmpty then throwError "empty axiom allowlist"

  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let declarations := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
        if isProjectModule moduleNames[idx.toNat]! then names.push name else names
    | none => names
  if declarations.isEmpty then throwError "no project declarations found to audit"
  let mut used : NameSet := {}
  let mut privateCount : Nat := 0
  let mut failed := false
  for name in declarations do
    if isPrivateName name then privateCount := privateCount + 1
    let axioms ← collectAxioms name
    for axiomName in axioms do
      used := used.insert axiomName
      if axiomName == `sorryAx || !allowed.contains axiomName then
        logError m!"{name} depends on unapproved axiom {axiomName}"
        failed := true
  if failed then throwError "axiom audit failed"
  let axioms := used.toArray.qsort Name.lt
  logInfo m!"Axiom audit passed: {declarations.size} project declarations ({privateCount} private), {axioms.size} assumptions."
  for name in axioms do logInfo m!"  {name}"
