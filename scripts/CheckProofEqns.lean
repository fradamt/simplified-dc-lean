import Lean
import Lake.Toml.Load
import AvailableChainCheckSupport.GeneratedOwner

open Lean AvailableChainCheckSupport

/-! Check (d), BUILD §7.2 B3a and §7.3: equation-like exports of proof modules.
Source: `claude-files/a0/check-sketches/CheckProofEqns.lean`.

Run from the repository root after the default targets have been built:
  lake build AvailableChainCheckSupport
  lake env lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt
  lake env lean --run scripts/CheckProofEqns.lean --write-baseline

Roots come from `defaultTargets` in lakefile.toml. Extra command-line modules
are additional roots. Proof source modules are also imported, so a proof
module need not appear in its library facade to be checked. Missing compiled
modules are errors; this script does not build or use the network.

Only `.exported` module data is scanned. Each module's own constant list is
checked, because the combined constant map keeps only the first module index
for a name that more than one module exports. Private matcher copies are
included. The baseline key is `<exporting module> <generated constant>`;
diagnostics also give the owner from the shared GeneratedOwner API. An owner
in another library does not exempt an export in a proof module.
If an owner's declaration is private, its module's private data is loaded
only for the owner lookup. That data never supplies the list of findings.

Kit and FGSAProofs submodules are proof modules except facades, Tests,
KitV2.ClockLaws, and the KitFG definition list used by checks (b) and (e).
Gen findings cannot be accepted by a baseline. Baseline generation writes
only non-Gen findings and returns 1 if there are Gen findings. The initial
baseline records the existing exports at 03bd912, including FGSARun.
Exit codes: 0 accepted; 1 unaccepted exports; 2 usage or input error.
-/

def baselinePath : System.FilePath := "scripts/baselines/check-proof-eqns.txt"

def eqLike (s : String) : Bool :=
  s == "eq_def" || s == "splitter" || s == "eq_unfold" || s == "induct" ||
  s == "fun_cases" ||
    (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit)

def dataLines (path : System.FilePath) : IO (List String) := do
  return (← IO.FS.lines path).toList.filterMap fun line =>
    let line := (line.splitOn "#").head!.trimAscii.toString
    if line.isEmpty then none else some line

def kitFGDefinitions : IO (Std.HashSet Name) := do
  let names ← dataLines "scripts/baselines/kitfg-def-modules.txt"
  return Std.HashSet.ofList <| names.map fun s =>
    (if s.startsWith "AvailableChainKitFG." then s else "AvailableChainKitFG." ++ s).toName

def isProofModule (definitions : Std.HashSet Name) (m : Name) : Bool :=
  let parts := m.components
  parts.contains `Proofs ||
    (!parts.contains `Tests && !definitions.contains m && m != `AvailableChainKitV2.ClockLaws &&
      parts.length > 1 &&
        [`AvailableChainKit, `AvailableChainKitV2, `AvailableChainKitFG,
          `AvailableChainFGSAProofs].contains parts.head!)

def tomlString (v : Lake.Toml.Value) : IO String :=
  match v with
  | .string _ s => pure s
  | _ => throw <| IO.userError "lakefile.toml: expected a string"

def defaultRoots (definitions : Std.HashSet Name) : IO (Array Name) := do
  let path := "lakefile.toml"
  let input ← IO.FS.readFile path
  let table ← (Lake.Toml.loadToml (Parser.mkInputContext input path)).toIO fun errors =>
    IO.userError s!"cannot parse lakefile.toml: {errors.toList.length} errors"
  let some (.array _ targets) := table.find? `defaultTargets |
    throw <| IO.userError "lakefile.toml: defaultTargets must be an array"
  if targets.isEmpty then throw <| IO.userError "lakefile.toml: no default targets"
  let some (.array _ libraries) := table.find? `lean_lib |
    throw <| IO.userError "lakefile.toml: no lean_lib tables"
  let mut roots := #[]
  for target in targets do
    let name ← tomlString target
    roots := roots.push name.toName
    let mut found := false
    for library in libraries do
      let .table _ library := library | continue
      let some n := library.find? `name | continue
      unless (← tomlString n) == name do continue
      found := true
      let srcDir ← match library.find? `srcDir with
        | some v => System.FilePath.mk <$> tomlString v
        | none => pure "."
      let dir := srcDir / name
      unless ← dir.isDir do continue
      for file in ← dir.walkDir do
        unless file.extension == some "lean" do continue
        let parts := (file.withExtension "").components.drop srcDir.components.length
        let m := parts.foldl Name.str .anonymous
        if isProofModule definitions m then roots := roots.push m
    unless found do throw <| IO.userError s!"default target is not a lean_lib: {name}"
  return (Std.HashSet.ofList roots.toList).toArray.qsort Name.lt

/-- The shared API covers equations and splitters. The other three checked
suffixes are not in generatedSuffix; their declared prefix is the owner. -/
def equationOwner (env : Environment) (n : Name) : Option Name :=
  generatedOwner env n <|> match n with
    | .str pre s =>
      if s == "eq_unfold" || s == "induct" || s == "fun_cases" then declaredName env pre
      else none
    | _ => none

structure Finding where
  mod : Name
  constant : Name
  owner : Option Name

def Finding.key (finding : Finding) : String := s!"{finding.mod} {finding.constant}"

def findings (env : Environment) (definitions : Std.HashSet Name) : Array Finding := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless isProofModule definitions m do continue
    for n in env.header.moduleData[i]!.constNames do
      let .str _ s := n | continue
      unless eqLike s do continue
      out := out.push { mod := m, constant := n, owner := equationOwner env n }
  return out.qsort fun a b => a.key < b.key

/-- Some exported equations refer to private definitions or tactic matchers
whose declarations are not exported. Add their compiled declarations to a
lookup environment, so GeneratedOwner can resolve them without importing
the private data of the full dependency tree. Keep the exported scan intact. -/
def resolveOwners (env : Environment) (rows : Array Finding) : IO (Array Finding) := do
  let missing := rows.filter (·.owner.isNone)
  if missing.isEmpty then return rows
  let modules := Std.HashSet.ofList (missing.toList.map (·.mod))
  let prefixes := Std.HashSet.ofList (missing.toList.map (·.constant.getPrefix))
  let mut lookup := env
  for m in modules.toArray do
    let path ← findOLean m
    let parts ← readModuleDataParts
      #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path]
    for (data, _) in parts do
      for info in data.constants do
        unless prefixes.contains info.name && !lookup.contains info.name do continue
        let addition ← lookup.addConstAsync info.name (.ofConstantInfo info) (reportExts := false)
        addition.commitConst lookup (some info) (some info)
        addition.commitCheckEnv lookup
        lookup := addition.mainEnv
  return rows.map fun row =>
    { row with owner := row.owner <|> equationOwner lookup row.constant }

structure CheckOptions where
  roots : Array Name := #[]
  baseline : Option System.FilePath := none
  write : Bool := false

def parseArgs : List String → CheckOptions → Except String CheckOptions
  | [], options =>
    if options.write && options.baseline.isSome then
      .error "--write-baseline and --baseline cannot be used together"
    else .ok options
  | "--baseline" :: path :: rest, options =>
    if path.startsWith "--" || options.baseline.isSome then .error "invalid --baseline"
    else parseArgs rest { options with baseline := some path }
  | "--write-baseline" :: rest, options => parseArgs rest { options with write := true }
  | arg :: rest, options =>
    if arg.startsWith "-" then .error s!"unknown or incomplete option: {arg}"
    else parseArgs rest { options with roots := options.roots.push arg.toName }

def runCheck (options : CheckOptions) : IO UInt32 := do
  let definitions ← kitFGDefinitions
  let roots := (← defaultRoots definitions) ++ options.roots
  let baseline := Std.HashSet.ofList (← match options.baseline with
    | some path => dataLines path
    | none => pure [])
  initSearchPath (← findSysroot)
  let env ← importModules (roots.map fun m => { module := m }) {} (level := .exported)
  let rows ← resolveOwners env (findings env definitions)
  let mut bad := 0
  let mut legacy : Array String := #[]
  let mut counts : Std.HashMap Name Nat := {}
  for row in rows do
    let lib := row.mod.components.head!
    counts := counts.insert lib (counts[lib]?.getD 0 + 1)
    let genModule := (`AvailableChainGeneric).isPrefixOf row.mod
    if !genModule then legacy := legacy.push row.key
    if genModule || (!options.write && !baseline.contains row.key) then
      let owner := row.owner.map toString |>.getD "UNRESOLVED"
      IO.println s!"EQ EXPORT {row.key} OWNER {owner}"
      bad := bad + 1
  if options.write then
    IO.FS.writeFile baselinePath (String.join <| legacy.toList.map (· ++ "\n"))
    IO.println s!"CheckProofEqns: wrote {legacy.size} legacy entries to {baselinePath}"
  let proofModules := env.header.moduleNames.filter (isProofModule definitions)
  IO.println s!"CheckProofEqns: {proofModules.size} proof modules; {rows.size} exports; {bad} unaccepted"
  for lib in counts.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    IO.println s!"CheckProofEqns: {lib.1} {lib.2}"
  let gen := rows.filter (fun row => (`AvailableChainGeneric).isPrefixOf row.mod)
  IO.println s!"CheckProofEqns: Gen {gen.size} exports"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error error => IO.eprintln s!"CheckProofEqns: {error}"; return 2
  | .ok options =>
    try runCheck options catch error =>
      IO.eprintln s!"CheckProofEqns: {error}"
      return 2
