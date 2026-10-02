import Lean
open Lean

/-! FG-SA old-read audit (fg5-rulings STOP 6 and ruling 7, lead 2026-10-02).

The stage-3 switch (J4) moves FG-SA from the old SimplexFG store fold to the
window fold. After J4 no old `on_block`, `update_finality`, `acceptViable`,
`HeadFields.ofBlock` or `rowValidFor` may stay in the ACTIVE FG-SA path. The
window fold has declarations with the same short names (`Window.on_block`, …),
so a text search cannot tell an old read from a new one. This audit reads the
COMPILED constants and matches full names.

Active path: every module of the source directories `AvailableChainFGSA`,
`AvailableChainFGSAClaims`, `AvailableChainFGSAProofs` and
`AvailableChainFGSARun` (and their root files), except modules under a `Tests`
directory.

A declaration of the active path READS OLD when its type or value names
- an old constant (directly), or
- a constant outside the active path whose type, or whose value if it is a
  definition, names an old constant (for example a KitFG lemma about the old
  `on_block`).
Auxiliary constants (`foo.proof_1`, `foo.match_1`, `foo.eq_1`, …) count for
their declaration `foo`; a private name counts under its user name.

Old constants: the five names of STOP 6 below (a name that the tree no longer
has cannot be read and is reported as absent), plus every `old <name>` line of
the data file (that name must exist). Data lines can add old names; only this
script can remove one.

Data file (default `scripts/baselines/fgsa-old-reads.txt`), one entry per line:
  `allow <declaration> # <reason>`   an old read that may stay for now;
  `old <constant> # <reason>`        one more old constant;
blank lines and lines that start with `#` are comments. Every entry needs a
reason after ` # `.

Result: every reading declaration must have an `allow` line, and every `allow`
line must name a reading declaration (a stale line fails, so the list only
shrinks with the code).

Run: `lake env lean --run scripts/CheckFGSAOldReads.lean [--data F] [--write]
[--controls]`. `--write` rewrites the `allow` lines from the current reads
(it keeps the reason of a kept line) and exits 0. `--controls` also runs the
negative controls in the same environment: a planted direct old read, a planted
read through an external lemma about the old fold, a dropped `allow` line, and
an extra `allow` line must each be detected.
Exit codes: 0 pass; 1 an unlisted read, a stale or duplicate line, or a
control that is not detected; 2 a usage, data or setup error. -/

def libs : List String :=
  ["AvailableChainFGSA", "AvailableChainFGSAClaims", "AvailableChainFGSAProofs",
    "AvailableChainFGSARun"]

/-- STOP 6 of fg5-rulings. -/
def floorOld : List Name :=
  [`AvailableChain.SimplexFG.on_block, `AvailableChain.SimplexFG.update_finality,
    `AvailableChain.SimplexFG.acceptViable, `AvailableChain.SimplexFG.HeadFields.ofBlock,
    `AvailableChain.FGSA.rowValidFor]

/-- An external lemma about the old fold, for the indirect negative control. -/
def indirectFixture : Name := `AvailableChain.KitFG.on_block_F_mono

def activeModules : IO (Array Name) := do
  let mut out := #[]
  for lib in libs do
    let dir : System.FilePath := lib
    unless ← dir.pathExists do
      throw <| IO.userError s!"missing source directory {lib}"
    if ← (System.FilePath.mk (lib ++ ".lean")).pathExists then
      out := out.push (Name.mkSimple lib)
    for f in ← dir.walkDir do
      if f.extension.map String.toLower == some "lean" then
        let parts := (f.withExtension "").components.drop dir.components.length
        if parts.contains "Tests" then continue
        out := out.push (parts.foldl (fun n s => Name.str n s) (Name.mkSimple lib))
  return out

def isAuxComp (s : String) : Bool :=
  s.startsWith "_" ||
    ["eq_def", "eq_unfold", "induct", "mutual_induct", "fun_cases", "sizeOf_spec"].contains s ||
    ["proof_", "match_", "eq_", "eqn_", "spec_"].any fun p =>
      s.startsWith p && s.length > p.length && (s.drop p.length).all Char.isDigit

partial def declKey (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  match n with
  | .str p s => if !p.isAnonymous && isAuxComp s then declKey p else n
  | .num p _ => if p.isAnonymous then n else declKey p
  | .anonymous => n

def namesIn (ci : ConstantInfo) (withValue : Bool) : Array Name :=
  match (if withValue then ci.value? else none) with
  | some v => ci.type.getUsedConstants ++ v.getUsedConstants
  | none => ci.type.getUsedConstants

/-- The old reads of one active constant, as printable reasons. -/
def readsOf (env : Environment) (active : NameSet) (old : NameSet) (ci : ConstantInfo) :
    Array String := Id.run do
  let mut out := #[]
  for c in namesIn ci true do
    if old.contains c then
      out := out.push s!"{c}"
    else if !active.contains c then
      if let some ce := env.find? c then
        let isDef := ce matches .defnInfo _
        let hits := (namesIn ce isDef).filter old.contains
        unless hits.isEmpty do
          out := out.push s!"{hits.toList.head!} (via {c})"
  return out

structure Data where
  allow : Array (Name × String) := #[]
  old : Array (Name × String) := #[]
  bad : Array String := #[]

def parseData (text : String) : Data := Id.run do
  let mut d : Data := {}
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let (body, reason) := match line.splitOn " # " with
      | b :: r :: rs => (b.trimAscii.toString, (" # ".intercalate (r :: rs)).trimAscii.toString)
      | _ => (line, "")
    let ws := (body.splitOn " ").filter (· ≠ "")
    match ws with
    | ["allow", n] =>
        if reason.isEmpty then d := { d with bad := d.bad.push s!"no reason: {line}" }
        d := { d with allow := d.allow.push (n.toName, reason) }
    | ["old", n] =>
        if reason.isEmpty then d := { d with bad := d.bad.push s!"no reason: {line}" }
        d := { d with old := d.old.push (n.toName, reason) }
    | _ => d := { d with bad := d.bad.push s!"bad line: {line}" }
  return d

/-- Unlisted reads and stale or duplicate allow lines. -/
def compare (reads : Std.HashMap Name (Array String)) (allow : Array Name) :
    Array String × Array String := Id.run do
  let mut unlisted := #[]
  for (k, why) in reads.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    unless allow.contains k do
      unlisted := unlisted.push s!"OLD READ NOT LISTED: {k} reads {why.toList}"
  let mut stale := #[]
  let mut seen : NameSet := {}
  for k in allow do
    if seen.contains k then stale := stale.push s!"DUPLICATE ALLOW LINE: {k}"
    seen := seen.insert k
    unless reads.contains k do
      stale := stale.push s!"STALE ALLOW LINE (no old read now; remove it): {k}"
  return (unlisted, stale)

def header : String :=
  "# FG-SA old-read audit data (scripts/CheckFGSAOldReads.lean; fg5-rulings STOP 6, ruling 7).\n\
   # allow <declaration> # <reason>: an old read that may stay for now. J4 and J6 remove lines.\n\
   # old <constant> # <reason>: one more old constant (tightening only).\n\
   # A new old read in the active FG-SA path fails; a stale allow line fails.\n"

def main (args : List String) : IO UInt32 := do
  let usage := "USAGE: lake env lean --run scripts/CheckFGSAOldReads.lean \
    [--data F] [--write] [--controls]"
  let mut rest := args
  let mut path : System.FilePath := "scripts/baselines/fgsa-old-reads.txt"
  let mut write := false
  let mut controls := false
  while !rest.isEmpty do
    match rest with
    | "--data" :: f :: r => path := f; rest := r
    | "--write" :: r => write := true; rest := r
    | "--controls" :: r => controls := true; rest := r
    | _ => IO.eprintln usage; return 2
  let data := parseData (← IO.FS.readFile path)
  unless data.bad.isEmpty do
    for b in data.bad do IO.println s!"DATA ERROR: {b}"
    return 2
  let mods ← activeModules
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({ module := · })) {}
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let isActive (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => modSet.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let mut old : NameSet := {}
  for n in floorOld do
    if env.contains n then old := old.insert n
    else IO.println s!"note: old constant {n} is absent (nothing can read it)"
  for (n, _) in data.old do
    unless env.contains n do
      IO.println s!"DATA ERROR: old constant {n} does not exist"
      return 2
    old := old.insert n
  let cs := env.constants.toList.filter (fun (n, _) => isActive n)
  if cs.isEmpty then
    IO.eprintln "NO ACTIVE CONSTANTS FOUND"
    return 2
  let active : NameSet := cs.foldl (fun s (n, _) => s.insert n) {}
  let mut reads : Std.HashMap Name (Array String) := {}
  let mut home : Std.HashMap Name Name := {}
  for (_, ci) in cs do
    let why := readsOf env active old ci
    unless why.isEmpty do
      let k := declKey ci.name
      reads := reads.insert k ((reads.getD k #[]) ++ why)
      if let some idx := env.getModuleIdxFor? ci.name then
        home := home.insert k env.header.moduleNames[idx.toNat]!
  let allow := data.allow.map (·.1)
  IO.println s!"scanned {cs.length} constants of {mods.size} active modules; \
    {old.size} old constants; {reads.size} reading declarations; {allow.size} allow lines"
  if write then
    let keep : Std.HashMap Name String := data.allow.foldl (fun m (n, r) => m.insert n r) {}
    let modOf (k : Name) : String := s!"{home.getD k .anonymous}"
    let mut out := header
    for (n, r) in data.old do out := out ++ s!"old {n} # {r}\n"
    for k in (reads.toArray.map (·.1)).qsort (fun a b => a.toString < b.toString) do
      let r := keep.getD k s!"pre-J4 baseline 2026-10-02 ({modOf k})"
      out := out ++ s!"allow {k} # {r}\n"
    IO.FS.writeFile path out
    IO.println s!"wrote {path}"
    return 0
  let (unlisted, stale) := compare reads allow
  for s in unlisted ++ stale do IO.println s
  let mut failed := !(unlisted.isEmpty && stale.isEmpty)
  if controls then
    let some o := floorOld.find? env.contains | do
      IO.println "CONTROL SETUP FAIL: no old constant exists"; return 2
    unless env.contains indirectFixture do
      IO.println s!"CONTROL SETUP FAIL: {indirectFixture} does not exist"
      return 2
    let mk (n v : Name) : ConstantInfo :=
      ConstantInfo.defnInfo
        { name := n
          levelParams := []
          type := mkConst `Nat
          value := mkConst v
          hints := .opaque
          safety := .safe }
    let direct := mk `OldReadControl.direct o
    let viaLemma := mk `OldReadControl.indirect indirectFixture
    let mut planted := reads
    for ci in [direct, viaLemma] do
      let why := readsOf env active old ci
      planted := planted.insert ci.name why
      if why.isEmpty then
        IO.println s!"NEGATIVE CONTROL NOT DETECTED: {ci.name} is not an old read"
        failed := true
    let (u, _) := compare planted allow
    for n in [direct.name, viaLemma.name] do
      if u.any (·.startsWith s!"OLD READ NOT LISTED: {n} ") then
        IO.println s!"control planted {n}: detected"
      else
        IO.println s!"NEGATIVE CONTROL NOT DETECTED: planted {n}"
        failed := true
    if let some first := allow[0]? then
      let (u, _) := compare reads (allow.erase first)
      if u.any (·.startsWith s!"OLD READ NOT LISTED: {first} ") then
        IO.println s!"control dropped allow line {first}: detected"
      else
        IO.println s!"NEGATIVE CONTROL NOT DETECTED: dropped allow line {first}"
        failed := true
    else
      IO.println "control dropped allow line: skipped (no allow lines)"
    let (_, st) := compare reads (allow.push `OldReadControl.stale)
    if st.any (·.endsWith "OldReadControl.stale") then
      IO.println "control stale allow line: detected"
    else
      IO.println "NEGATIVE CONTROL NOT DETECTED: stale allow line"
      failed := true
  IO.println s!"FGSA old-read audit: {if failed then "FAIL" else "PASS"}"
  return if failed then 1 else 0
