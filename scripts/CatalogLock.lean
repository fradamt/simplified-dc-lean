import AvailableChainFramework
open Lean

/-! Catalog lock. Each locked declaration gets a hash of its own statement
(and body, for a definition) and of every declaration that it uses,
transitively. `docs/catalog.lock` has one line `<name> <16 hex digits>` per
declaration, sorted by name.

Run: `lake env lean --run scripts/CatalogLock.lean --write | --check`.
Exit codes: 0 same, 1 different, 2 usage or a missing declaration. -/

/-- Every declaration of these modules is locked (L1–L3). The LM/L0
definitions that they use are reached through the closure. `Kit` (L5) is
not locked. -/
def lockedModules : List Name :=
  [`AvailableChainFramework.Hooks, `AvailableChainFramework.Instance,
   `AvailableChainFramework.Claim, `AvailableChainFramework.Cert,
   `AvailableChainFramework.Profile, `AvailableChainFramework.Pareto]

/-- Every declaration of the modules under this prefix is locked (L3). -/
def lockedModulePrefix : Name := `AvailableChainFramework.Catalog

def locked (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      lockedModules.contains m || lockedModulePrefix.isPrefixOf m
  | none => false

def ownHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (hash ci.name) (hash ci.type)
  match ci with
  | .defnInfo d => mixHash base (hash d.value)
  | .opaqueInfo d => mixHash base (hash d.value)
  | .inductInfo d => d.ctors.foldl (fun h c => mixHash h (hash c)) base
  | _ => base  -- theorems: the statement only; a new proof keeps the hash

/-- The declarations that `ci` uses. A theorem uses only the constants of its
statement, so that a new proof keeps the hash. -/
def deps (ci : ConstantInfo) : NameSet :=
  match ci with
  | .thmInfo _ => ci.type.getUsedConstantsAsSet
  | _ => ci.getUsedConstantsAsSet

partial def closureHash (env : Environment) (n : Name)
    (memo : Std.HashMap Name UInt64) : Except String (UInt64 × Std.HashMap Name UInt64) := do
  if let some h := memo[n]? then return (h, memo)
  let some ci := env.find? n | throw s!"missing body: {n}"
  let memo := memo.insert n (ownHash ci)  -- breaks cycles through recursors
  let ds := ((deps ci).toList.filter (· != n)).toArray.qsort Name.lt
  let mut h := ownHash ci
  let mut memo := memo
  for d in ds do
    let (hd, m) ← closureHash env d memo
    memo := m
    h := mixHash h hd
  return (h, memo.insert n h)

def hex (u : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  "".pushn '0' (16 - s.length) ++ s

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `AvailableChainFramework }] {}
  let names := (env.constants.toList.map (·.1)).filter (fun n =>
    !n.isInternal && locked env n)
  let names := names.toArray.qsort Name.lt
  let mut memo : Std.HashMap Name UInt64 := {}
  let mut lines : Array String := #[]
  for n in names do
    match closureHash env n memo with
    | .ok (h, m) => memo := m; lines := lines.push s!"{n} {hex h}"
    | .error e => IO.eprintln e; return 2
  let text := String.intercalate "\n" lines.toList ++ "\n"
  match args with
  | ["--write"] => IO.FS.writeFile "docs/catalog.lock" text; return 0
  | ["--check"] =>
      match ← (IO.FS.readFile "docs/catalog.lock").toBaseIO with
      | .error e => IO.eprintln s!"cannot read docs/catalog.lock: {e}"; return 2
      | .ok old =>
        if old == text then return 0
        IO.eprintln "catalog.lock differs"; return 1
  | _ => IO.eprintln "usage: --write | --check"; return 2
