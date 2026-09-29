import AvailableChainFramework
import AvailableChainRegistry
import AvailableChainKit
import AvailableChainEngineV2
import AvailableChainKitV2
import Lean.Util.CollectAxioms
open Lean

/-! Framework axiom check. It imports the library roots
`AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainKit`,
`AvailableChainEngineV2` and `AvailableChainKitV2`, and every module under
`AvailableChainEngineV2/Tests/` (found at run time; the root does not import
them). Every non-internal constant of an imported module of these five
libraries may depend only on `propext`, `Classical.choice` and `Quot.sound`
(`collectAxioms`, proofs included). Modules of these libraries that no root
and no test module imports are not checked; `example`s are not constants and
are not checked. This rejects `sorryAx`, the auxiliary axioms of
`native_decide` and project axioms. It is modelled on
`scripts/CheckFGAxioms.lean`.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainFramework
AvailableChainRegistry AvailableChainKit AvailableChainEngineV2 AvailableChainKitV2`
first.

Run from the repository root: `lake env lean --run scripts/CheckFrameworkAxioms.lean`.
Exit codes: 0 clean; 1 a bad axiom; 2 nothing found or a usage error. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The libraries whose modules are checked. -/
def libraries : List Name :=
  [`AvailableChainFramework, `AvailableChainRegistry, `AvailableChainKit, `AvailableChainEngineV2,
    `AvailableChainKitV2]

def inLibraries (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      libraries.any (·.isPrefixOf m)
  | none => false

/-- The directory of the engine v2 test modules, relative to the repository root. -/
def engineTestsDir : System.FilePath := "AvailableChainEngineV2" / "Tests"

/-- Every module under `engineTestsDir`: `AvailableChainEngineV2/Tests/A/B.lean`
gives `AvailableChainEngineV2.Tests.A.B`. -/
def engineTestModules : IO (Array Name) := do
  let files ← engineTestsDir.walkDir
  return (files.filter (·.extension == some "lean")).map fun f =>
    (f.withExtension "").components.foldl Name.str .anonymous

/-- The axioms `n` transitively depends on. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFrameworkAxioms", fileMap := .ofString "" } { env := env }

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "USAGE: lake env lean --run scripts/CheckFrameworkAxioms.lean"
    return 2
  unless ← engineTestsDir.isDir do
    IO.eprintln s!"NO DIRECTORY {engineTestsDir}: run from the repository root"
    return 2
  let tests ← engineTestModules
  initSearchPath (← findSysroot)
  let modules := libraries.toArray ++ tests
  let env ← importModules (modules.map ({ module := · })) {}
  let cs := env.constants.toList.filter (fun (n, _) => !n.isInternal && inLibraries env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let mut badAxioms := false
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
  IO.println s!"checked {cs.length} constants (test modules: {tests})"
  return if badAxioms then 1 else 0
