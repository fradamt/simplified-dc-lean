import AvailableChainFramework
import AvailableChainRegistry
import AvailableChainKit
import AvailableChainEngineV2
import AvailableChainKitV2
import Lean.Util.CollectAxioms
open Lean

/-! Framework axiom check. Every non-internal constant of the modules of
`AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainKit`,
`AvailableChainEngineV2` and `AvailableChainKitV2` may depend only on
`propext`, `Classical.choice` and `Quot.sound` (`collectAxioms`, proofs
included). This rejects `sorryAx`, the auxiliary axioms of `native_decide`
and project axioms. It is modelled on `scripts/CheckFGAxioms.lean`.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainFramework
AvailableChainRegistry AvailableChainKit AvailableChainEngineV2 AvailableChainKitV2`
first.

Run: `lake env lean --run scripts/CheckFrameworkAxioms.lean`.
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

/-- The axioms `n` transitively depends on. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFrameworkAxioms", fileMap := .ofString "" } { env := env }

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "USAGE: lake env lean --run scripts/CheckFrameworkAxioms.lean"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (libraries.map ({ module := · })).toArray {}
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
  IO.println s!"checked {cs.length} constants"
  return if badAxioms then 1 else 0
