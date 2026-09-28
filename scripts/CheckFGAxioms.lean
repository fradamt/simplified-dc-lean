import AvailableChainSimplexFG
import AvailableChainKitFG
import Lean.Util.CollectAxioms
open Lean

/-! FG axiom check. Every compiled constant of the modules of
`AvailableChainSimplexFG` and `AvailableChainKitFG` may depend only on
`propext`, `Classical.choice` and `Quot.sound`. This rejects `sorryAx`,
`Lean.ofReduceBool` (from `native_decide`) and project axioms.

Run: `lake env lean --run scripts/CheckFGAxioms.lean [--expect N …]`.
With `--expect`, each named constant must be a checked constant (a short
name matches a qualified one by suffix).
Exit codes: 0 clean; 1 a bad axiom; 2 nothing found or an expected name
missing. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def inFG (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      (`AvailableChainSimplexFG).isPrefixOf m || (`AvailableChainKitFG).isPrefixOf m
  | none => false

/-- The axioms `n` transitively depends on. Uses the `Core.CoreM.toIO'`
pattern of `scripts/Registry.lean`: the toolchain's `CollectAxioms` API is
called through `Lean.Util.CollectAxioms`'s `collectAxioms` in `CoreM`. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFGAxioms", fileMap := .ofString "" } { env := env }

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `AvailableChainSimplexFG }, { module := `AvailableChainKitFG }] {}
  let cs := env.constants.toList.filter (fun (n, _) => inFG env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let thms := cs.filterMap fun (n, ci) => if ci matches .thmInfo _ then some n else none
  let mut status : UInt32 := 0
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      status := 1
  if let "--expect" :: names := args then
    for s in names do
      unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
        IO.println s!"NOT CHECKED: {s}"
        status := 2
  IO.println s!"checked {cs.length} constants, {thms.length} theorems"
  return status
