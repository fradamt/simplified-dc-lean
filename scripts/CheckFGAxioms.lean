import AvailableChainSimplexFG
import AvailableChainKitFG
import Lean.Util.CollectAxioms
open Lean

/-! FG axiom check. Every compiled constant of the modules of
`AvailableChainSimplexFG` and `AvailableChainKitFG` may depend only on
`propext`, `Classical.choice` and `Quot.sound`. This rejects `sorryAx`, the
auxiliary `_native` axiom of `native_decide` or `decide +native` (for example
`t._native.native_decide.ax_1_1` on v4.30.0-rc2; older toolchains:
`Lean.ofReduceBool`) and project axioms.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainSimplexFG
AvailableChainKitFG` first, or use `bash scripts/check-fg.sh`, which builds and
then runs every FG check.

Run: `lake env lean --run scripts/CheckFGAxioms.lean [--expect N …]`.
With `--expect`, each named constant must be a checked constant (a short
name matches a qualified one by suffix).
Exit codes: 0 clean; 1 a bad axiom; 2 nothing found, a usage error (an
unknown argument, or `--expect` without a name), or an expected name missing.
Each missing expected name forces exit 2, also after a bad axiom or after
other expected names that are present. -/

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
  -- Reject an unknown argument: a typo must not skip the `--expect` test.
  unless args.isEmpty || (args.head? == some "--expect" && args.length ≥ 2) do
    IO.eprintln "USAGE: lake env lean --run scripts/CheckFGAxioms.lean [--expect N …]"
    return 2
  let expected := args.drop 1
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `AvailableChainSimplexFG }, { module := `AvailableChainKitFG }] {}
  let cs := env.constants.toList.filter (fun (n, _) => inFG env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let thms := cs.filterMap fun (n, ci) => if ci matches .thmInfo _ then some n else none
  let mut badAxioms := false
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
  -- Count the missing names; no later name can clear an earlier miss.
  let mut missing := 0
  for s in expected do
    unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
      IO.println s!"NOT CHECKED: {s}"
      missing := missing + 1
  IO.println s!"checked {cs.length} constants, {thms.length} theorems"
  if missing > 0 then
    IO.println s!"{missing} expected names not checked"
    return 2
  return if badAxioms then 1 else 0
