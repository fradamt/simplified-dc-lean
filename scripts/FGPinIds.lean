import AvailableChainKitFG.Pins
import Lean
open Lean AvailableChain.KitFG  -- the namespace of Pins.lean

/-! Prints the manifest of `Pins.lean` from the elaborated values (`manifest`),
or with `--check-names` checks the pinned names (`checkNames`). It reads BUILT
data: `lean --run` imports the `.olean` files and does not compare them with the
sources. Run it after `lake build AvailableChainSimplexFG AvailableChainKitFG`:
`lake env lean --run scripts/FGPinIds.lean [--check-names]`, or use
`bash scripts/check-fg.sh`, which builds and then runs every FG check.
`scripts/check-fg-pins.sh` builds, then runs it without an argument. -/

/-- Every pinned name is a constant of a module of `AvailableChainSimplexFG` or
`AvailableChainKitFG`, so `CheckFGAxioms.lean` checks its axioms (Astra T02).
Exit 0 when all are; 2 otherwise. -/
def checkNames (ns : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `AvailableChainSimplexFG }, { module := `AvailableChainKitFG }] {}
  let inFG (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (`AvailableChainSimplexFG).isPrefixOf m || (`AvailableChainKitFG).isPrefixOf m
    | none => false
  if ns.isEmpty then
    IO.println "NO PIN NAMES"
    return 2
  let bad := ns.filter (!inFG ·)
  for n in bad do IO.println s!"NOT AN FG CONSTANT: {n}"
  IO.println s!"checked {ns.length} pinned names"
  return if bad.isEmpty then 0 else 2

def main (args : List String) : IO UInt32 := do
  if args == ["--check-names"] then
    checkNames (pinNames pins defPins helpers)
  else
    for l in manifest pins defPins notFormalized historicalPins do IO.println l
    return 0
