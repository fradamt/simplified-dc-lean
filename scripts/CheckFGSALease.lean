import AvailableChainFGSA
open Lean Meta

/-! FGSA lease-instance check (G11 M1). The SA base runs GridCO with
`GridCO.slowLeasePolicy`. Every use, in a type or a value of a compiled
constant of the modules of `AvailableChainFGSA`, of a constant with a
`[GridCO.LeasePolicy]` argument must give that argument as
`GridCO.slowLeasePolicy`. A use at the default instance (`gridLeasePolicy`),
at a bound variable, or without the argument (partial or unapplied) fails.

It checks BUILT data, as `scripts/CheckFGSAAxioms.lean`: run
`lake build AvailableChainFGSA` first, or use `bash scripts/check-fgsa.sh`.

A declaration of another library that Lean creates in an FGSA module (the
equation lemma `GridCO.recordGenuine.eq_1`, realized when an FGSA proof
unfolds `recordGenuine`) is skipped when it is itself generic in the policy
(a `[LeasePolicy]` binder) and is outside the namespace `AvailableChain.FGSA`:
its policy is a bound variable, and every use of it is checked.

Run: `lake env lean --run scripts/CheckFGSALease.lean [M …]`. Each optional
`M` is one more root module to import; its own constants are checked too (the
negative control in `check-fgsa.sh` uses this).
Exit codes: 0 clean; 1 a bad use; 2 nothing found. -/

def policyName : Name := `AvailableChain.GridCO.LeasePolicy
def slowName : Name := `AvailableChain.GridCO.slowLeasePolicy

def inScope (roots : List Name) (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      roots.any (·.isPrefixOf m)
  | none => false

/-- The positions of the `[LeasePolicy]` binders of a constant. -/
def leasePositions (ci : ConstantInfo) : MetaM (Array Nat) :=
  forallTelescopeReducing ci.type fun xs _ => do
    let mut out := #[]
    for i in [0:xs.size] do
      if (← inferType xs[i]!).isConstOf policyName then out := out.push i
    return out

structure Scan where
  cache : Std.HashMap Name (Array Nat) := {}
  seen : Std.HashSet Expr := {}
  bad : Array String := #[]
  uses : Nat := 0

partial def scan (owner : Name) (e : Expr) : StateT Scan MetaM Unit := do
  if (← get).seen.contains e then return
  modify fun s => { s with seen := s.seen.insert e }
  let posOf (c : Name) : StateT Scan MetaM (Array Nat) := do
    if let some ps := (← get).cache[c]? then return ps
    let ps ← match (← getEnv).find? c with
      | some ci => leasePositions ci
      | none => pure #[]
    modify fun s => { s with cache := s.cache.insert c ps }
    return ps
  match e with
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then
        for i in ← posOf c do
          modify fun s => { s with uses := s.uses + 1 }
          if h : i < args.size then
            unless args[i].isConstOf slowName do
              modify fun s => { s with bad := s.bad.push s!"{owner}: {c} at {args[i]}" }
          else
            modify fun s => { s with bad := s.bad.push s!"{owner}: {c} (partial)" }
      else scan owner f
      for a in args do scan owner a
  | .const c _ =>
      unless (← posOf c).isEmpty do
        modify fun s => { s with bad := s.bad.push s!"{owner}: {c} (unapplied)" }
  | .lam _ t b _ | .forallE _ t b _ => do scan owner t; scan owner b
  | .letE _ t v b _ => do scan owner t; scan owner v; scan owner b
  | .mdata _ b | .proj _ _ b => scan owner b
  | _ => pure ()

def main (args : List String) : IO UInt32 := do
  let extra := args.map String.toName
  let roots := `AvailableChainFGSA :: extra
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map ({ module := · })) {}
  let cs := env.constants.toList.filter (fun (n, _) => inScope roots env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let run : MetaM (Scan × Nat) := do
    let mut st : Scan := {}
    let mut skipped := 0
    for (n, ci) in cs do
      if !(`AvailableChain.FGSA).isPrefixOf n && !(← leasePositions ci).isEmpty then
        skipped := skipped + 1
        continue
      st := { st with seen := {} }
      let ((), st') ← (do
        scan n ci.type
        if let some v := ci.value? (allowOpaque := true) then scan n v).run st
      st := st'
    return (st, skipped)
  let (st, skipped) ← run.run' {} |>.toIO' { fileName := "CheckFGSALease", fileMap := .ofString "" }
    { env := env }
  for b in st.bad do IO.println s!"BAD LEASE INSTANCE {b}"
  IO.println s!"checked {cs.length - skipped} constants ({skipped} generic skipped), {st.uses} lease arguments"
  return if st.bad.isEmpty then 0 else 1
