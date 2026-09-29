import AvailableChainFGSA
open Lean Meta

/-! FGSA lease-instance check (G11 M1; G13 Astra M1, Opus m2). The SA base runs
GridCO with `GridCO.slowLeasePolicy`. A parameter is a policy parameter if its
type, reduced by `whnf`, is `GridCO.LeasePolicy` (so an alias of the type is
caught).

Scanned (the types and values of these constants):
- every compiled constant of the modules of `AvailableChainFGSA` (and of each
  extra root module `M` on the command line), except the equation lemmas that
  Lean generates for a definition of another library (see "Skipped");
- inspected imported definitions: every definition in a namespace
  `AvailableChain.*` of a module outside the scanned roots that a scanned
  constant reaches, directly or through the values of other inspected
  definitions.

Rules:
- A scanned constant must not have a policy parameter. FGSA never needs a
  policy-generic declaration, so a wrapper with its own policy parameter in an
  FGSA module fails, whatever its namespace or name (also a `private` one).
- In a scanned constant, every argument at a policy position of an applied
  constant must be the constant `GridCO.slowLeasePolicy`. The default instance
  `gridLeasePolicy`, any other term, a bound variable, a partial use and an
  unapplied use fail.
- In an inspected imported definition, a policy argument may also be a bound
  variable (a generic definition that passes its own policy parameter
  through); every closed policy argument must be `GridCO.slowLeasePolicy`.
  So an imported wrapper that fixes `gridLeasePolicy` inside and that FGSA
  reaches fails.

Trusted, not inspected: the proofs of imported theorems (their statements
reach FGSA only through the arguments at each use, which the rules check), and
definitions outside the namespace `AvailableChain` (Lean core, Batteries,
Mathlib: they do not mention GridCO).

Skipped: a constant whose last name component is `eq_<k>` or `eq_def`, whose
prefix is a definition declared in a module outside the scanned roots (for
example `GridCO.recordGenuine.eq_1`, which Lean realizes in an FGSA module when
an FGSA proof unfolds `recordGenuine`). Its policy is a bound variable, and
each use of it is checked at the use. Its definition is inspected as an
imported definition (the equation states the body of that definition).

It checks BUILT data, as `scripts/CheckFGSAAxioms.lean`: run
`lake build AvailableChainFGSA` first, or use `bash scripts/check-fgsa.sh`.

Run: `lake env lean --run scripts/CheckFGSALease.lean [M …]`. Each optional
`M` is one more root module to import and scan (the negative controls in
`check-fgsa.sh` use this).
Exit codes: 0 clean; 1 a bad use; 2 nothing found. -/

def policyName : Name := `AvailableChain.GridCO.LeasePolicy
def slowName : Name := `AvailableChain.GridCO.slowLeasePolicy

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def inRoots (roots : List Name) (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => roots.any (·.isPrefixOf m)
  | none => false

/-- A generated equation lemma of a definition of another library. -/
def generatedEqn (roots : List Name) (env : Environment) (n : Name) : Bool :=
  match n with
  | .str pre s =>
      let k := s.drop 3
      let isEqn := s == "eq_def" || (s.startsWith "eq_" && !k.isEmpty && k.all Char.isDigit)
      isEqn && (match env.find? pre with
        | some (.defnInfo _) => !inRoots roots env pre
        | _ => false)
  | _ => false

/-- The positions of the policy parameters of a constant (types reduced). -/
def leasePositions (ci : ConstantInfo) : MetaM (Array Nat) :=
  forallTelescopeReducing ci.type fun xs _ => do
    let mut out := #[]
    for i in [0:xs.size] do
      let t ← whnf (← inferType xs[i]!)
      if t.isConstOf policyName then out := out.push i
    return out

structure Scan where
  cache : Std.HashMap Name (Array Nat) := {}
  seen : Std.HashSet Expr := {}
  bad : Array String := #[]
  uses : Nat := 0
  reached : Std.HashSet Name := {}

def posOf (c : Name) : StateT Scan MetaM (Array Nat) := do
  if let some ps := (← get).cache[c]? then return ps
  let ps ← match (← getEnv).find? c with
    | some ci => leasePositions ci
    | none => pure #[]
  modify fun s => { s with cache := s.cache.insert c ps }
  return ps

def report (msg : String) : StateT Scan MetaM Unit :=
  modify fun s => { s with bad := s.bad.push msg }

def note (c : Name) : StateT Scan MetaM Unit :=
  modify fun s => { s with reached := s.reached.insert c }

/-- Scan `e`, a type or value of `owner`. `generic`: a bound variable is a valid
policy argument (only in an inspected imported definition). -/
partial def scan (owner : Name) (generic : Bool) (e : Expr) : StateT Scan MetaM Unit := do
  if (← get).seen.contains e then return
  modify fun s => { s with seen := s.seen.insert e }
  match e with
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then
        note c
        for i in ← posOf c do
          modify fun s => { s with uses := s.uses + 1 }
          if h : i < args.size then
            let a := args[i]
            unless a.isConstOf slowName || (generic && a.isBVar) do
              report s!"{owner}: {c} at {a}"
          else
            report s!"{owner}: {c} (partial)"
      else scan owner generic f
      for a in args do scan owner generic a
  | .const c _ =>
      note c
      unless (← posOf c).isEmpty do report s!"{owner}: {c} (unapplied)"
  | .lam _ t b _ | .forallE _ t b _ => do scan owner generic t; scan owner generic b
  | .letE _ t v b _ => do scan owner generic t; scan owner generic v; scan owner generic b
  | .mdata _ b | .proj _ _ b => scan owner generic b
  | _ => pure ()

def scanConst (owner : Name) (generic : Bool) (ci : ConstantInfo) :
    StateT Scan MetaM Unit := do
  modify fun s => { s with seen := {} }
  scan owner generic ci.type
  if let some v := ci.value? (allowOpaque := true) then scan owner generic v

def main (args : List String) : IO UInt32 := do
  let extra := args.map String.toName
  let roots := `AvailableChainFGSA :: extra
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map ({ module := · })) {}
  let cs := env.constants.toList.filter (fun (n, _) => inRoots roots env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let run : MetaM (Scan × Nat × Nat) := do
    let mut st : Scan := {}
    let mut skipped := 0
    for (n, ci) in cs do
      if generatedEqn roots env n then
        -- The equation states the body of its definition: inspect that body.
        skipped := skipped + 1
        st := { st with reached := st.reached.insert n.getPrefix }
        continue
      let ((), st') ← (do
        unless (← posOf ci.name).isEmpty do
          report s!"{n}: has a policy parameter (a policy-generic declaration in FGSA)"
        scanConst n false ci).run st
      st := st'
    -- Inspect the imported `AvailableChain.*` definitions that FGSA reaches.
    let mut done : Std.HashSet Name := {}
    let mut inspected := 0
    let mut todo := st.reached.toList
    while !todo.isEmpty do
      let c := todo.head!
      todo := todo.tail!
      if done.contains c then continue
      done := done.insert c
      if !(`AvailableChain).isPrefixOf c || inRoots roots env c then continue
      match env.find? c with
      | some ci@(.defnInfo _) =>
          inspected := inspected + 1
          let ((), st') ← (scanConst c true ci).run { st with reached := {} }
          todo := todo ++ st'.reached.toList
          st := st'
      | _ => pure ()
    return (st, skipped, inspected)
  let (st, skipped, inspected) ← run.run' {} |>.toIO'
    { fileName := "CheckFGSALease", fileMap := .ofString "" } { env := env }
  for b in st.bad do IO.println s!"BAD LEASE INSTANCE {b}"
  IO.println s!"checked {cs.length - skipped} constants ({skipped} generated equation \
    lemmas skipped), {inspected} imported definitions inspected, {st.uses} lease arguments"
  return if st.bad.isEmpty then 0 else 1
