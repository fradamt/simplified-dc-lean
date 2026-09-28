import AvailableChainRegistry
import Lean.Util.CollectAxioms
import Lean.Meta.Basic
open Lean

/-! Type-scanning registry. Every constant in `AvailableChainRegistry` whose
type is `Cert c I`, `Refutation c I` or `RefutationFamily c I` is a row of
`docs/REGISTRY.md` (with the claim domain `K` of `c : ClaimSpec K` as the first,
implicit argument). A type `∀ …, Cert c I` is CONDITIONAL and is not a
certificate; it is still written as a row, with status `CONDITIONAL (not a
certificate)`.

A row's status is `LEAN` only if every axiom the declaration transitively
depends on (`Lean.collectAxioms`) is one of `propext`, `Classical.choice`,
`Quot.sound`. Any other axiom (including `sorryAx`) gives status
`UNSOUND(<axiom names>)`; a CONDITIONAL row is not checked, since it is not
a certificate. A row's claim column keeps the claim's name and appends
`NON-CATALOG` if the `ClaimSpec` it certifies is not declared in a module
under `AvailableChainFramework.Catalog`.

A certificate of a pulled claim `ClaimSpec.pull m c` shows the base claim
`c` with the suffix `(pulled)`. A row of kind `profile-cert` (a `ProfileCert p
I`, or a `Candidate I`, which is `ProfileCert core I`) shows the profile `id`
in the claim column, for example `core.v1`.

The libraries in `instanceLibraries` are imported, and only their modules
give rows. A row of a module under `AvailableChainRegistry.Gaps` has status
`KNOWN-GAP` in place of `LEAN`; `UNSOUND` and `CONDITIONAL` stay.

Run: `lake env lean --run scripts/Registry.lean [--check]`. Without an
argument, write `docs/REGISTRY.md`. With `--check`, compare the text with
`docs/REGISTRY.md` and write nothing.
Exit codes: 0 written, or the same; 1 different; 2 a usage error or an
unreadable file. -/

/-- The libraries that hold certificates and refutations. The script imports
them and scans only their modules. -/
def instanceLibraries : List Name := [`AvailableChainRegistry]

/-- Rows of these modules are known gaps: a `LEAN` status becomes
`KNOWN-GAP`. -/
def gapsPrefix : Name := `AvailableChainRegistry.Gaps

/-- The head constant after all leading binders, and whether binders exist. -/
partial def headOf (e : Expr) (binders : Bool := false) : Option Name × Bool :=
  match e with
  | .forallE _ _ b _ => headOf b true
  | _ => (e.getAppFn.constName?, binders)

def kinds : List (Name × String) :=
  [(``AvailableChain.Framework.Cert, "cert"),
   (``AvailableChain.Framework.Refutation, "refutation"),
   (``AvailableChain.Framework.RefutationFamily, "refutation-family"),
   -- Arguments `K p I`.
   (``AvailableChain.Framework.ProfileCert, "profile-cert"),
   -- Argument `I`. `Candidate I` is a `def`, so its type head is `Candidate`.
   (``AvailableChain.Framework.Catalog.Candidate, "profile-cert")]

/-- Axioms allowed in a sound LEAN row. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms `n` transitively depends on. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n) { fileName := "Registry", fileMap := .ofString "" }
    { env := env }

/-- `n`'s status column: `LEAN`, or `UNSOUND(ax1, ax2, …)` if it depends on
an axiom outside `allowedAxioms`. -/
def statusOf (env : Environment) (n : Name) : IO String := do
  let axs ← axiomsOf env n
  let bad := (axs.filter (fun a => !allowedAxioms.contains a)).qsort Name.lt
  if bad.isEmpty then
    return "LEAN"
  else
    return s!"UNSOUND({String.intercalate ", " (bad.toList.map toString)})"

/-- Every catalog claim lives in a module under this prefix. -/
def catalogPrefix : Name := `AvailableChainFramework.Catalog

/-- `n`'s claim column: its name (or `shown`), with `NON-CATALOG` appended if
`n` is not declared in a module under `catalogPrefix`. -/
def claimOf (env : Environment) (n : Name) (shown : Name := n) : String :=
  let s := toString shown
  match env.getModuleIdxFor? n with
  | some idx =>
      if catalogPrefix.isPrefixOf env.header.moduleNames[idx.toNat]! then s
      else s ++ " NON-CATALOG"
  | none => s ++ " NON-CATALOG"

/-- The claim column of a claim expression `c`. For `@ClaimSpec.pull K' K m c'`,
the base claim `c'` (the last argument) with the suffix `(pulled)`. -/
def claimColumn (env : Environment) (c : Expr) : String :=
  if c.isAppOfArity ``AvailableChain.Framework.ClaimSpec.pull 4 then
    ((c.getAppArgs.back!.getAppFn.constName?.map (claimOf env)).getD "?") ++ " (pulled)"
  else
    (c.getAppFn.constName?.map (claimOf env)).getD "?"

/-- The name that a closed `Name` expression in normal form denotes. -/
partial def nameOfExpr? (e : Expr) : Option Name :=
  if e.isConstOf ``Name.anonymous then some .anonymous
  else match e.getAppFn.constName?, e.getAppArgs with
    | some ``Name.str, #[p, .lit (.strVal s)] => (nameOfExpr? p).map (·.str s)
    | some ``Name.num, #[p, .lit (.natVal k)] => (nameOfExpr? p).map (·.num k)
    | _, _ => none

/-- The claim column of a profile certificate: the `id` of the profile `p`
over the claim domain `K`, by reduction of `Profile.id p`. If the reduction does not
give a name, the name of the constant `p`. `NON-CATALOG` as for a claim. -/
def profileColumn (env : Environment) (K p : Expr) : IO String := do
  let e := mkApp2 (mkConst ``AvailableChain.Framework.Profile.id) K p
  let r ← Core.CoreM.toIO' (Meta.MetaM.run' (Meta.reduce e))
    { fileName := "Registry", fileMap := .ofString "" } { env := env }
  let some n := p.getAppFn.constName? | return "?"
  return claimOf env n ((nameOfExpr? r).getD n)

/-- The text of `docs/REGISTRY.md`. -/
def registryText : IO String := do
  let env ← importModules (instanceLibraries.map ({ module := · })).toArray {}
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    -- Only declarations of `instanceLibraries` modules are rows.
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless instanceLibraries.any (·.isPrefixOf m) do continue
    let (h, conditional) := headOf ci.type
    match h.bind (fun h => kinds.lookup h) with
    | some kind =>
        let args := ci.type.getForallBody.getAppArgs
        -- The claim (or profile) column and the instance argument.
        let (claim, i) ← match h with
          | some ``AvailableChain.Framework.ProfileCert =>
              -- `K p I`: the claim domain, the profile, the instance.
              pure (← profileColumn env args[0]! args[1]!, args[2]!)
          | some ``AvailableChain.Framework.Catalog.Candidate =>
              -- `I`: `Candidate I` is `ProfileCert core I` over `v1`.
              pure (← profileColumn env (mkConst ``AvailableChain.Framework.ClaimDomain.v1)
                  (mkConst ``AvailableChain.Framework.Catalog.core), args[0]!)
          | _ =>
              -- `K c I`: the claim domain, the claim, the instance.
              pure (claimColumn env args[1]!, args[2]!)
        let inst := (i.getAppFn.constName?.map toString).getD "?"
        let status ← if conditional then pure "CONDITIONAL (not a certificate)" else statusOf env n
        let status := if status == "LEAN" && gapsPrefix.isPrefixOf m then "KNOWN-GAP" else status
        rows := rows.push s!"│ {n} │ {kind} │ {claim} │ {inst} │ {status} │"
    | none => pure ()
  let sorted := rows.qsort (· < ·)
  let libs := String.intercalate ", " (instanceLibraries.map (s!"`{·}`"))
  return "# Registry (generated by scripts/Registry.lean; do not edit)\n\n" ++
    s!"Scanned libraries: {libs}.\n\n```text\n" ++
    "│ Declaration │ Kind │ Claim │ Instance │ Status │\n" ++
    String.intercalate "\n" sorted.toList ++ "\n```\n"

def registryPath : System.FilePath := "docs/REGISTRY.md"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [] =>
      IO.FS.writeFile registryPath (← registryText)
      return 0
  | ["--check"] =>
      let text ← registryText
      match ← (IO.FS.readFile registryPath).toBaseIO with
      | .error e => IO.eprintln s!"cannot read {registryPath}: {e}"; return 2
      | .ok old =>
          if old == text then return 0
          IO.eprintln s!"{registryPath} differs: run scripts/Registry.lean to write it"
          return 1
  | _ =>
      IO.eprintln "usage: lake env lean --run scripts/Registry.lean [--check]"
      return 2
