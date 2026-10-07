module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationTiming
public meta import AvailableChainFGSAProofs.Proofs.Outage.Arming -- shake: keep (closed run evaluation)

@[expose] public section

/-! OUTPUT-DIRECT non-vacuity audit. The event generator and premise checks
are adapted from 583cee0, read with git show. This is a new fixture: restoration
is at 21, so (V) holds at equality. All honest nodes sleep on [17,21).
The finite audit is executable evidence, not a kernel proof of all run premises. -/

open AvailableChain AvailableChain.FGSA AvailableChain.FGSA.Run AvailableChain.SimplexFG
namespace AvailableChain.FGSA.Run.Tests.OutageContinuationSleep

abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 7, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 100, δt := 200, RLarge := by decide,
    digest := fun d => ⟨d.slot + 1⟩ }
def B : NamedProposal 4 := namedProposal p .genesis 1 0 [] [] []
def C : NamedProposal 4 := namedProposal p .genesis 4 0 [] [] []
def prop (s : Nat) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 4) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head N.root⟩
def E : Generic.Env (Fin 4) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 21, t_GST_nonneg := by decide,
    awake := fun _ t => decide (t < 17 ∨ 21 ≤ t) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 4
  | .prop _, _ => 3
  | .base _, i => i

def honestNodes : List (Fin 4) := [0, 1, 2]
abbrev FixtureEvent := V2.Event (Fin 4) (Obj p)
instance : DecidableEq (fgsa p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent := inferInstanceAs (DecidableEq (V2.Event (Fin 4) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def runWith (es : List FixtureEvent) : V2.D.Run (Fin 4) (fgsa p unitCodec) :=
  { honest := {0, 1, 2}, horizon := 30, events := es, seatOf := seats, input := fun _ _ => () }
abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 4 → Node p := fun x => w.getD x.val node0

def cachedStep (w : Array (Node p)) (e : FixtureEvent) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E (runWith []) (world w) e)

/-- Materialization preserves the actual V2 step; events do not affect that step. -/
theorem outageV_sleep_cachedStep_exact (es : List FixtureEvent) (w : Array (Node p))
    (e : FixtureEvent) (x : Fin 4) :
    world (cachedStep w e) x = V2.D.World.step E (runWith es) (world w) e x := by
  have h (f : Fin 4 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E (runWith []) (world w) e)

/-- Cached folds have exactly the event-fold semantics of the V2 engine. -/
theorem outageV_sleep_cachedFold_exact (es : List FixtureEvent) (w : Array (Node p)) :
    world (es.foldl cachedStep w) = es.foldl (V2.D.World.step E (runWith es)) (world w) := by
  have stepEq (w : Array (Node p)) (e : FixtureEvent) :
      world (cachedStep w e) = V2.D.World.step E (runWith es) (world w) e :=
    funext (outageV_sleep_cachedStep_exact es w e)
  have foldEq (xs : List FixtureEvent) (w : Array (Node p)) :
      world (xs.foldl cachedStep w) = xs.foldl (V2.D.World.step E (runWith es)) (world w) := by
    induction xs generalizing w with
    | nil => rfl
    | cons e xs ih => simp only [List.foldl_cons]; rw [ih, stepEq]; rfl
  exact foldEq es w

/-- Only four faulty objects supplement the actual honest emissions. -/
def faultyObjects (t : Nat) : List (Obj p) :=
  match t with
  | 4 => [prop 1 B]
  | 17 => [prop 4 C, head 4 3 C]
  | 21 => [head 5 3 C]
  | _ => []

/-- Tick all honest nodes first. Deliver every actual emission and dependency at the same time. -/
def generateDay (acc : List FixtureEvent × Array (Node p)) (t : Nat) :
    List FixtureEvent × Array (Node p) := Id.run do
  let mut es := acc.1
  let mut w := acc.2
  let mut emitted : List (Obj p) := []
  for x in honestNodes do
    let released : List (Obj p) := (V2.D.tick E (runWith []) (world w x) x (t : Int)).2
    emitted := emitted ++ released
    let ev := V2.Event.tick x (t : Int)
    es := es ++ [ev]
    w := cachedStep w ev
  for o in emitted ++ faultyObjects t do
    for x in honestNodes do
      let ev := V2.Event.deliver x o (t : Int)
      es := es ++ [ev]
      w := cachedStep w ev
  return (es, w)

def rho : V2.D.Run (Fin 4) (fgsa p unitCodec) :=
  runWith ((List.range 31).foldl generateDay ([], Array.replicate 4 node0)).1

theorem outageV_sleep_fresh_committees : V2.D.CStar (fgsaFamilies p unitCodec).fresh rho := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l => cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id

theorem outageV_sleep_linked_committee : V2.D.Linked (fgsaFamilies p unitCodec).linked rho := by
  refine ⟨4, Equiv.refl (Fin 4), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l => cases l with
    | head s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

def trace : Array (Array (Node p)) :=
  rho.events.foldl (fun acc e =>
    acc.push (cachedStep (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 4 node0]
def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 4) : Node p :=
  world (tr.getD i #[]) x
def atTime (tr : Array (Array (Node p))) (t : Time) (x : Fin 4) : State 4 :=
  (atIndex tr (rho.events.takeWhile (fun e => decide (e.time ≤ t))).length x).st
def beforeTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : State 4 :=
  (atIndex tr ((rho.tickIdx? x t).getD 0) x).st
def emitted (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match rho.events[i]? with
  | some (.tick x t) => (V2.D.tick E rho (atIndex tr i x) x t).2
  | _ => []

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Outage continuation: {label} failed")
  IO.println s!"Outage continuation: {label}: PASS"

/-- All carried-object checks enumerate the full model relation. -/
def carriedObjects (o : Obj p) : List (Obj p) :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++ N.rows.map (ofRow p)
  | _ => []

theorem outageV_sleep_carriedObjects_exact (o u : Obj p) :
    (fgsa p unitCodec).carries o u ↔ u ∈ carriedObjects o := by
  change carriesS p o u ↔ _
  delta carriesS carriedObjects
  cases o.payload <;> simp only [List.mem_append, List.not_mem_nil]
  all_goals tauto

def audit : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace
  let hs := honestNodes
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 == u && row.2.1 == o && row.2.2 ≤ t)
  let deliveredAt := fun x o t => es.contains (.deliver x o t)
  require "run parameters and honest set" (decide (
    p.n = 4 ∧ p.k = 2 ∧ p.Δ = 1 ∧ p.η = 7 ∧ L p = 7 ∧
    p.R = 100 ∧ p.δt = 200 ∧ p.K_W = 2 ∧ E.t_GST = 21 ∧ rho.horizon = 30) &&
    hs.length == 3 && ((List.finRange 4).filter (fun x => !hs.contains x)).length == 1)
  require "Base2 schedule and no restart" (
    decide (rho.events.Nodup) && decide (rho.events.Pairwise (fun e f => e.key ≤ f.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ rho.horizon) && hs.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range 31).all (fun t => hs.all (fun x => es.contains (.tick x (t : Int)))))
  require "Base2 wires, exact dependencies, and freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (fgsa p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "Base2 direct signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => hs.all (fun u =>
        if rho.holder o.auth == some u then hasEmission u o t else true)
    | _ => true))
  require "Base2 carried signatures and empty carriage" (es.all (fun e =>
    match e with
    | .deliver _ o t => (carriedObjects o).isEmpty &&
        (carriedObjects o).all (fun a => hs.all (fun u =>
          if rho.holder a.auth == some u then hasEmission u a t else true))
    | _ => true))
  let bodies := [.genesis, B, C]
  require "Base2 named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal N => bodies.contains N
        | _ => true
      | _ => true) &&
    states.all (fun i => (List.finRange 4).all (fun x =>
      (atIndex tr i x).st.namedBodies.all bodies.contains)) &&
    bodies.all (fun N => bodies.contains N.parent) &&
    bodies.all (fun N => bodies.all (fun M => if N.root == M.root then N == M else true)))
  -- The family properties also have kernel proofs below. The maps are fixed for every label.
  require "Base2 committee maps and delta" (
    decide (hs.toFinset = rho.honest) && E.Δ == p.Δ &&
    (List.range 8).all (fun s =>
      seats (.prop s) ⟨0, by change 0 < 1; decide⟩ == 3 &&
      (List.finRange 4).all (fun i => seats (.base (.head s)) i == i &&
        seats (.base .fg) i == i)))
  -- With empty carriage, a handler call can only be for the delivered object itself.
  -- These unconditional same-time checks are stronger than both delivery regimes:
  -- they include all triggers, without an exclusion, cut, or horizon exception.
  require "HealthyPrefix2 and partial synchrony broadcast" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => deliveredAt x o t) &&
    decide (t < t + 1 ∧ t < max t E.t_GST + 1)))
  require "HealthyPrefix2 and partial synchrony acceptance relay" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t =>
        if !processedS p (atIndex tr i y).st o && processedS p (atIndex tr (i + 1) y).st o then
          hs.all (fun x => deliveredAt x o t) &&
            decide (t < t + 1 ∧ t < max t E.t_GST + 1)
        else true
    | _ => true))
  require "HealthyPrefix2 cut, deltaF, and participation" (
    decide (0 ≤ (17 : Time) ∧ 17 ≤ rho.horizon ∧ E.Δ ≤ (1 : Time)) &&
    (List.range 17).all (fun t =>
      decide (1 < (hs.filter (fun x => E.awake x (t : Int))).length)))
  require "Outage2 sleepy bound and fast participation" ((List.range 17).all (fun u =>
    let t : Time := u
    let awake := (hs.filter (fun x => E.awake x t)).length
    let recentOrFaulty := (List.finRange 4).filter (fun x =>
      !hs.contains x || (List.range 8).any (fun j => E.awake x (t - p.η + (j : Int))))
    decide (recentOrFaulty.length < 2 * awake ∧ (p.n + 1) / 2 ≤ awake)))
  require "Outage2 order, both lags, and budget" (decide (
    0 ≤ (10 : Time) ∧ 10 ≤ (17 : Time) ∧ 17 ≤ (21 : Time) ∧ 21 ≤ rho.horizon ∧
    10 + 4 * p.Δ ≤ 17 ∧ 10 + (L p - 3 * p.Δ) ≤ 17 ∧
    (21 : Time) - 17 ≤ min p.η (L p) ∧ (21 : Time) ≤ 17 + L p))
  require "GST and full honest participation after b1" (
    decide (E.t_GST ≤ (21 : Time)) &&
    (List.range 10).all (fun j => hs.all (fun x => E.awake x (21 + (j : Int)))))
  require "corrected length V at equality" (decide (
    (21 : Time) - 17 + (17 - 6 * p.Δ) % (4 * p.Δ) = L p))
  require "full honest sleep on the outage" ((List.range 4).all (fun j =>
    hs.all (fun x => !(E.awake x (17 + (j : Int))))))
  require "no honest outage emissions" (emissions.all (fun row =>
    decide (row.2.2 < 17 ∨ 21 ≤ row.2.2)))
  require "non-genesis initial read B" (decide (B.erase ≠ Block.genesis) &&
    hs.all (fun x => stable (atTime tr 10 x) == B.erase))
  require "both outputs and F through the inclusive horizon" ((List.range 14).all (fun j =>
    hs.all (fun x =>
      let st := atTime tr (17 + (j : Int)) x
      Block.preceq B.erase (stable st) && Block.preceq B.erase (confirmed st) &&
        Block.compatible B.erase (eraseFG st.fg.F))))
  IO.println s!"OUTAGE-V SLEEP: PASS; events={es.size}; honest=3; faulty=1"

/-- The exact delta, K, b0, and b1 of commit 583cee0 violate (V). -/
theorem counterexample_violates_V : ¬ OutageLengthV p 17 24 := by
  rw [OutageLengthV_def]
  decide

/-- The new full-sleep fixture satisfies the corrected length bound. -/
theorem sleep_length_V : OutageLengthV p 17 21 :=
  (outageV_iff_vote_bound p 17 21 (by decide)).mpr (by decide)

#eval audit
#print axioms counterexample_violates_V
#print axioms sleep_length_V
#print axioms outageV_sleep_carriedObjects_exact
#print axioms outageV_sleep_cachedStep_exact
#print axioms outageV_sleep_cachedFold_exact
#print axioms outageV_sleep_fresh_committees
#print axioms outageV_sleep_linked_committee

end AvailableChain.FGSA.Run.Tests.OutageContinuationSleep
end
