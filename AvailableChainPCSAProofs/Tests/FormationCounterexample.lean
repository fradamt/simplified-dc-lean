module
public import AvailableChainPCSAProofs
public meta import AvailableChainPCSAProofs -- shake: keep (closed run evaluation)

@[expose] public section

/-! A finite run check for the Formation premises at slot 4.
The proposer has a local lock that is released at the vote tick.
The common view is empty. F4 is true, but the proposal path is ineligible.
The check uses the actual engine and model hooks. It does not assert a claim proof. -/

open AvailableChain AvailableChain.PCSA AvailableChain.PCSA.Run AvailableChain.SimplexFG
namespace AvailableChain.PCSA.Run.Tests.FormationCounterexample
abbrev p : Params :=
  { Δ := 1, n := 4, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide,
    digest := fun d => if d.slot = 1 then ⟨1⟩ else if d.slot = 3 then ⟨2⟩ else ⟨3⟩ }
def A : NamedProposal 4 := namedProposal p .genesis 1 0 [] [] [] none
def B : NamedProposal 4 := namedProposal p .genesis 3 0 [] [] [] none
def prop (s : Nat) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.prop s) ⟨0, by change 0 < 1; decide⟩, .proposal N⟩
def head (s : Nat) (i : Fin 4) (N : NamedProposal 4) : Obj p :=
  ⟨.seat (.base (.head s)) i, .head N.root⟩
def E : Generic.Env (Fin 4) :=
  { Δ := 1, Δ_pos := by decide, t_GST := 0, t_GST_nonneg := by decide,
    awake := fun v t => if v = 0 then decide (t = 5 ∨ t = 9 ∨ t = 13 ∨ t = 16 ∨ t = 17 ∨ t = 18)
      else decide (t = 13 ∨ t = 17 ∨ t = 18) }
def seats : (l : RunLabel) → Fin (RunLabel.seats p l) → Fin 4
  | .prop s, _ => if s = 4 then 0 else 3
  | .base _, i => i
-- Old proposals and HEADs can be delivered after their emission. No row or ack.
def oldDeliveries (t : Nat) : List (V2.Event (Fin 4) (Obj p)) :=
  match t with
  | 4 => [.deliver 0 (prop 1 A) 4]
  | 5 => [.deliver 0 (head 1 0 A) 5]
  | 9 => [.deliver 0 (head 2 0 A) 9]
  | 14 => [.deliver 0 (prop 3 B) 14]
  | 12 => [.deliver 1 (prop 3 B) 12, .deliver 2 (prop 3 B) 12]
  | 15 =>
    [.deliver 1 (prop 1 A) 15, .deliver 2 (prop 1 A) 15] ++
    [1, 2].flatMap (fun v => [.deliver v (head 1 0 A) 15, .deliver v (head 2 0 A) 15]) ++
    [0, 1, 2].flatMap (fun v =>
      [.deliver v (head 3 0 A) 15, .deliver v (head 3 1 B) 15,
       .deliver v (head 3 2 B) 15, .deliver v (head 3 3 B) 15])
  | _ => []
def rho0 : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec) :=
  { honest := {0, 1, 2}, horizon := 22,
    events := (List.range 23).flatMap (fun (t : Nat) =>
      [0, 1, 2].map (fun v => V2.Event.tick v (t : Int)) ++ oldDeliveries t),
    seatOf := seats, input := fun _ _ => () }
/-- The same identity committee map is used at every fresh label. -/
theorem fresh_committees : V2.D.CStar (pcsaFamilies p unitCodec).fresh rho0 := by
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | fg => exact hl.elim
    | head s => exact Function.bijective_id
    | ack s => exact Function.bijective_id

/-- The FG committee is fixed and linked. -/
theorem linked_committee : V2.D.Linked (pcsaFamilies p unitCodec).linked rho0 := by
  refine ⟨4, Equiv.refl (Fin 4), ?_⟩
  intro l hl
  cases l with
  | prop s => exact hl.elim
  | base l =>
    cases l with
    | head s => exact hl.elim
    | ack s => exact hl.elim
    | fg => exact ⟨rfl, fun _ => rfl⟩

def raw3 : List (HeadWire 4) :=
  [⟨.seat (.head 3) 0, A.root⟩, ⟨.seat (.head 3) 1, B.root⟩,
   ⟨.seat (.head 3) 2, B.root⟩, ⟨.seat (.head 3) 3, B.root⟩]
def N : NamedProposal 4 := namedProposal p A 4 0 raw3 raw3 [] none
def laterDeliveries (t : Nat) : List (V2.Event (Fin 4) (Obj p)) :=
  match t with
  | 16 => [0, 1, 2].map (fun v => .deliver v (prop 4 N) 16)
  | 17 => [0, 1, 2].flatMap (fun v =>
    [.deliver v (head 4 0 B) 17, .deliver v (head 4 1 B) 17,
     .deliver v (head 4 2 B) 17])
  | _ => []
def rho : V2.D.Run (Fin 4) (pcsaWith .idle p unitCodec) :=
  { rho0 with events := (List.range 23).flatMap (fun (t : Nat) =>
    [0, 1, 2].map (fun v => V2.Event.tick v (t : Int)) ++ oldDeliveries t ++ laterDeliveries t) }

abbrev node0 : Node p := ⟨initial p.n, RecordOnce.initial⟩
abbrev world (w : Array (Node p)) : Fin 4 → Node p := fun x => w.getD x.val node0

def cachedStep (w : Array (Node p)) (e : V2.Event (Fin 4) (Obj p)) : Array (Node p) :=
  Array.ofFn (V2.D.World.step E rho (world w) e)

/-- Materializing a finite world preserves the actual engine step at each node. -/
theorem cachedStep_exact (w : Array (Node p)) (e : V2.Event (Fin 4) (Obj p)) (x : Fin 4) :
    world (cachedStep w e) x = V2.D.World.step E rho (world w) e x := by
  have h (f : Fin 4 → Node p) : (Array.ofFn f).getD x.val node0 = f x := by
    rw [← Array.getElem_eq_getD (h := by rw [Array.size_ofFn]; exact x.isLt)]
    exact Array.getElem_ofFn _
  exact h (V2.D.World.step E rho (world w) e)

/-- Cached folds have the same semantics as the engine's event fold. -/
theorem cachedFold_exact (es : List (V2.Event (Fin 4) (Obj p))) (w : Array (Node p)) :
    world (es.foldl cachedStep w) = es.foldl (V2.D.World.step E rho) (world w) := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, funext (cachedStep_exact w e)]
    rfl

def trace : Array (Array (Node p)) :=
  rho.events.foldl (fun acc e =>
    acc.push (cachedStep (acc.getD (acc.size - 1) #[]) e)) #[Array.replicate 4 node0]

def atIndex (tr : Array (Array (Node p))) (i : Nat) (x : Fin 4) : Node p :=
  world (tr.getD i #[]) x

def beforeTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : Node p :=
  atIndex tr ((rho.tickIdx? x t).getD 0) x

def readTick (tr : Array (Array (Node p))) (x : Fin 4) (t : Time) : State 4 :=
  clock p (beforeTick tr x t).st t

def carriedObjects (o : Obj p) : List (Obj p) :=
  match o.payload with
  | .proposal N => N.raw.map (ofHead p) ++ N.support.map (ofHead p) ++
      N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)
  | .pc C => C.acks.map (ofAck p)
  | _ => []

/-- The signature check enumerates every object in the carries relation. -/
theorem carriedObjects_exact (o u : Obj p) :
    (pcsaWith .idle p unitCodec).carries o u ↔ u ∈ carriedObjects o := by
  change carriesS p o u ↔ _
  delta carriesS carriedObjects
  cases o.payload <;> simp only [List.mem_append, List.not_mem_nil]
  all_goals tauto

abbrev FixtureEvent := V2.Event (Fin 4) (Obj p)
instance : DecidableEq (pcsaWith .idle p unitCodec).Object :=
  inferInstanceAs (DecidableEq (Obj p))
instance : DecidableEq FixtureEvent :=
  inferInstanceAs (DecidableEq (V2.Event (Fin 4) (Obj p)))
instance : BEq FixtureEvent := ⟨fun x y => decide (x = y)⟩

def handlesTest (st : State 4) (o u : Obj p) : Bool :=
  decide (o = u) || match (toWire p o).decode with
  | some (.block s N) => namedParentHeld st N &&
      (match parentFG st N.erase with
      | some P => blockAccepted p st s N P &&
          (N.raw.map (ofHead p) ++ N.rows.map (ofRow p) ++ N.pcAcks.map (ofAck p)).contains u
      | none => false)
  | some (.pc C) => (C.acks.map (ofAck p)).contains u
  | _ => false

/-- The finite handles test is the model's complete handles relation. -/
theorem handlesTest_exact (st : State 4) (o u : Obj p) :
    handlesS p st o u ↔ handlesTest st o u = true := by
  delta handlesS handlesTest
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  cases h : (toWire p o).decode with
  | none => simp only [Bool.false_eq_true]
  | some d =>
    cases d <;> simp only [Bool.false_eq_true]
    · rename_i s N
      cases hp : parentFG st N.erase with
      | none => simp only [Bool.and_false, Bool.false_eq_true, reduceCtorEq, false_and,
          exists_false, and_false]
      | some P =>
        simp only [Option.some.injEq, exists_eq_left', Bool.and_eq_true,
          List.contains_iff_mem, List.mem_append]
        tauto
    · simp only [List.contains_iff_mem]

-- All acceptance handles are the parent itself or one of its carried objects.
def handledObjects (st : State 4) (o : Obj p) : List (Obj p) :=
  (o :: carriedObjects o).filter (fun u => handlesTest st o u)

def emitted (tr : Array (Array (Node p))) (i : Nat) : List (Obj p) :=
  match rho.events[i]? with
  | some (.tick x t) => (V2.D.tick E rho (atIndex tr i x) x t).2
  | _ => []

def deadline (t : Time) : Time := max t 15 + 1

def require (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError s!"Formation counterexample: {label} failed")
  IO.println s!"Formation counterexample: {label}: PASS"

def audit : IO Unit := do
  let es : Array FixtureEvent := rho.events.toArray
  let tr := trace
  let hs := ([0, 1, 2] : List (Fin 4))
  let is := List.range es.size
  let states := List.range tr.size
  let emissions := is.flatMap (fun i =>
    let e := es.getD i (.tick 0 0)
    (emitted tr i).map (fun o => (e.node, o, e.time)))
  let hasEmission := fun u o t =>
    emissions.any (fun row => row.1 = u && row.2.1 == o && row.2.2 ≤ t)
  require "schedule" (decide ((rho.events : List FixtureEvent).Nodup) &&
    (es.toList.zip (es.toList.drop 1)).all (fun ef => decide (ef.1.key ≤ ef.2.key)) &&
    es.all (fun e => decide (0 ≤ e.time ∧ e.time ≤ 22) && hs.contains e.node &&
      match e with | .restart .. => false | _ => true) &&
    (List.range 23).all (fun t => hs.all (fun x => es.contains (.tick x (t : Int)))) )
  require "wire/dependencies/freshness" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver x o _ => (pcsaWith .idle p unitCodec).wellFormed o &&
        depsS p (atIndex tr i x).st o && !processedS p (atIndex tr i x).st o
    | _ => true))
  require "direct signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => hs.all (fun u =>
        if rho.holder o.auth == some u then hasEmission u o t else true)
    | _ => true))
  require "carried signatures" (es.all (fun e =>
    match e with
    | .deliver _ o t => (carriedObjects o).all (fun a => hs.all (fun u =>
        if rho.holder a.auth == some u then hasEmission u a t else true))
    | _ => true))
  let bodies := [.genesis, A, B, N]
  require "named root collision freedom" (
    es.all (fun e => match e with
      | .deliver _ o _ => match o.payload with
        | .proposal X => bodies.contains X
        | _ => true
      | _ => true) &&
    states.all (fun i => hs.all (fun x => (atIndex tr i x).st.namedBodies.all bodies.contains)) &&
    bodies.all (fun X => bodies.contains X.parent) &&
    bodies.all (fun X => bodies.all (fun Y => if X.root == Y.root then X == Y else true)))
  require "stage-one frame" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.fg.F == .genesis && (controls p st).Z == .genesis && (controls p st).lo == 0)))
  -- The fresh HEAD and ack maps and the linked FG map are the identity.
  require "fault cap/committee maps" (decide (4 * 1 ≤ p.n) &&
    (List.finRange 4).all (fun i => seats (.base .fg) i == i &&
      seats (.base (.head 4)) i == i && seats (.base (.ack 4)) i == i))
  let handlesBy := fun x o t => is.any (fun j =>
    match es.getD j (.tick 0 0) with
    | .deliver y a u => x == y && decide (t ≤ u ∧ u < deadline t) &&
        handlesTest (atIndex tr j x).st a o
    | _ => false)
  let excluded := fun x o t =>
    let k := (es.toList.takeWhile (fun e => decide (e.time < deadline t))).length
    excludesS p (atIndex tr k x).st o
  require "F1 broadcast" (emissions.all (fun row =>
    let (_, o, t) := row
    hs.all (fun x => if deadline t ≤ 22 && !excluded x o t then handlesBy x o t else true)))
  require "F1 acceptance relay" (is.all (fun i =>
    match es.getD i (.tick 0 0) with
    | .deliver y o t => (handledObjects (atIndex tr i y).st o).all (fun a =>
        if !processedS p (atIndex tr i y).st a && processedS p (atIndex tr (i + 1) y).st a then
          hs.all (fun x =>
            if !processedS p (atIndex tr (i + 1) x).st a && deadline t ≤ 22 && !excluded x a t then
              handlesBy x a t else true)
        else true)
    | _ => true))
  require "honest proposal at slot 4" (seats (.prop 4) ⟨0, by change 0 < 1; decide⟩ == 0 &&
    E.awake 0 16 && (emitted tr ((rho.tickIdx? 0 16).getD 0)).contains (prop 4 N))
  require "F2 participation" (decide (nQuorum p.n ≤
    (hs.filter (fun x => E.awake x 17 && E.awake x 18)).length))
  require "F3 common view" (N.pc == none &&
    hs.all (fun x => voterPC p (readTick tr x 17) 4 == none))
  require "F4 locks" (hs.all (fun x =>
    let st := readTick tr x 17
    st.base.obligations.all (fun row =>
      if st.base.now < row.2.2 && Block.compatible row.1 .genesis && 0 < row.1.depth then
        Block.preceq row.1 N.erase.parent else true)))
  require "other Formation premises" (decide (0 < 4 ∧ SA.gateTime p.toParams 4 ≤ 22 ∧ E.Δ ≤ 1) &&
    E.Δ == p.Δ)
  require "no ack or PC in the run" (states.all (fun i => hs.all (fun x =>
    let st := (atIndex tr i x).st
    st.ackPool.isEmpty && st.pcs.isEmpty)))
  require "missing retained target-prefix" (
    liveRoot p (readTick tr 0 16) (proposerPC p (readTick tr 0 16)) == A.erase &&
    hs.all (fun x =>
      let st := readTick tr x 17
      liveRoot p st (voterPC p st 4) == .genesis &&
        !eligible p st (headVotes p st 4) (headSupport p st 4) A.erase))
  require "C7 counterexample" (hs.all (fun x =>
    let st := readTick tr x 17
    E.awake x 17 && headVote p st 4 == B.erase && headVote p st 4 != N.erase) &&
    hs.all (fun x => !holdsN p (actView (readTick tr x 18)) 4 N.erase))
  require "formation-to-source counterexample" (p.actionTime 2 == 22 &&
    hs.all (fun x => fgSource p (readTick tr x 22) == none))
  IO.println s!"Formation counterexample: events={es.size}; h_s=3; faults=1"
  IO.println "Formation counterexample: proposal root=3; HEAD root=2; source=none"

#eval audit
#print axioms cachedStep_exact
#print axioms carriedObjects_exact
#print axioms handlesTest_exact
#print axioms cachedFold_exact
#print axioms fresh_committees
#print axioms linked_committee

end AvailableChain.PCSA.Run.Tests.FormationCounterexample
end
