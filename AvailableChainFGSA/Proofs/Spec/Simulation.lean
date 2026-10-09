module
public import AvailableChainFGSA.Proofs.Spec.Clock
public import AvailableChainFGSA.Proofs.Spec.Handlers
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainEngineV2.Conditions.Duty.Schedule

public section

namespace AvailableChain.FGSA.Spec

/-! WP12b: Ruling U's simulation-only filter removes non-Assigned proposal chains.
The identity gate, store invariant, emission identity, and event stutter are proved below.
The old raw-erasure trace remains as regression evidence. A second initialized trace
shows that restart between public ticks changes block acceptance, even on Assigned
chains. Full block-step simulation, matched-cut induction, and claim transfer stop there.
No Lean protocol or existing claim is changed. -/

/-- The last-tick cutoff can be removed at a gate when all stored votes precede it. -/
theorem spec_lateVotes_eq_pool (p : Params) (st : GridCO.State p.n .root) (s : Slot)
    (h : ∀ o ∈ GridCO.votesAt st s, GridCO.stampVote st o < SA.gateTime p.toParams s) :
    GridCO.lateVotes p.toParams.engine st s = GridCO.votesAt st s := by
  apply List.filter_eq_self.mpr
  intro o ho
  exact decide_eq_true (h o ho)

/-- The run adapter preserves the existing all-wire boundary check. -/
theorem spec_run_wire_check (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    (Run.fgsa p Run.unitCodec).wellFormed (Run.ofWire p (deliveryWire assigned o)) =
      (wellFormed p o && admissionValid assigned o) := by
  change FGSA.wellFormed p (Run.toWire p (Run.ofWire p (deliveryWire assigned o))) = _
  have hw : Run.toWire p (Run.ofWire p (deliveryWire assigned o)) =
      deliveryWire assigned o := (Run.toWireEquiv p).right_inv _
  rw [hw]
  exact delivery_check_embedding p assigned o

/-- Restart preserves the durable anti-slashing record and resets the Lean store. -/
theorem spec_restart_durable (p : Params) (nd : Run.Node p) :
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd)).record =
      nd.record ∧
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd)).st.base.now =
      0 := ⟨rfl, rfl⟩

/-- The pinned spec keeps the clock at restart; raw clock equality cannot cover that cut. -/
theorem spec_restart_clock_mismatch (p : Params) (nd : Run.Node p) (t : Time) (ht : t ≠ 0) :
    ((Run.fgsa p Run.unitCodec).restore nd.record).st.base.now ≠ t := Ne.symm ht

/-- Computable recursive proposer test, used only by the simulation. -/
def specAssignedCheck {n : Nat} (assigned : Slot → Fin n) : Block n → Bool
  | .genesis => true
  | .node P s i _ _ _ _ => (i == assigned s) && specAssignedCheck assigned P

theorem spec_assigned_check_iff {n : Nat} (assigned : Slot → Fin n) (B : Block n) :
    specAssignedCheck assigned B = true ↔ B.Assigned assigned := by
  induction B with
  | genesis => simp [specAssignedCheck, Block.Assigned]
  | node P s i r rows raw support ih =>
      simp [specAssignedCheck, Block.Assigned, ih]

/-- The two identity conditions of FG admission. Other checks can only refuse more. -/
def specIdentityGate {n : Nat} (assigned : Slot → Fin n) (held : List (Block n)) :
    Block n → Bool
  | .genesis => false
  | .node P s i _ _ _ _ => (i == assigned s) && decide (P ∈ held)

/-- Initialization and admitted-parent closure supply Assigned; it is not a claim premise. -/
theorem spec_identity_gate_assigned {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : specIdentityGate assigned held B = true) :
    B.Assigned assigned := by
  cases B with
  | genesis => trivial
  | node P s i r rows raw support =>
      simp only [specIdentityGate, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      exact ⟨hB.1, hheld P hB.2⟩

/-- A non-Assigned payload fails before writes or carried-object handlers. -/
theorem spec_identity_gate_refused {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : ¬ B.Assigned assigned) :
    specIdentityGate assigned held B = false := by
  cases h : specIdentityGate assigned held B
  · rfl
  · exact False.elim (hB (spec_identity_gate_assigned assigned held hheld B h))

/-- Refusal keeps both states and produces no output, for every remaining block handler. -/
theorem spec_identity_refusal_step {n : Nat} {σ α O : Type}
    (assigned : Slot → Fin n) (held : List (Block n))
    (hheld : ∀ B ∈ held, B.Assigned assigned) (B : Block n)
    (hB : ¬ B.Assigned assigned) (next : σ × α → (σ × α) × List O) (st : σ × α) :
    (if specIdentityGate assigned held B then next st else (st, [])) = (st, []) := by
  rw [spec_identity_gate_refused assigned held hheld B hB]
  rfl

/-- Admitted blocks have Assigned parents, so plain Lean membership is exact here. -/
theorem spec_assigned_parent_membership {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (B : Block n) (hB : B.Assigned assigned) :
    B.embed.parent ∈ held.map Block.embed ↔ B.parent ∈ held := by
  have hp : B.parent.Assigned assigned := by
    cases B with
    | genesis => trivial
    | node P s i r rows raw support => exact hB.2
  rw [embed_parent, List.mem_map]
  constructor
  · rintro ⟨P, hP, heq⟩
    exact (assigned_embed_injective assigned P B.parent (hheld P hP) hp heq) ▸ hP
  · intro h
    exact ⟨B.parent, h, rfl⟩

/-- Identity-store cuts: the trace keeps refusals, accepted blocks, and restarts.
The Boolean is the result of the remaining admission checks. -/
def specIdentityStoreStep {n : Nat} (assigned : Slot → Fin n) (held : List (Block n)) :
    Option (Block n × Bool) → List (Block n)
  | none => [.genesis]
  | some (B, accepted) =>
      if specIdentityGate assigned held B && accepted then held ++ [B] else held

/-- The identity invariant follows by induction from initialization, at every cut.
This is the identity-store projection, not the full matched-state induction. -/
theorem spec_identity_store_induction {n : Nat} (assigned : Slot → Fin n)
    (events : List (Option (Block n × Bool))) :
    ∀ B ∈ events.foldl (specIdentityStoreStep assigned) [.genesis], B.Assigned assigned := by
  have step (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
      (event : Option (Block n × Bool)) :
      ∀ B ∈ specIdentityStoreStep assigned held event, B.Assigned assigned := by
    cases event with
    | none => simp [specIdentityStoreStep, Block.Assigned]
    | some item =>
        rcases item with ⟨B, accepted⟩
        simp only [specIdentityStoreStep]
        split_ifs with h
        · intro C hC
          rcases List.mem_append.mp hC with hc | hc
          · exact hheld C hc
          · have heq := List.mem_singleton.mp hc
            subst C
            simp only [Bool.and_eq_true] at h
            exact spec_identity_gate_assigned assigned held hheld B h.1
        · exact hheld
  have fold (xs : List (Option (Block n × Bool))) (held : List (Block n))
      (hheld : ∀ B ∈ held, B.Assigned assigned) :
      ∀ B ∈ xs.foldl (specIdentityStoreStep assigned) held, B.Assigned assigned := by
    induction xs generalizing held with
    | nil => exact hheld
    | cons x xs ih => exact ih _ (step held hheld x)
  exact fold events [.genesis] (by simp [Block.Assigned])

/-- An honest proposal from a held parent passes the recursive identity filter. -/
theorem spec_assigned_proposal_emission {n : Nat} (assigned : Slot → Fin n)
    (held : List (Block n)) (hheld : ∀ B ∈ held, B.Assigned assigned)
    (P : Block n) (hP : P ∈ held) (s : Slot) (root : BlockId)
    (rows : List (RowWire n)) (raw support : List (HeadWire n)) :
    specAssignedCheck assigned (.node P s (assigned s) root rows raw support) = true :=
  (spec_assigned_check_iff assigned _).mpr ⟨rfl, hheld P hP⟩

/-- Full source objects remain available; this filter constructs only target deliveries.
A removed source delivery maps to zero target events, never to absent authentication. -/
def specSimulationWire (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    Option (Run.Obj p) :=
  let identities := match o.payload with
    | .proposal B => specAssignedCheck assigned B
    | _ => true
  if identities && wellFormed p o && admissionValid assigned o then
    some (Run.ofWire p (deliveryWire assigned o)) else none

/-- Non-Assigned chains are stutters in the target event list. -/
theorem spec_simulation_wire_stutter (p : Params) (assigned : Slot → Fin p.n)
    (auth : Auth Label p.n) (B : Block p.n) (hB : ¬ B.Assigned assigned) :
    specSimulationWire p assigned ⟨auth, .proposal B⟩ = none := by
  have hb : specAssignedCheck assigned B = false := by
    cases h : specAssignedCheck assigned B
    · rfl
    · exact False.elim (hB ((spec_assigned_check_iff assigned B).mp h))
  simp [specSimulationWire, hb]

/-- Every retained delivery passes the target wire check. Dependency and freshness
checks still need the state relation; this is not an ExecutionValid theorem. -/
theorem spec_simulation_wire_valid (p : Params) (assigned : Slot → Fin p.n)
    (o : Wire p.n) (q : Run.Obj p) (hq : specSimulationWire p assigned o = some q) :
    (Run.fgsa p Run.unitCodec).wellFormed q = true := by
  simp only [specSimulationWire] at hq
  split_ifs at hq with h
  · have hg : (wellFormed p o && admissionValid assigned o) = true := by
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1.2, h.2⟩
    cases Option.some.inj hq
    rw [spec_run_wire_check, hg]

/-- A valid Assigned proposal keeps its authentication and all its signed lists. -/
theorem spec_simulation_proposal_retained (p : Params) (assigned : Slot → Fin p.n)
    (auth : Auth Label p.n) (B : Block p.n) (hB : B.Assigned assigned)
    (hw : wellFormed p ⟨auth, .proposal B⟩ = true)
    (ha : admissionValid assigned ⟨auth, .proposal B⟩ = true) :
    specSimulationWire p assigned ⟨auth, .proposal B⟩ =
      some (Run.ofWire p (Wire.embed ⟨auth, .proposal B⟩)) := by
  have ha' := ha
  simp only [admissionValid, Bool.and_eq_true] at ha'
  have hp := ha'.1
  simp [specSimulationWire, (spec_assigned_check_iff assigned B).mpr hB, hw, ha,
    deliveryWire, hp]

/-- Preserve ticks and restarts; filter refused deliveries without changing time or node. -/
def specSimulationEvent {V : Type} (p : Params) (assigned : Slot → Fin p.n) :
    V2.Event V (Wire p.n) → Option (V2.Event V (Run.Obj p))
  | .tick v t => some (.tick v t)
  | .restart v t => some (.restart v t)
  | .deliver v o t => (specSimulationWire p assigned o).map (fun q => .deliver v q t)

theorem spec_simulation_event_stutter {V : Type} (p : Params)
    (assigned : Slot → Fin p.n) (v : V) (t : Time) (auth : Auth Label p.n)
    (B : Block p.n) (hB : ¬ B.Assigned assigned) :
    specSimulationEvent p assigned (.deliver v ⟨auth, .proposal B⟩ t) = none := by
  simp [specSimulationEvent, spec_simulation_wire_stutter p assigned auth B hB]

theorem spec_simulation_event_key {V : Type} (p : Params) (assigned : Slot → Fin p.n)
    (e : V2.Event V (Wire p.n)) (f : V2.Event V (Run.Obj p))
    (h : specSimulationEvent p assigned e = some f) :
    f.key = e.key ∧ f.node = e.node := by
  cases e with
  | tick v t => cases Option.some.inj h; exact ⟨rfl, rfl⟩
  | restart v t => cases Option.some.inj h; exact ⟨rfl, rfl⟩
  | deliver v o t =>
      simp only [specSimulationEvent, Option.map_eq_some_iff] at h
      obtain ⟨q, _, rfl⟩ := h
      exact ⟨rfl, rfl⟩

/-- A small parameter set with distinct parent and child roots. -/
abbrev parentIdentityParams : Params :=
  { Δ := 1, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun d => ⟨d.slot + 6⟩ }

def parentIdentityAssigned (_ : Slot) : Fin 2 := 0

def parentIdentityHeld : Block 2 := .node .genesis 1 0 ⟨7⟩ [] [] []

def parentIdentityAbsent : Block 2 := .node .genesis 1 1 ⟨7⟩ [] [] []

def parentIdentityChild : Block 2 := .node parentIdentityAbsent 2 0 ⟨8⟩ [] [] []

def parentIdentityGoodChild : Block 2 := .node parentIdentityHeld 2 0 ⟨8⟩ [] [] []

abbrev parentIdentityWire : Wire 2 := ⟨.proposer 2, .proposal parentIdentityChild⟩

/-- One awake local tick for validator 1, with immediate self-delivery.
Validator 1 has no proposal duty under the fixed assignment. -/
def parentIdentityTick (nd : Run.Node parentIdentityParams) (t : Nat) :
    Run.Node parentIdentityParams := Id.run do
  let p := parentIdentityParams
  let mut nd := { nd with st := FGSA.clock p nd.st t }
  let s := p.slotOf t
  if (t : Time) = SA.voteTime p.toParams s then
    let H := Next.headVoteNext p nd.st s
    nd := { nd with st := process p nd.st ⟨.seat (.head s) 1, .head H.root⟩ }
  if (t : Time) = p.actionTime ((s - 1) / p.R) then
    let (row, record) := Next.attestNext p nd.st nd.record 1
    nd := { nd with record := record }
    if let some a := row then
      nd := { nd with st := process p nd.st ⟨.seat .fg 1, .row a⟩ }
  return nd

/-- Public ticks 0 through 4, the valid parent delivery at 4, then ticks 5 through 8. -/
def parentIdentityBefore : Run.Node parentIdentityParams :=
  let nd := (List.range 5).foldl parentIdentityTick
    ⟨FGSA.initial 2, SimplexFG.RecordOnce.initial⟩
  let nd := { nd with
    st := process parentIdentityParams nd.st
      (Wire.embed ⟨.proposer 1, .proposal parentIdentityHeld⟩) }
  ([5, 6, 7, 8] : List Nat).foldl parentIdentityTick nd

/-- The all-wire erasure loses an ancestor identity even with a valid top proposer. -/
theorem spec_parent_identity_erasure :
    parentIdentityAbsent ≠ parentIdentityHeld ∧
    parentIdentityChild.parent ∉ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityGoodChild.parent ∈ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityChild.embed = parentIdentityGoodChild.embed ∧
    deliveryWire parentIdentityAssigned parentIdentityWire =
      deliveryWire parentIdentityAssigned
        ⟨.proposer 2, .proposal parentIdentityGoodChild⟩ := by decide

set_option maxRecDepth 4096 in
/-- Concrete refusal mismatch at time 8, after every earlier public tick.
The checked parent set is exactly genesis and the first received proposal. -/
theorem spec_parent_identity_trace :
    parentIdentityBefore.st.namedBodies = [.genesis, parentIdentityHeld.embed] ∧
    parentIdentityBefore.st.base.now = 8 ∧
    wellFormed parentIdentityParams parentIdentityWire = true ∧
    admissionValid parentIdentityAssigned parentIdentityWire = true ∧
    FGSA.wellFormed parentIdentityParams
      (deliveryWire parentIdentityAssigned parentIdentityWire) = true ∧
    namedParentHeld parentIdentityBefore.st parentIdentityChild.embed = true ∧
    (process parentIdentityParams parentIdentityBefore.st
      (deliveryWire parentIdentityAssigned parentIdentityWire)).proposals.length = 2 := by
  decide

/-- Proposer-only aliases share a root without distinct digest inputs. -/
theorem spec_parent_identity_root : parentIdentityAbsent.root = parentIdentityHeld.root := by
  decide

/-- The old ancestor counterexample is removed by the simulation filter. -/
theorem spec_parent_identity_filtered :
    specSimulationWire parentIdentityParams parentIdentityAssigned parentIdentityWire = none ∧
    specIdentityGate parentIdentityAssigned [.genesis, parentIdentityHeld]
      parentIdentityChild = false := by decide

/-- A restart at 9 is strictly between public ticks 8 and 10. -/
abbrev specRestartParams : Params :=
  { Δ := 2, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun d => ⟨d.slot + 6⟩ }

def specRestartEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun _ _ => true⟩

def specRestartWire : Wire 2 := ⟨.proposer 1, .proposal parentIdentityHeld⟩

/-- The empty post-restart spec store, represented with the current clock.
This does not run an extra tick or duty. -/
def specRestartCurrent : State 2 := { FGSA.initial 2 with base.now := 9 }

/-- The exact prefix has every public tick and immediate HEAD self-delivery.
The only honest node is 1; proposer 0 can supply the empty proposal. -/
def specRestartRun : V2.D.Run (Fin 2) (Run.fgsa specRestartParams Run.unitCodec) where
  honest := {1}
  horizon := 9
  events := [.tick 1 0, .tick 1 2,
    .deliver 1 (Run.ofWire specRestartParams ⟨.seat (.head 0) 1, .head genesisRoot⟩) 2,
    .tick 1 4, .tick 1 6, .tick 1 8, .restart 1 9,
    .deliver 1 (Run.ofWire specRestartParams specRestartWire.embed) 9]
  seatOf := fun l i => match l with
    | .base _ => i
    | .prop _ => 0
  input := fun _ _ => ()

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation unfolds the eight-event engine prefix and the block handler.
/-- All identity, parent, slot and row checks of the spec accept this empty block.
Lean refuses it after restore because its clock has become zero. The last two
conjuncts compute the initialized engine prefix and the differing post-delivery cut. -/
theorem spec_restart_block_trace :
    parentIdentityHeld.Assigned parentIdentityAssigned ∧
    wellFormed specRestartParams specRestartWire = true ∧
    admissionValid parentIdentityAssigned specRestartWire = true ∧
    specIdentityGate parentIdentityAssigned [.genesis] parentIdentityHeld = true ∧
    blockAccepted specRestartParams specRestartCurrent 1 parentIdentityHeld.embed
      .genesis = true ∧
    (process specRestartParams specRestartCurrent specRestartWire.embed).proposals.length = 1 ∧
    (V2.D.Run.stateBefore specRestartEnv specRestartRun 7 1).st.base.now = 0 ∧
    (V2.D.Run.final specRestartEnv specRestartRun 1).st.proposals.length = 0 := by
  refine ⟨⟨rfl, trivial⟩, ?_⟩
  decide

set_option maxRecDepth 4096 in
/-- The counterexample obeys the engine's ordered, total public-tick schedule. -/
theorem spec_restart_schedule : V2.D.ScheduleWellFormed specRestartEnv specRestartRun := by
  constructor
  · decide
  · decide
  · decide
  · intro e he
    simp only [specRestartRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    simp only [specRestartRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v t ht
    simp only [specRestartRun, List.mem_cons, List.not_mem_nil, or_false,
      V2.Event.tick.injEq, reduceCtorEq, or_false, false_or] at ht
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · intro v hv t ht _ ht9
    have hv' : v = 1 := Finset.mem_singleton.mp hv
    subst v
    obtain ⟨k, rfl⟩ := ht
    change (k : Int) * 2 ≤ 9 at ht9
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The only deliveries in the restart fixture, with their exact list positions. -/
theorem spec_restart_delivery_cases (i : Nat) (v : Fin 2) (o : Run.Obj specRestartParams)
    (t : Time) (h : specRestartRun.events[i]? = some (.deliver v o t)) :
    (i = 2 ∧ v = 1 ∧
      o = Run.ofWire specRestartParams ⟨.seat (.head 0) 1, .head genesisRoot⟩ ∧ t = 2) ∨
    (i = 7 ∧ v = 1 ∧ o = Run.ofWire specRestartParams specRestartWire.embed ∧ t = 9) := by
  have hi : i < 8 := (List.getElem?_eq_some_iff.mp h).1
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [specRestartRun, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- Even the refused block meets every engine delivery condition. -/
theorem spec_restart_delivery_valid :
    V2.D.DeliveryWellFormed specRestartEnv specRestartRun := by
  constructor
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide
  · intro i v o t h
    rcases spec_restart_delivery_cases i v o t h with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

set_option maxRecDepth 4096 in
/-- Honest signatures come from the immediate HEAD emission; proposer 0 is faulty. -/
theorem spec_restart_signatures :
    V2.D.UnforgeableSignatures specRestartEnv specRestartRun := by
  constructor
  · intro v o t hp u hu hh
    obtain ⟨i, hi⟩ := hp
    have hu' : u = 1 := Finset.mem_singleton.mp hu
    subst u
    rcases spec_restart_delivery_cases i v o t hi with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · refine ⟨2, le_rfl, 1, rfl, ?_⟩
      change _ ∈ [Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩]
      exact List.mem_singleton_self _
    · change some (0 : Fin 2) = some 1 at hh
      contradiction
  · intro v o t hp o' hc
    obtain ⟨i, hi⟩ := hp
    rcases spec_restart_delivery_cases i v o t hi with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact False.elim hc
    · change o' ∈ [] ∨ o' ∈ [] ∨ o' ∈ [] at hc
      simp at hc

/-- The target trace is a valid execution, not only an arbitrary handler state. -/
theorem spec_restart_execution_valid : V2.D.ExecutionValid specRestartEnv specRestartRun :=
  { spec_restart_schedule, spec_restart_delivery_valid, spec_restart_signatures with }

set_option maxRecDepth 4096 in
/-- Every self-visible emission is delivered immediately, before the next tick. -/
theorem spec_restart_self_delivery : V2.D.SelfDelivery specRestartEnv specRestartRun := by
  intro i v t h o ho _
  have hi : i < 8 := (List.getElem?_eq_some_iff.mp h).1
  have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [specRestartRun, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, V2.Event.tick.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  · change o ∈ [] at ho
    contradiction
  · have heq : o = Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩ := by
      change o ∈ [Run.ofWire specRestartParams
        ⟨.seat (.head 0) 1, .head genesisRoot⟩] at ho
      exact List.mem_singleton.mp ho
    subst o
    exact ⟨2, by decide, rfl⟩
  · change o ∈ [] at ho
    contradiction
  · change o ∈ [] at ho
    contradiction
  · change o ∈ [] at ho
    contradiction

/-- The corrective tick at 9 would violate the target's public-time condition. -/
theorem spec_restart_no_public_tick : ¬ V2.PublicTime specRestartEnv 9 := by
  rintro ⟨k, hk⟩
  change (9 : Int) = (k : Int) * 2 at hk
  omega

end AvailableChain.FGSA.Spec
end
