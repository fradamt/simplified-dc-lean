module
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedEndpoint
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSARun.Proofs.Receipts

/-! F-23 exception (L47): each theorem here takes at most one regime record, Set or Contract
premise and concludes a field-level fact or another regime record. -/

public section

namespace AvailableChain.FGSA.Run

variable {ΔF : Time}

open Gen.Pure
open Gen.V2.Duty (faulty faulty_def awakeHonest awakeHonest_def SeedAt SeedAt_def)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- The old prefix fields imply the per-object regime at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem HealthyPrefix₂.of_legacy {b₀ : Time} (base : Base₂ p c E rho)
    (cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon)
    (healthy : V2.D.HealthyPrefixDelivery E rho b₀)
    (partBefore : ∀ t : Time, 0 ≤ t → t < b₀ →
      (faulty rho).card < (awakeHonest E rho t).card) :
    HealthyPrefix₂ p c E rho b₀ E.Δ := by
  refine ⟨base, cut, ?_, le_rfl, partBefore⟩
  rw [fgsaDelay_self]
  exact (Gen.V2.Duty.healthyPrefix_iff_by_const E rho b₀).1 healthy

/-- Recover the old prefix delivery law at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem HealthyPrefix₂.legacy_delivery {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ E.Δ) :
    V2.D.HealthyPrefixDelivery E rho b₀ := by
  apply (Gen.V2.Duty.healthyPrefix_iff_by_const E rho b₀).2
  have hh := h.healthy
  rw [fgsaDelay_self] at hh
  exact hh

/-- The old recovery fields imply the per-object regime at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem Recovery₂.of_legacy {G : Time}
    (core : Gen.V2.Duty.RecoveryCore (fgsa p c) (fgsaInterface p c) E rho G)
    (base : Base₂ p c E rho) (fault : (faulty rho).card ≤ (p.n - 1) / 3)
    (awake : ∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true)
    (gapPos : 4 * p.Δ ≤ G) : Recovery₂ p c E rho G E.Δ := by
  refine ⟨?_, le_rfl, core.gap, base, fault, awake, gapPos⟩
  rw [fgsaDelay_self]
  exact (Gen.V2.Duty.partialSynchrony_iff_by_const E rho).1 core.sync

/-- Recover the old recovery core at ΔF = Δ.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem Recovery₂.toRecoveryCore {G : Time} (h : Recovery₂ p c E rho G E.Δ) :
    Gen.V2.Duty.RecoveryCore (fgsa p c) (fgsaInterface p c) E rho G := by
  refine ⟨?_, h.gap⟩
  apply (Gen.V2.Duty.partialSynchrony_iff_by_const E rho).2
  have hh := h.sync
  rw [fgsaDelay_self] at hh
  exact hh

omit [DecidableEq V] in
theorem card_eq_n_of_linked (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    Fintype.card V = p.n :=
  (V2.D.CStar.seats_eq (ℓ := .base .fg) hL.toCStar trivial).symm

private theorem fgsa_honest_card (hL : V2.D.Linked (fgsaFamilies p c).linked rho) :
    rho.honest.card = p.n - (faulty rho).card := by
  rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_eq_n_of_linked hL]
  have hc := Finset.card_le_univ rho.honest
  rw [card_eq_n_of_linked hL] at hc
  omega

private theorem fgsa_awake_card_le (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (t : Time) :
    (awakeHonest E rho t).card ≤ p.n - (faulty rho).card := by
  rw [awakeHonest_def, ← fgsa_honest_card hL]
  exact Finset.card_filter_le _ _

theorem CleanPrefix₂.toCleanCut {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    CleanCut₂ p c E rho b₀ ΔF := h.toHealthyPrefix₂

theorem HealthyPrefix₂.faultQ_of_pos {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    (hb : 0 < b₀) : FaultQ p.n (faulty rho).card :=
  count_clean (h.partBefore 0 le_rfl hb) (fgsa_awake_card_le h.base.linked 0)

theorem CleanPrefix₂.faultQ {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    FaultQ p.n (faulty rho).card :=
  count_clean h.partAt (fgsa_awake_card_le h.base.linked b₀)

theorem HealthyPrefix₂.batch {b₀ t : Time} (h : HealthyPrefix₂ p c E rho b₀ ΔF)
    (ht : 0 ≤ t) (hb : t < b₀) : Batch (awakeHonest E rho t).card (faulty rho).card :=
  ⟨h.partBefore t ht hb⟩

theorem CleanPrefix₂.batchAt {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀ ΔF) :
    Batch (awakeHonest E rho b₀).card (faulty rho).card := ⟨h.partAt⟩

-- P3 §4.4 places regime producers here; F1.9 supplies these two bridges.
theorem Recovery₂.faultX_count_rec {G : Time} (h : Recovery₂ p c E rho G ΔF) :
    FaultX p.n (faulty rho).card := count_rec p.nPos h.fault

theorem Recovery₂.faultQ {G : Time} (h : Recovery₂ p c E rho G ΔF) :
    FaultQ p.n (faulty rho).card := by
  have hx := h.faultX_count_rec.lt
  constructor
  rw [qF_def] at hx ⊢
  omega

theorem Recovery₂.batch {G t : Time} (h : Recovery₂ p c E rho G ΔF)
    (ht : E.t_GST ≤ t) (hh : t ≤ rho.horizon) :
    Batch (awakeHonest E rho t).card (faulty rho).card := by
  have he : awakeHonest E rho t = rho.honest := by
    rw [awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun v hv => h.awake v hv t ht hh)
  rw [he, fgsa_honest_card h.base.linked]
  have hn := p.nPos
  have hf := h.fault
  exact ⟨by omega⟩

-- LabelSync and LabelFacts producers live in Gen.V2.Duty. Use them with the
-- default vote/gate times and the Batch producers above; do not copy them.
-- DeliveryWithin producers are Gen.V2.Duty.deliveryWithin_of_partialSynchrony
-- and Gen.V2.Duty.deliveryWithin_of_healthyPrefix, with no Base premise.

/- With the schedule already in Base, the two horizon delivery conditions agree. -/
omit [Fintype V] in
theorem fgsa_clean_delivery_iff (hS : V2.D.ScheduleWellFormed E rho) (hG : E.t_GST = 0) :
    V2.D.HealthyPrefixDelivery E rho rho.horizon ↔ V2.D.PartialSynchrony E rho := by
  have emitTime : ∀ v o t, V2.D.Run.emits E rho v o t → max t E.t_GST = t := by
    intro v o t h
    obtain ⟨i, hi, _⟩ := h
    have ht : 0 ≤ t := (hS.in_horizon _ (List.mem_of_getElem? hi)).1
    rw [hG, max_eq_left ht]
  have acceptTime : ∀ i v o t, V2.D.Run.acceptsAt E rho i v o t → max t E.t_GST = t := by
    intro i v o t h
    obtain ⟨⟨o', hi, _⟩, _⟩ := h
    have ht : 0 ≤ t := (hS.in_horizon _ (List.mem_of_getElem? hi)).1
    rw [hG, max_eq_left ht]
  constructor
  · intro h
    constructor
    · intro v hv o t he w hw
      rw [emitTime v o t he]
      exact h.broadcast_emitted v hv o t he w hw
    · intro v hv i o t ha w hw
      rw [acceptTime i v o t ha]
      exact h.relay_accepted v hv i o t ha w hw
  · intro h
    constructor
    · intro v hv o t he w hw
      have hb := h.broadcast_emitted v hv o t he w hw
      rw [emitTime v o t he] at hb
      exact hb
    · intro v hv i o t ha w hw
      have hr := h.relay_accepted v hv i o t ha w hw
      rw [acceptTime i v o t ha] at hr
      exact hr

/- T7.5 supplies the fixed reachable-state predicate at any explicit event cut. -/
omit [Fintype V] in
theorem fgsa_seed_reachable (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (start : Nat) :
    SeedAt E rho start (fun _ nd => Reachable p nd.st) := by
  rw [SeedAt_def]
  exact reachable_stateBefore E rho start

/- T7.7/T7.8 supplies the fixed processed predicate after acceptance.
The predicate selects one receiver; the cut is after its accepting event. -/
omit [Fintype V] in
theorem fgsa_seed_accepted (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hS : V2.D.ScheduleWellFormed E rho) (w : V) (o : Obj p) (i start : Nat) (t : Time)
    (ha : V2.D.Run.acceptsAt E rho i w o t) (his : i + 1 ≤ start)
    (hrf : V2.D.restartFree rho w (i + 1) start) :
    SeedAt E rho start (fun v nd => v = w → (fgsa p c).processed nd o = true) := by
  rw [SeedAt_def]
  intro v hv
  subst v
  exact processed_stable E rho hS w o (i + 1) start his hrf ha.2.2

theorem Outage₂.pos {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : 0 < b₀ := by
  have hT := h.order.1
  have hlag := h.lag
  have hd := p.deltaPos
  have hk : (2 : Time) ≤ p.k := by exact_mod_cast p.kLarge
  cases fast with
  | false =>
    change T + ((4 * (p.k : Time) - 1) * p.Δ - 3 * p.Δ) ≤ b₀ at hlag
    nlinarith
  | true =>
    change T + 4 * p.Δ ≤ b₀ at hlag
    linarith

theorem Outage₂.toCleanCut {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : CleanCut₂ p c E rho b₀ ΔF := h.pre

theorem Outage₂.faultQ {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁ ΔF) : FaultQ p.n (faulty rho).card :=
  h.pre.faultQ_of_pos h.pos

open AvailableChain.SimplexFG

/-- Blueprint 02:537–539; P3 erratum 13, Clean wrapper.
DC: Generic/Conditions.lean:134–156 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: healthy-prefix delivery supplies the vote-to-gate LabelSync;
geometry stays an explicit consumer obligation.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.gateTime p.toParams s ≤ b₀)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K⟩) t ∧
        baseVote (⟨.seat (.head s) q, K⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2
  exact fgsa_gateReceipt E rho h.base.valid h.base.noRestart h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- Blueprint 21 H.22:3100–3120; P3 erratum 13, Recovery wrapper.
DC: Generic/Conditions.lean:110–132 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: post-GST delivery supplies the vote-to-gate LabelSync.
GST ≤ voteTime s suffices; no earlier synchrony pair is used.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_gateReceipt_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head s)) q)
          (ofHead p ⟨.seat (.head s) q, K⟩) t ∧
        baseVote (⟨.seat (.head s) q, K⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i x).base.votes ∧
        K ∈ (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))).blocks ∧
        K.slot ≤ s ∧
        GridCO.stampVote (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)))
          (baseVote (⟨.seat (.head s) q, K⟩ : HeadWire p.n)) <
            GridCO.earlyTime p.toParams.engine s ∧
        GridCO.stampBlock (actView (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s))) K < GridCO.earlyTime p.toParams.engine s ∧
        Block.Preceq (eraseFG (clockPre p (storeAt p c E rho i x)
          (SA.gateTime p.toParams s)).fg.F) K ∧ Block.Preceq B K := by
  have hvd : SA.voteTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hhorizon : SA.gateTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? ht)).2
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hhorizon
  exact fgsa_gateReceipt E rho h.base.valid h.base.noRestart h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- P3 N1:2518–2525; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:134.
INTENTIONAL: the Clean wrapper uses the healthy prefix through v_s and
Gen LabelSync at (t_s - Δ, v_s); geometry remains a separate consumer input.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_score_eq_on_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  have hvd : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.voteTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) - p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hsync := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2
  exact fgsa_score_eq_on_run E rho h.base.valid h.base.noRestart h.base.delta s hsync
    hx hy hip hih hseat b raw sup rows hem hadm D hgeom

/-- P3 N1:2518–2525 and O25 §7; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:110.
INTENTIONAL: Recovery requires GST ≤ t_s - Δ, not merely GST ≤ v_s.
The actual HEAD tick supplies the horizon bound for Gen LabelSync.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_score_eq_on_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  have hvd : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.voteTime p.toParams s := by
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) - p.Δ + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hhorizon : SA.voteTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hih)).2
  have hsync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hhorizon
  exact fgsa_score_eq_on_run E rho h.base.valid h.base.noRestart h.base.delta s hsync
    hx hy hip hih hseat b raw sup rows hem hadm D hgeom

/-- P3 F1b.4b N1 C14 and C9/C11–C13/C19; blueprint 03:350–379.
DC: Goldfish/ProposalWalkTransportCore.lean:162–191; Conditions.lean:134.
INTENTIONAL: the Clean healthy prefix ends no earlier than v_s. Both N1
LabelSync records come from the same healthy prefix.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_ghost_transfer_sfx_on_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq b.parent (headVote p dst s) := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  exact fgsa_ghost_transfer_sfx_on_run E rho h.base.valid h.base.noRestart h.base.delta s
    hscore hwalk hx hy hip hih hseat b raw sup rows hem hadm D hgeom

/-- P3 F1b.4b N1 C14 and C9/C11–C13/C19; blueprint 03:350–379.
DC: Goldfish/ProposalWalkTransportCore.lean:162–191; Conditions.lean:110.
INTENTIONAL: Recovery requires GST ≤ t_s - Δ. The actual proposal and
HEAD ticks supply the horizons for the two N1 LabelSync records.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem fgsa_ghost_transfer_sfx_on_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq b.parent (headVote p dst s) := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hvh : SA.voteTime p.toParams s ≤ rho.horizon :=
    (h.base.valid.in_horizon _ (List.mem_of_getElem? hih)).2
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hvh
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hvh)
  exact fgsa_ghost_transfer_sfx_on_run E rho h.base.valid h.base.noRestart h.base.delta s
    hscore hwalk hx hy hip hih hseat b raw sup rows hem hadm D hgeom

/-- J2 HEAD clause on a Clean prefix; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:134.
INTENTIONAL: the Clean record supplies both G25/G11 synchronization intervals.
The consumer supplies the same per-reader geometry as the Shared producer.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_head_of_proposal_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D b) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  exact exactService_head_of_proposal E rho h.base.valid h.base.noRestart h.base.delta s
    hscore hwalk hx hip hseat b raw sup rows hem D hgeom

/-- J2 HEAD clause in Recovery; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:110.
INTENTIONAL: GST precedes t_s - Δ, and the HEAD horizon supplies both
G25/G11 synchronization intervals. Geometry remains a consumer obligation.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_head_of_proposal_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D b) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b := by
  intro hhorizon
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hhorizon
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hhorizon)
  exact exactService_head_of_proposal E rho h.base.valid h.base.noRestart h.base.delta s
    hscore hwalk hx hip hseat b raw sup rows hem D hgeom hhorizon

/-- J2 HEAD clause on a Clean prefix; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:134.
INTENTIONAL: the Clean record supplies both G25/G11 synchronization intervals.
Class (iii). The Shared supplier constructs walk and endpoint geometry
from the same per-reader elementary premises. Gate service stays separate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_head_of_retained_proposal_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b := by
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    (hpt.trans htv) hcut h.cut.2
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _)
    hpt (htv.trans hcut) h.cut.2
  have hgeom := fgsa_retainedExactHead_geometry_on_run E rho h.base.valid h.base.noRestart
    h.base.delta s hwalk hscore hx hip hseat b raw sup rows hem D hreads
  exact exactService_head_of_retained_proposal E rho h.base.valid h.base.delta s
    hip b raw sup rows hem D hgeom

/-- J2 HEAD clause in Recovery; 21 H.22:3100–3120, S1b E1–E6.
DC: Goldfish/PreparedV4CanonicalProposalDuty.lean:867–887; Conditions.lean:110.
INTENTIONAL: GST precedes t_s - Δ, and the HEAD horizon supplies both
G25/G11 synchronization intervals. Class (iii). The Shared supplier
constructs geometry from per-reader premises. Gate service stays separate.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_head_of_retained_proposal_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n))
    (hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams s))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams s)) s D b Kc) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some b := by
  intro hhorizon
  have hpt : SA.proposalTime p.toParams s - p.Δ + E.Δ ≤ SA.proposalTime p.toParams s := by
    rw [h.base.delta]
    exact le_of_eq (sub_add_cancel _ _)
  have htv : SA.proposalTime p.toParams s ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hscore := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST (hpt.trans htv) hhorizon
  have hwalk := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hpt (htv.trans hhorizon)
  have hgeom := fgsa_retainedExactHead_geometry_on_run E rho h.base.valid h.base.noRestart
    h.base.delta s hwalk hscore hx hip hseat b raw sup rows hem D hreads
  exact exactService_head_of_retained_proposal E rho h.base.valid h.base.delta s
    hip b raw sup rows hem D hgeom hhorizon

/-- P3 A.9 and blueprint 21 H.22 H3, conditional Clean exact service.
DC: Generic/Conditions.lean:134–156; UserConfirmationRecovery.lean:235.
INTENTIONAL: healthy-prefix delivery supplies LabelSync. Clean participation
alone need not reach the fast threshold, so that count stays explicit.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_clean
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hcut : SA.gateTime p.toParams v ≤ b₀)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤ (awakeHonest E rho (SA.voteTime p.toParams v)).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hvpos : 0 ≤ SA.voteTime p.toParams v := by
    change 0 ≤ 4 * p.Δ * (v : Int) + p.Δ
    have hd := p.deltaPos
    positivity
  have hvcut : SA.voteTime p.toParams v < b₀ := by
    have hd : 0 < E.Δ := h.base.delta.symm ▸ p.deltaPos
    linarith
  apply exactService_of_head_and_gate E rho h.base.valid h.base.noRestart h.base.delta
    h.base.cstar v Q hne hhead
    (fun _ => Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2)
    _ hgeometry
  intro _
  exact exactService_participation_of_card E rho h.base.cstar v
    ⟨h.partBefore _ hvpos hvcut⟩ hfast

/-- P3 A.9 and blueprint 21 H.22 H3, conditional Recovery exact service.
DC: Generic/Conditions.lean:110–132; UserConfirmationRecovery.lean:235.
INTENTIONAL: post-GST waking and the one-third fault bound supply the SA
fast count. Cardinality uses only the fresh HEAD-seat bijection.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_recovery
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams v)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, headAtLabel p c E rho x v = some Q)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate E rho h.base.valid h.base.noRestart h.base.delta
    h.base.cstar v Q hne hhead
    (fun hh => Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hh) _ hgeometry
  intro hh
  have hvhor : SA.voteTime p.toParams v ≤ rho.horizon := by
    have hd : 0 < E.Δ := h.base.delta.symm ▸ p.deltaPos
    linarith
  have hawake : awakeHonest E rho (SA.voteTime p.toParams v) = rho.honest := by
    rw [awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun x hx => h.awake x hx _ hGST hvhor)
  have hn : Fintype.card V = p.n :=
    (V2.D.CStar.seats_eq (ℓ := .base (.head v)) h.base.cstar trivial).symm
  have hcard : (faulty rho).card + rho.honest.card = p.n := by
    rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hn]
    have hc := Finset.card_le_univ rho.honest
    rw [hn] at hc
    omega
  have hf := h.fault
  have hp := p.nPos
  apply exactService_participation_of_card E rho h.base.cstar v
  · rw [hawake]
    exact ⟨by omega⟩
  · rw [hawake]
    change (p.n + 1) / 2 ≤ rho.honest.card
    omega

end AvailableChain.FGSA.Run
end
