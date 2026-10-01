module
public import AvailableChainFGSAProofs.Proofs.Shared.GateReceipt
public import AvailableChainFGSAProofs.Proofs.Shared.ScoreRun
public import AvailableChainGeneric.Proofs.V2.Regimes
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainFGSARun.Proofs.Receipts

/-! F-23 exception (L47): each theorem here takes at most one regime record, Set or Contract
premise and concludes a field-level fact or another regime record. -/

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure
open Gen.V2 (faulty faulty_def awakeHonest awakeHonest_def SeedAt SeedAt_def)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {E : Generic.Env V} {rho : V2.Run V (fgsa p c)}

omit [DecidableEq V] in
theorem card_eq_n_of_linked (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    Fintype.card V = p.n :=
  (V2.CStar.seats_eq (ℓ := .base (.fg 0)) hL.toCStar trivial).symm

private theorem fgsa_honest_card (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    rho.honest.card = p.n - (faulty rho).card := by
  rw [faulty_def, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_eq_n_of_linked hL]
  have hc := Finset.card_le_univ rho.honest
  rw [card_eq_n_of_linked hL] at hc
  omega

private theorem fgsa_awake_card_le (hL : V2.Linked (fgsaFamilies p c).linked rho) (t : Time) :
    (awakeHonest E rho t).card ≤ p.n - (faulty rho).card := by
  rw [awakeHonest_def, ← fgsa_honest_card hL]
  exact Finset.card_filter_le _ _

theorem CleanPrefix₂.toCleanCut {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀) :
    CleanCut₂ p c E rho b₀ := h.toHealthyPrefix₂

theorem HealthyPrefix₂.faultQ_of_pos {b₀ : Time} (h : HealthyPrefix₂ p c E rho b₀)
    (hb : 0 < b₀) : FaultQ p.n (faulty rho).card :=
  count_clean (h.partBefore 0 le_rfl hb) (fgsa_awake_card_le h.base.linked 0)

theorem CleanPrefix₂.faultQ {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀) :
    FaultQ p.n (faulty rho).card :=
  count_clean h.partAt (fgsa_awake_card_le h.base.linked b₀)

theorem HealthyPrefix₂.batch {b₀ t : Time} (h : HealthyPrefix₂ p c E rho b₀)
    (ht : 0 ≤ t) (hb : t < b₀) : Batch (awakeHonest E rho t).card (faulty rho).card :=
  ⟨h.partBefore t ht hb⟩

theorem CleanPrefix₂.batchAt {b₀ : Time} (h : CleanPrefix₂ p c E rho b₀) :
    Batch (awakeHonest E rho b₀).card (faulty rho).card := ⟨h.partAt⟩

-- P3 §4.4 places regime producers here; F1.9 supplies these two bridges.
theorem Recovery₂.faultX_count_rec {G : Time} (h : Recovery₂ p c E rho G) :
    FaultX p.n (faulty rho).card := count_rec p.nPos h.fault

theorem Recovery₂.faultQ {G : Time} (h : Recovery₂ p c E rho G) :
    FaultQ p.n (faulty rho).card := by
  have hx := h.faultX_count_rec.lt
  constructor
  rw [qF_def] at hx ⊢
  omega

theorem Recovery₂.batch {G t : Time} (h : Recovery₂ p c E rho G)
    (ht : E.t_GST ≤ t) (hh : t ≤ rho.horizon) :
    Batch (awakeHonest E rho t).card (faulty rho).card := by
  have he : awakeHonest E rho t = rho.honest := by
    rw [awakeHonest_def]
    exact Finset.filter_eq_self.mpr (fun v hv => h.awake v hv t ht hh)
  rw [he, fgsa_honest_card h.base.linked]
  have hn := p.nPos
  have hf := h.fault
  exact ⟨by omega⟩

-- LabelSync and LabelFacts producers live in Gen.V2. Use them with the
-- default vote/gate times and the Batch producers above; do not copy them.
-- DeliveryWithin producers are Gen.V2.deliveryWithin_of_partialSynchrony
-- and Gen.V2.deliveryWithin_of_healthyPrefix, with no Base premise.

/- With the schedule already in Base, the two horizon delivery conditions agree. -/
omit [Fintype V] in
theorem fgsa_clean_delivery_iff (hS : V2.ScheduleWellFormed E rho) (hG : E.t_GST = 0) :
    V2.HealthyPrefixDelivery E rho rho.horizon ↔ V2.PartialSynchrony E rho := by
  have emitTime : ∀ v o t, V2.Run.emits E rho v o t → max t E.t_GST = t := by
    intro v o t h
    obtain ⟨i, hi, _⟩ := h
    have ht : 0 ≤ t := (hS.in_horizon _ (List.mem_of_getElem? hi)).1
    rw [hG, max_eq_left ht]
  have acceptTime : ∀ i v o t, V2.Run.acceptsAt E rho i v o t → max t E.t_GST = t := by
    intro i v o t h
    obtain ⟨⟨o', hi, _⟩, _⟩ := h
    have ht : 0 ≤ t := (hS.in_horizon _ (List.mem_of_getElem? hi)).1
    rw [hG, max_eq_left ht]
  constructor
  · intro h
    constructor
    · intro v hv o t he w hw
      rw [emitTime v o t he]
      exact h.broadcast v hv o t he w hw
    · intro v hv i o t ha w hw
      rw [acceptTime i v o t ha]
      exact h.relay v hv i o t ha w hw
  · intro h
    constructor
    · intro v hv o t he w hw
      have hb := h.broadcast v hv o t he w hw
      rw [emitTime v o t he] at hb
      exact hb
    · intro v hv i o t ha w hw
      have hr := h.relay v hv i o t ha w hw
      rw [acceptTime i v o t ha] at hr
      exact hr

/- T7.5 supplies the fixed reachable-state predicate at any explicit event cut. -/
omit [Fintype V] in
theorem fgsa_seed_reachable (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (start : Nat) :
    SeedAt E rho start (fun _ nd => Reachable p nd.st) := by
  rw [SeedAt_def]
  exact reachable_stateBefore E rho start

/- T7.7/T7.8 supplies the fixed processed predicate after acceptance.
The predicate selects one receiver; the cut is after its accepting event. -/
omit [Fintype V] in
theorem fgsa_seed_accepted (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hS : V2.ScheduleWellFormed E rho) (w : V) (o : Obj p) (i start : Nat) (t : Time)
    (ha : V2.Run.acceptsAt E rho i w o t) (his : i + 1 ≤ start)
    (hrf : V2.restartFree rho w (i + 1) start) :
    SeedAt E rho start (fun v nd => v = w → (fgsa p c).processed nd o = true) := by
  rw [SeedAt_def]
  intro v hv
  subst v
  exact processed_stable E rho hS w o (i + 1) start his hrf ha.2.2

theorem Outage₂.pos {fast : Bool} {T b₀ b₁ : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁) : 0 < b₀ := by
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

theorem Outage₂.toCleanCut {fast : Bool} {T b₀ b₁ : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁) : CleanCut₂ p c E rho b₀ := h.pre

theorem Outage₂.faultQ {fast : Bool} {T b₀ b₁ : Time}
    (h : Outage₂ p c fast E rho T b₀ b₁) : FaultQ p.n (faulty rho).card :=
  h.pre.faultQ_of_pos h.pos

open AvailableChain.SimplexFG

/-- Blueprint 02:537–539; P3 erratum 13, Clean wrapper.
DC: Generic/Conditions.lean:134–156 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: healthy-prefix delivery supplies the vote-to-gate LabelSync;
geometry stays an explicit consumer obligation. -/
theorem fgsa_gateReceipt_clean
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀)
    (s : Slot) (hcut : SA.gateTime p.toParams s ≤ b₀)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.Run.emits E rho (rho.seatOf (.base (.head s)) q)
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
  have hsync := Gen.V2.LabelSync.of_cleanCut E rho b₀ _ _ h.healthy hvd hcut h.cut.2
  exact fgsa_gateReceipt E rho h.base.valid h.base.noRestart h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- Blueprint 21 H.22:3100–3120; P3 erratum 13, Recovery wrapper.
DC: Generic/Conditions.lean:110–132 and Goldfish/Confirmation.lean:434–441.
INTENTIONAL: post-GST delivery supplies the vote-to-gate LabelSync.
GST ≤ voteTime s suffices; no earlier synchrony pair is used. -/
theorem fgsa_gateReceipt_recovery
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G)
    (s : Slot) (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    {i : Nat} {x : V} (ht : IsGateTick p c rho i x s) (B : Block)
    (hgeom : GateReceiptGeometry E rho
      (clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)) s B) :
    ∀ q : Fin p.n, rho.seatOf (.base (.head s)) q ∈ rho.honest →
      E.awake (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s) = true →
      ∃ K t,
        rho.seatOf (.base (.head s)) q ∈ rho.honest ∧
        V2.Run.emits E rho (rho.seatOf (.base (.head s)) q)
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
  have hsync := Gen.V2.LabelSync.of_recovery E rho _ _ h.sync hGST hvd hhorizon
  exact fgsa_gateReceipt E rho h.base.valid h.base.noRestart h.base.delta h.base.cstar
    s hsync ht B hgeom

/-- P3 N1:2518–2525; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:134.
INTENTIONAL: the Clean wrapper uses the healthy prefix through v_s and
Gen LabelSync at (t_s - Δ, v_s); geometry remains a separate consumer input. -/
theorem fgsa_score_eq_on_clean
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀)
    (s : Slot) (hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.Run.stateBefore E rho ih y).st.base.blocks)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
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
  have hsync := Gen.V2.LabelSync.of_cleanCut E rho b₀ _ _ h.healthy hvd hcut h.cut.2
  exact fgsa_score_eq_on_run E rho h.base.valid h.base.noRestart h.base.delta s hsync
    hx hy hip hih hseat b raw sup rows hem hadm D hgeom

/-- P3 N1:2518–2525 and O25 §7; blueprint 03:256–317.
DC: Goldfish/ProposalSnapshotBridge.lean:210,225; Conditions.lean:110.
INTENTIONAL: Recovery requires GST ≤ t_s - Δ, not merely GST ≤ v_s.
The actual HEAD tick supplies the horizon bound for Gen LabelSync. -/
theorem fgsa_score_eq_on_recovery
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G)
    (s : Slot) (hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal b raw sup rows⟩ : Obj p) ∈
      V2.Run.emitsAt E rho ip)
    (hadm : b ∈ (V2.Run.stateBefore E rho ih y).st.base.blocks)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D) :
    let src := clock p (V2.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
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
  have hsync := Gen.V2.LabelSync.of_recovery E rho _ _ h.sync hGST hvd hhorizon
  exact fgsa_score_eq_on_run E rho h.base.valid h.base.noRestart h.base.delta s hsync
    hx hy hip hih hseat b raw sup rows hem hadm D hgeom

end AvailableChain.FGSA.Run
end
