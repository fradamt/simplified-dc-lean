module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSA.Statements.Invariants
import AvailableChainFGSARun.Proofs.Receipts

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

end AvailableChain.FGSA.Run
end
