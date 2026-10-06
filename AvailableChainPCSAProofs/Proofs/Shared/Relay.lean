module
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy

public section

/-! Strict object receipt for PC-SA (pcsa34-r4.3 §5.2.3).
FG-SA Shared/Relay and HeldReceipt supply the proof pattern. Their run
types are FG-SA, so PC-SA uses the Generic delivery contract directly. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {m : FGMode}

/-- HEADs, proposals, acks, and PCs use the base delay. -/
theorem pcsa_nonrow_delay (o : Obj p) (Δ ΔF : Time)
    (h : ∀ body, o.payload ≠ .row body) : pcsaDelay p Δ ΔF o = Δ := by
  rw [pcsaDelay_def]
  cases he : o.payload <;> try rfl
  exact (h _ he).elim

/-- An ack object cannot be excluded by any store. -/
theorem pcsa_ack_not_excluded (nd : Node p) (s : Slot) (i : Fin p.n) (r : BlockId) :
    (pcsaWith m p c).excludes nd (ackObj p s i r) = false := rfl

/-- An unsigned PC object cannot be excluded by any store. -/
theorem pcsa_pc_not_excluded (nd : Node p) (C : PC p.n) :
    (pcsaWith m p c).excludes nd (⟨.none, .pc C⟩ : Obj p) = false := rfl

/-- A handled ack is processed exactly when its signed ack is in the pool. -/
theorem pcsa_ack_processed_iff (nd : Node p) (s : Slot) (i : Fin p.n) (r : BlockId) :
    (pcsaWith m p c).processed nd (ackObj p s i r) = true ↔
      (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ nd.st.ackPool := by
  change decide ((⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ nd.st.ackPool) = true ↔
    (⟨.seat (.ack s) i, r⟩ : AckWire p.n) ∈ nd.st.ackPool
  constructor
  · intro h
    exact of_decide_eq_true h
  · intro h
    exact decide_eq_true h

/-- Every ack carried by a received PC has a handler call. -/
theorem pcsa_pc_handles_ack (nd : Node p) (C : PC p.n) (a : AckWire p.n)
    (ha : a ∈ C.acks) :
    (pcsaWith m p c).handles nd (⟨.none, .pc C⟩ : Obj p) (ofAck p a) := by
  change handlesS p nd.st _ _
  right
  left
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- A proposal carries the acks of its carried PC, with their signatures. -/
theorem pcsa_proposal_carries_ack (N : NamedProposal p.n) (auth :
    V2.Auth RunLabel (RunLabel.seats p)) (a : AckWire p.n) (ha : a ∈ N.pcAcks) :
    (pcsaWith m p c).carries (⟨auth, .proposal N⟩ : Obj p) (ofAck p a) := by
  change (ofAck p a ∈ N.raw.map (ofHead p) ∨ ofAck p a ∈ N.support.map (ofHead p) ∨
    ofAck p a ∈ N.rows.map (ofRow p) ∨ ofAck p a ∈ N.pcAcks.map (ofAck p)) ∨ _
  exact Or.inl (Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))))

/-- An accepted proposal calls the handlers of the acks of its carried PC. -/
theorem pcsa_proposal_handles_ack (nd : Node p) (s : Slot) (N : NamedProposal p.n)
    (hn : namedParentHeld nd.st N = true)
    (hp : ∃ P, parentFG nd.st N.erase = some P ∧ blockAccepted p nd.st s N P = true)
    (a : AckWire p.n) (ha : a ∈ N.pcAcks) :
    (pcsaWith m p c).handles nd (ofWire p ⟨.proposer s, .proposal N⟩) (ofAck p a) := by
  change handlesS p nd.st _ _
  right
  left
  exact ⟨⟨hn, hp⟩, Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))⟩

/-- Broadcast receipt has a strict deadline, also at an asleep receiver. -/
theorem pcsa_strict_broadcast (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) (x y : V) (t : Time)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) (he : V2.D.Run.emits E rho x o t)
    (hc : t + E.Δ ≤ cut)
    (hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧ ∃ j, V2.D.Run.handlesAt E rho j y o t' := by
  have hd := pcsa_nonrow_delay o E.Δ ΔF hn
  simpa only [hd] using hD.broadcast_emitted x hx o t he y hy (by simpa [hd] using hc)
    (by simpa [hd] using hNX)

/-- Accepted objects relay with a strict deadline if the receiver still needs them. -/
theorem pcsa_strict_relay (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (o : Obj p) (hn : ∀ body, o.payload ≠ .row body) (x y : V) (i : Nat) (t : Time)
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (ha : V2.D.Run.acceptsAt E rho i x o t)
    (hneed : (pcsaWith m p c).processed (V2.D.Run.stateBefore E rho (i + 1) y) o = false)
    (hc : t + E.Δ ≤ cut)
    (hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (t + E.Δ) y) o = false) :
    ∃ t', t ≤ t' ∧ t' < t + E.Δ ∧ ∃ j, V2.D.Run.handlesAt E rho j y o t' := by
  have hd := pcsa_nonrow_delay o E.Δ ΔF hn
  simpa only [hd] using hD.relay_accepted x hx i o t ha y hy hneed
    (by simpa [hd] using hc) (by simpa [hd] using hNX)

/-- Honest acks emitted at the early duty are handled strictly before the freeze. -/
theorem pcsa_ack_handled_before_freeze (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (hdelta : E.Δ = p.Δ) (s : Slot) (i : Fin p.n) (r : BlockId) (y : V)
    (hi : rho.seatOf (.base (.ack s)) i ∈ rho.honest) (hy : y ∈ rho.honest)
    (he : V2.D.Run.emits E rho (rho.seatOf (.base (.ack s)) i) (ackObj p s i r)
      (SA.earlyTime p.toParams s)) (hc : SA.freezeTime p.toParams s ≤ cut) :
    ∃ t', SA.earlyTime p.toParams s ≤ t' ∧ t' < SA.freezeTime p.toParams s ∧
      ∃ j, V2.D.Run.handlesAt E rho j y (ackObj p s i r) t' := by
  have ht : SA.earlyTime p.toParams s + E.Δ = SA.freezeTime p.toParams s := by
    rw [hdelta]
    change (4 * p.Δ * (s : Int) + 2 * p.Δ) + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hh := pcsa_strict_broadcast E rho hD (ackObj p s i r)
    (fun _ => by intro h; cases h) _ y _ hi hy he (by simpa only [ht] using hc)
    (pcsa_ack_not_excluded _ s i r)
  simpa only [ht] using hh

end AvailableChain.PCSA.Run
end
