module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep (retained seed interface)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (source discipline producers)

public section

namespace AvailableChain.FGSA.Run

open SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Rebuild the finite seed's certificate origins in the continuation.
The selected signer is honest in rho. No source signer is transferred. -/
theorem wcg_certifiedOrigin (hb : Base₂ p c E rho)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (X : FGBlock (Fin p.n)) (hX : X ∈ certified p W) (hne : X ≠ .genesis) :
    WCTargetOrigin p c E rho i X (heightView p X).h := by
  have strat := sourceDiscipline_strat p c E rho
    (pt := ()) ⟨hb, hq⟩ (fgsa_rStore p c E rho)
  obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := strat i x W hx hW X hX hne
  obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
    sourceDiscipline_emittedName p c E rho hb.valid.toScheduleWellFormed hrow hname
  have hXK : X = (derive p.E p.cfg K).T_h :=
    rootScope_eq hb.idealization
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry)
      (congrArg Prod.snd hpair)
  exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩

/-- A nonempty growth suffix supplies the one-quorum cap needed to rebuild
certificate origins at its own cut, including certificates from the prefix. -/
theorem wcg_seedCertified {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (h : CleanGrowthContinuation₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) (u : Slot)
    (x : V) (hx : x ∈ rho.honest)
    (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams u)) x).fg.TF)
    (X : FGBlock (Fin p.n)) (hX : X ∈ certified p W) (hXne : X ≠ .genesis) :
    WCTargetOrigin p c E rho (afterTicksIdx rho (SA.gateTime p.toParams u))
      X (heightView p X).h :=
  wcg_certifiedOrigin h.base (wcg_suffix_faultQ h hne) _ x hx W hW X hX hXne

/-- A covered strict suffix forces a nonempty retained honest set. -/
theorem wcg_retained_nonempty {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (h : CleanGrowthContinuation₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) : rho.honest.Nonempty := by
  have hp := h.participation rho.horizon hne le_rfl
  have hcard : (Gen.V2.Duty.awakeHonest E rho rho.horizon).card ≤ rho.honest.card := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.card_filter_le _ _
  exact Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hp.trans_le hcard))

omit [Fintype V] in
/-- The healing carrier enters continuation scope through a retained store.
Its original source signer need not remain honest. -/
theorem wcg_seedCarrier {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {w : HealingWitness} {iSource : Nat}
    (ha : RetainedAgreesThrough₂ p c E₀ source E rho)
    (hsource : V2.D.ScheduleWellFormed E₀ source)
    (hrho : V2.D.ScheduleWellFormed E rho)
    (hs : WCSeed p c E₀ source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hne : rho.honest.Nonempty) :
    let i := afterTicksIdx rho (SA.gateTime p.toParams w.u)
    ∃ WStar : FGBlock (Fin p.n), eraseFG WStar = w.CStar ∧
      (heightView p WStar).h = w.M + 1 ∧
      RootBlockInRun p c E rho (eraseFG WStar) ∧
      ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
  intro i
  obtain ⟨W, hW, hh, _, hstored⟩ := hs.carrier
  have hretained : ∀ x ∈ rho.honest, W ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    rw [wcg_cut_storeReplay ha hsource hrho x hx hend, ← hs.cut]
    exact hstored x (ha.honest hx)
  obtain ⟨x, hx⟩ := hne
  exact ⟨W, hW, hh, rootScope_store hx (hretained x hx), hretained⟩

/-- Before the endpoint, all retained validators are awake. A nonempty
strict suffix supplies the global majority needed for these earlier votes. -/
theorem wcg_participation {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {G ΔF : Time}
    (hsource : StrongRecoverySearchPrefix₂ p c E₀ source G ΔF)
    (h : CleanGrowthContinuation₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon)
    (t : Time) (hgst : E.t_GST ≤ t) (ht : t ≤ rho.horizon) :
    (Gen.V2.Duty.faulty rho).card < (Gen.V2.Duty.awakeHonest E rho t).card := by
  by_cases hp : source.horizon < t
  · exact h.participation t hp ht
  have hprefix : t ≤ source.horizon := le_of_not_gt hp
  have hall : Gen.V2.Duty.awakeHonest E rho t = rho.honest := by
    rw [Gen.V2.Duty.awakeHonest_def]
    apply Finset.filter_eq_self.mpr
    intro x hx
    rw [h.agrees.awake x hx t hprefix]
    exact hsource.awake x (h.agrees.honest hx) t
      (h.agrees.gst ▸ hgst) hprefix
  rw [hall]
  have hsuffix := h.participation rho.horizon hne le_rfl
  have hcard : (Gen.V2.Duty.awakeHonest E rho rho.horizon).card ≤ rho.honest.card := by
    rw [Gen.V2.Duty.awakeHonest_def]
    exact Finset.card_filter_le _ _
  exact hsuffix.trans_le hcard

end AvailableChain.FGSA.Run
end
