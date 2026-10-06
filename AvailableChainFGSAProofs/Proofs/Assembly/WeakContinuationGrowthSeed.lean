module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep (retained seed interface)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (source discipline producers)

public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (H-time source interface)

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


/-- All finite seed fields come from continuation producers at its own index. -/
theorem wcg_finiteSeed (hb : Base₂ p c E rho)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) (i : Nat) :
    WCFiniteFacts p c E rho i := by
  have hsch := hb.valid.toScheduleWellFormed
  exact wcg_finiteFacts hb.valid hb.idealization
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ (fgsa_rStore p c E rho))
    (fun x hx => fgsa_clientSafeAll p c E rho hb.linked x hx)
    (fun _ _ _ _ _ ha he => sourceDiscipline_emittedName p c E rho hsch ha he)
    (fgsa_leaseOrigins_lastWrite p c E rho hsch)
    (fgsa_leaseOrigins_fastWrites p c E rho hsch)
    (fgsa_leaseOrigins_ancestorDeadlines p c E rho) i

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_cut_downward (t : Time) :
    ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key →
      cutPred t f = true → cutPred t e = true := by
  intro e f hef hf
  exact decide_eq_true (hef.trans (of_decide_eq_true hf))

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_tick_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t d : Time} (he : rho.events[i]? = some (.tick x t))
    (ht : t ≤ d) : i < afterTicksIdx rho d := by
  by_contra h
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred d)
    (wcg_cut_downward d) (Nat.le_of_not_gt h) he
  have hc : cutPred d (.tick x t : V2.Event V (fgsa p c).Object) = true := by
    apply decide_eq_true
    exact Prod.Lex.toLex_le_toLex.mpr (ht.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  rw [hc] at hf
  cases hf

omit [DecidableEq V] [Fintype V] in
/-- WC J1; DC finite event provenance: private replay or source-construction helper. -/
private theorem wcg_time_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {d : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho d) : e.time ≤ d := by
  have hm : e ∈ rho.events.filter (cutPred d) := by
    rw [V2.D.Engine.filter_eq_take hs (cutPred d) (wcg_cut_downward d)]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho d))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

private def seed_headAtIdx (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) =>
      headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis
private theorem seed_headAtIdx_eq : @headAtIdx = @seed_headAtIdx := rfl

/-- WC J1; DC height seed: construct HS from the selected HealingInput and source regime.
The output cut alone is not used as a replacement for the source witness. -/
theorem wcg_heightSeed {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i := by
  let i := afterTicksIdx rho (tstar p w)
  have hs := hS.base.valid.toScheduleWellFormed
  have hservice := hinput.ac.h3 w.u w.QStar hinput.wit.proposal hinput.wit.proposal_lower
  have hgate : SA.gateTime p.toParams w.u ≤ rho.horizon := le_of_lt hend
  have href : ∀ x ∈ rho.honest, S_at p c E rho i x = w.QStar := by
    intro x hx
    have h := hinput.ac.h4.1 x hx
    rw [afterTicks_eq_stateBefore E rho hs] at h
    exact h
  have hnext : SA.voteTime p.toParams (w.u + 1) ≤ SA.gateTime p.toParams w.u := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  have hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1) := by
    have hstart := hinput.wit.synchronous
    have hslot : w.sStar + 2 ≤ w.u := hinput.wit.proposal_lower
    have hslot' : (w.sStar : Int) ≤ (w.u : Int) + 1 := by
      exact_mod_cast (Nat.le_trans (Nat.le_add_right w.sStar 2)
        (hslot.trans (Nat.le_succ w.u)))
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hstart
    change E.t_GST ≤ 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  obtain ⟨j₀, y₀, a₀, WStar, hrow₀, _, hsrc₀, herase, hheight⟩ := hinput.wit.fresh
  have hstored : ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    have hc := cstoreInv_stateBefore E rho i x
    have hQ : w.QStar ∈ (storeAt p c E rho i x).base.blocks := by
      rw [← href x hx]
      exact hc.Smem
    obtain ⟨Qfg, hQfg, heQ⟩ := hc.baseTree w.QStar |>.mp hQ
    apply KitFG.ancestor_closed_of_parent_closed _ hc.fg.closed Qfg hQfg
    apply eraseFG_preceq_iff.mp
    rw [herase, heQ]
    exact hinput.wit.source_prefix
  have hscope := rootScope_source hrow₀.1 hsrc₀
  refine ⟨⟨hinput.wit.after_gst, hend, rfl, hinput.wit.proposal, href⟩,
    ⟨rfl, List.length_filter_le _ _, hinput.wit.after_gst, hfirst,
      ⟨WStar, herase, hheight, hscope, hstored⟩, hinput.wit.source_prefix,
      ?_, href, ?_, ?_, ?_, ?_, ?_, wcg_finiteSeed hS.base (fgsa_faultQ_of_count p hS.fault) i⟩⟩
  · intro x hx
    obtain ⟨hraw, ⟨j, hj, hpass⟩, _⟩ := hservice.2 hgate x hx
    refine ⟨j, wcg_tick_before_cut hs hj le_rfl, hj, ?_, hpass⟩
    rw [gateResultAt_eq_gateResult p c E rho hs hj]
    exact hraw
  · intro x hx
    have heq : ((4 * (w.u + 1) + 1 : Nat) : Time) * p.Δ =
        SA.voteTime p.toParams (w.u + 1) := by
      change _ = 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hS.base.delta x hx
      (4 * (w.u + 1) + 1) (heq ▸ hnext.trans hgate)
    rw [heq] at hk
    let st := FGSA.clock p (storeAt p c E rho k x) (SA.voteTime p.toParams (w.u + 1))
    have hread : headAtLabel p c E rho x (w.u + 1) = some (headVote p st (w.u + 1)) := by
      change (postClock E rho x (SA.voteTime p.toParams (w.u + 1))).map
        (fun nd => headVote p nd.st (w.u + 1)) = _
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
      rfl
    have hraw := (hservice.2 hgate x hx).1
    have hsu : w.sStar ≤ w.u := le_trans (Nat.le_add_right _ _) hinput.wit.proposal_lower
    have hle := (hinput.ac.h5 x w.u w.QStar hx hsu hraw).2.1
      x (w.u + 1) (headVote p st (w.u + 1)) hx le_rfl hread
    have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x)
      (SA.voteTime p.toParams (w.u + 1))
    refine ⟨k, wcg_tick_before_cut hs hk hnext, ⟨hk, ?_, ?_, ?_⟩⟩
    · rw [seed_headAtIdx_eq]
      unfold seed_headAtIdx
      rw [hk]
      exact hle
    · intro A hA
      obtain ⟨H, hH, hHread⟩ := hinv.baseTree _ |>.mp (headVote_stored p st hinv (w.u + 1))
      obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hH
        (hHread ▸ Gen.Pure.block_preceq_trans hA hle)
      exact hinv.baseTree A |>.mpr ⟨Afg, hAfg, heA⟩
    · have hr := (wcg_finiteSeed hS.base (fgsa_faultQ_of_count p hS.fault) k).receipts x hx
      constructor
      · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
      · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes
  · intro j x r a e hj ha he hhigh
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
      sourceDiscipline_emittedName p c E rho hs ha he
    refine ⟨K, B, hK, hpair, hentry, hB, hKB, ?_⟩
    have ht := wcg_time_before_cut hs ha.2.1 hj
    have hlabel : r * p.R ≤ w.u := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
      have hd := p.deltaPos
      have hcast : ((r * p.R : Nat) : Int) ≤ (w.u : Int) := by nlinarith
      exact_mod_cast hcast
    rcases hlabel.lt_or_eq with hlt | heq
    · have hh : high p w K := by
        rw [high_def, heightView_eq_simplex]
        change w.M + 1 ≤ hOf p.E p.cfg K
        simpa only [hpair] using hhigh
      have hhead := hservice.1 (by
        change 4 * p.Δ * (w.u : Int) + p.Δ ≤ rho.horizon
        change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ rho.horizon at hgate
        have hd := p.deltaPos
        nlinarith) x ha.1
      exact (hinput.ac.h2A x r K ha.1 hK hh).1 x w.u w.QStar ha.1
        (Nat.succ_le_of_lt hlt) hhead
    · rw [heq] at hB
      have heB := Option.some.inj (Option.some.inj (hB.symm.trans (hservice.2 hgate x ha.1).1))
      exact heB ▸ hKB
  · intro x hx
    have hc := (cstoreInv_stateBefore E rho i x).fg
    change w.M + 1 ≤ (rho.stateBefore E i x).st.fg.h_max
    rw [hc.hmax]
    rw [← hheight]
    have hw : WStar ∈ (rho.stateBefore E i x).st.fg.TF := hstored x hx
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hw)
  · intro x hx
    have hn := nestOK_stateBefore E rho i x
    change Block.Preceq (F_at p c E rho i x) (S_at p c E rho i x) at hn
    rwa [href x hx] at hn
  · intro x hx row hr _
    have ht := storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
    change Block.Preceq row.1 (S_at p c E rho i x) at ht
    rwa [href x hx] at ht

/-- Choose the bounded source seed before any continuation is considered. -/
theorem wcg_sourceWitness (hH : HTimeClaim p) {G ΔF : Time}
    (hδ : p.δt = 2 * p.R)
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF) :
    ∃ w : HealingWitness,
      BoundedHealingCut₂ p c E rho w.u w.QStar
        (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF ∧
      WCSeed p c E rho w (afterTicksIdx rho (SA.gateTime p.toParams w.u)) := by
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨hS.toRecovery₂, hS.liveness⟩, hS.endpoint.ge⟩
  have hend : tstar p w < rho.horizon := by
    rw [hS.endpoint]
    exact start.trans_lt bound
  exact ⟨w, wcg_heightSeed hS input hend⟩

end AvailableChain.FGSA.Run
end
