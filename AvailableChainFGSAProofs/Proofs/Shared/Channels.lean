module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSARun.Proofs.EmissionWellFormed
public import AvailableChainFGSARun.Proofs.Hooks

public section

/-! Channel equations for P3 F0.8a. Gen.V2.Duty.linked_holder_eq and
Gen.V2.Duty.linked_card_le_of_holders supply identity transport (Q5, S4b-14).
T7 provides `processed_stable`, `fgsa_proposal_receipt`, `fgsa_head_receipt`,
`EmitsRow`, `EmittedRowsNoSlash`, `decodeRowObject`, `honest_emit_wellFormed`,
`contentAgree_run`, and `fgsa_receiptCoverage`; this file does not restate them. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

theorem ancestorClosed_preceq (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B) := by
  constructor
  intro X Y hXY hYB
  exact KitFG.preceq_trans hXY hYB

theorem ancestorClosed_compatible (B : FGBlock (Fin p.n)) :
    AncestorClosed p (fun e => FGBlock.Preceq e B ∨ FGBlock.Preceq B e) := by
  constructor
  intro X Y hXY hY
  rcases hY with hYB | hBY
  · exact Or.inl (KitFG.preceq_trans hXY hYB)
  · exact KitFG.preceq_total_of_common hXY hBY

theorem srcFrame_genesis_preceq (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) → FGBlock.Preceq .genesis B :=
  fun _ => KitFG.genesis_preceq B

theorem srcFrame_genesis_compatible (B : FGBlock (Fin p.n)) (c₀ : Nat) :
    c₀ ≤ hOf p.E p.cfg (.genesis : FGBlock (Fin p.n)) →
      FGBlock.Preceq .genesis B ∨ FGBlock.Preceq B .genesis :=
  fun _ => Or.inl (KitFG.genesis_preceq B)

/-- The store selector is the channel's deepest member of X_r ∩ D(Σ.T). -/
theorem fgSource_eq_jointSource (st : State p.n) :
    FGSA.fgSource p st = jointSource p st := by
  rw [jointSource_def, domainR_def, frameR_def, treeT_def]
  change FGSA.deepest ((FGSA.fullTree p st).filter _) =
    FGSA.deepest ((FGSA.fullTree p st).filter _)
  apply congrArg (FGSA.deepest (n := p.n))
  apply Finset.filter_congr
  intro B _
  rw [sourceCandidates_def, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
    Finset.mem_filter, List.mem_toFinset]
  cases leaseOf st (eraseFG B) <;> rfl

/-- For a positive slot, propose uses the joint proposer head as parent. -/
theorem propose_head (st : State p.n) (s : Slot) (hs : s ≠ 0) :
    FGSA.propose p st s = some (.proposal
      (.node (proposerHead p st s) s (packBody 0 (proposalRows p st (proposerHead p st s))))
      ((proposerVotes st s).filterMap liftHead?) ((proposerSupport st s).filterMap liftHead?)
      (proposalRows p st (proposerHead p st s))) := by
  rw [proposerHead_def]
  change (if s = 0 then none else _) = _
  exact ite_eq_right hs

/-- The frame reads only the FG store. -/
theorem frameR_congr_fg (st st' : State p.n) (h : st.fg = st'.fg) :
    frameR p st = frameR p st' := by
  rw [frameR_def, frameR_def]
  exact congrArg (KitFG.storeControlsView (heightView p)) h

/-- D(X) reads the FG store and X, with no vote-pool input. -/
theorem domainR_congr_fg (st st' : State p.n) (X : Finset (FGBlock (Fin p.n)))
    (h : st.fg = st'.fg) : domainR p st X = domainR p st' X := by
  rw [domainR_def, domainR_def, frameR_congr_fg p st st' h]

/-- The channel domain equals the fixed-store frame through the height bridge. -/
theorem domainR_eq_storeFrame (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainR p st X = storeFrame p.E p.cfg st.fg X := by
  rw [domainR_def, frameR_def, controls_eq,
    ← KitFG.filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  rfl

/-- HEAD eligibility uses the live lo relaxation, then score and current slot. -/
theorem eligible_lo_live (st : State p.n) (raw sup : List (GridCO.Wire p.n)) (B : Block) :
    FGSA.eligible p st raw sup B =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = B.parent ∧ hOf p.E p.cfg P < (frameR p st).lo) ||
       decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw sup B) ||
       B.slot == st.slot p) := fgsa_eligible_eq p st raw sup B

/-- All five joint selections and the finality triple ignore the own record Λ. -/
theorem jointSelections_record_irrel (st : State p.n) (Λ Λ' : RecordOnce)
    (s : Slot) (raw sup : List (GridCO.Wire p.n)) (B : Block) :
    let nd : Node p := ⟨st, Λ⟩
    let nd' : Node p := ⟨st, Λ'⟩
    (FGSA.liveRoot p nd.st, FGSA.eligible p nd.st raw sup B, jointSource p nd.st,
      proposerHead p nd.st s, FGSA.fgHead p nd.st, (FGSA.fgInputs p nd.st).2) =
    (FGSA.liveRoot p nd'.st, FGSA.eligible p nd'.st raw sup B, jointSource p nd'.st,
      proposerHead p nd'.st s, FGSA.fgHead p nd'.st, (FGSA.fgInputs p nd'.st).2) := rfl

variable {In V : Type} (c : AppCodec In) [DecidableEq V]
    (rho : V2.D.Run V (fgsa p c))

/-- The pre-tick and post-clock reads have the same FG frame.
The gate can still change the AC candidates. -/
theorem frame_postClock (E : Generic.Env V) (x : V) (t : Time) (nd nd' : Node p)
    (hpre : preTick E rho x t = some nd) (hpost : postClock E rho x t = some nd') :
    frameR p nd'.st = frameR p nd.st := by
  rw [postClock_def, hpre] at hpost
  have he : (fgsa p c).clock nd t = nd' := Option.some.inj hpost
  rw [← he]
  exact frameR_congr_fg p _ _ (FGSA.clock_fg p nd.st t)

omit [DecidableEq V] in
/-- A holder alone is insufficient: the authentication must be an FG seat. -/
theorem rowSigner_iff_holder (a : RowWire p.n) (x : V) : RowSigner p c rho a x ↔
    (∃ i, a.auth = .seat .fg i) ∧ V2.D.Run.holder rho (ofRow p a).auth = some x := by
  rw [RowSigner_def]
  constructor
  · rintro ⟨i, ha, hx⟩
    refine ⟨⟨i, ha⟩, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a.auth) = some x
    rw [ha]
    exact congrArg some hx
  · rintro ⟨⟨i, ha⟩, hx⟩
    refine ⟨i, ha, ?_⟩
    change V2.D.Run.holder rho (ofAuth p a.auth) = some x at hx
    rw [ha] at hx
    exact Option.some.inj hx

/-- Every honest row has fixed FG authentication. -/
theorem honestRow_auth (E : Generic.Env V) (h : V2.D.ExecutionValid E rho)
    {j : Nat} {y : V} {r : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) : ∃ i, a.auth = .seat .fg i := by
  obtain ⟨hy, hj, hem⟩ := he
  have hawake : E.awake y (p.actionTime r) = true := by
    by_contra hn
    have hf : E.awake y (p.actionTime r) = false := Bool.eq_false_iff.mpr hn
    rw [(V2.D.Run.step_tick_eq E rho hj).2,
      (fgsa_tick_asleep (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho j y) y _ hf).1] at hem
    exact List.not_mem_nil hem
  have hv := honest_emit_wellFormed E rho h.toDeliveryWellFormed
    h.toScheduleWellFormed j y _ hj hy hawake (ofRow p a) hem
  change FGSA.wellFormed p (toWire p (ofRow p a)) = true at hv
  rw [toWire_ofRow] at hv
  rcases a with ⟨auth, body⟩
  cases auth with
  | none => cases hv
  | proposer s => cases hv
  | seat l i => cases l with
    | head s => cases hv
    | fg => exact ⟨i, rfl⟩

/-- An honest signed row is released before its direct or carried handler call.
The time inequality can be non-strict; tick-before-delivery makes the index strict. -/
theorem emit_lt_handles (E : Generic.Env V) (h : V2.D.ExecutionValid E rho)
    {j k : Nat} {y x : V} {r : Nat} {a : RowWire p.n}
    (he : HonestRowAt p c E rho j y r a) (hh : HandlesRowAt p c E rho k x a) : j < k := by
  obtain ⟨seat, ha⟩ := honestRow_auth p c rho E h he
  obtain ⟨hy, hj, hem⟩ := he
  obtain ⟨u, envelope, hk, hhandle⟩ := hh
  rcases a with ⟨auth, body⟩
  dsimp only at ha
  subst auth
  have hrow := (fgsa_emitsAt_row E rho j y _ hj seat body).mp hem
  have hholder : V2.D.Run.holder rho (ofRow p ⟨.seat .fg seat, body⟩).auth = some y :=
    congrArg some hrow.2.1
  have horigin : ∃ u', u' ≤ u ∧
      V2.D.Run.emits E rho y (ofRow p ⟨.seat .fg seat, body⟩) u' := by
    rcases (fgsaHooks p c).handles_carries _ envelope _ hhandle with heq | hc
    · subst envelope
      exact h.unforgeable x _ u ⟨k, hk⟩ y hy hholder
    · exact h.carried x envelope u ⟨k, hk⟩ _ hc y hy hholder
  obtain ⟨u', hle, j', hj', hem'⟩ := horigin
  have hjj' := fgsa_emitOnceUnder E rho h seat (hrow.2.1.symm ▸ hy)
    (.row body) j j' (p.actionTime r) u'
    (hrow.2.1.symm ▸ hj) (hrow.2.1.symm ▸ hj') hem hem'
  subst j'
  have htime := (V2.Event.tick.inj (Option.some.inj (hj.symm.trans hj'))).2
  exact V2.D.Engine.tick_index_lt_delivery E rho h.toScheduleWellFormed hj hk (htime ▸ hle)

/-- P3 §8.7 F2.2; bp02 §§3.1–3.5. Class B channel assembly.
DC counterparts: ChainState/FGRootWitness.lean:327,493 and
Execution/WeakGenesisGSTZeroActionSources.lean:106. The all-entry FJ bundle
and G1 differ intentionally (TS/spec/fgsa-protocol.tex:2557–2571;
TS/log.md:1475). No source existence or Clean premise is used. -/
theorem cpPrefix_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) : CPPrefix p c E rho := by
  simp only [CPPrefix_def, heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x B hx hrows
  have hs := hsrc (fun e => FGBlock.Preceq e B) 0 (ancestorClosed_preceq p B)
    (by simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
      using srcFrame_genesis_preceq p B 0) i x hx (by
      intro y r a e ha hn _
      obtain ⟨X, hXB, he⟩ := hrows y r a _ ha hn
      have heX : X = e := FGBlock.root_injective (congrArg Prod.snd he)
      exact heX ▸ hXB)
  have hc : ∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      FGBlock.Preceq e B := fun W hW e he => hs.1 W hW e he (Nat.zero_le _)
  have hF := hs.2.1 (Nat.zero_le _)
  have hJ := hs.2.2.1 (Nat.zero_le _)
  have hZ := hs.2.2.2 (Nat.zero_le _)
  let st := storeAt p c E rho i x
  have hinv := (hstore i x hx).1.fg
  have hcert := (fgCertificateLaws p).height
  have hjust := fgJustificationLaws p
  rw [heightView_eq_simplex p] at hinv hcert hjust
  have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      hOf p.E p.cfg U < hOf p.E p.cfg W → FGBlock.Preceq (derive p.E p.cfg U).T_h B := by
    intro W hW U hU hlt
    apply hc W hW
    simp only [certified_def, heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def]
    exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
  have hn := KitFG.storeFrameView_noContest_of_crossed_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust (by
    intro W hW U hU hlt
    exact KitFG.preceq_total_of_common hJ (hcross W hW U hU hlt))
  have hlo := KitFG.storeFrameView_height_of_crossed_prefix_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv B hn hcross
  have hcontrols : R_at p c E rho i x = storeControls p.E p.cfg st.fg :=
    (hframe i x hx).1.trans (by
      simpa only [KitFG.fjControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using (storeControls_eq p st (hstore i x hx).1).symm.trans (controls_eq p st))
  refine ⟨hc, hF, hJ, hZ, ?_, ?_⟩
  · rw [hcontrols]; exact hn
  · rw [hcontrols]; exact hlo

/-- P3 §8.7 F2.2; bp02 §3.4 and P3 App. A.3 CPCompat. Class B.
DC counterpart: ChainState/FGRootWitness.lean:548 concludes root
compatibility only. Retention and EVERY contest witness are intentional FJ
extensions (TS/spec/fgsa-protocol.tex:2557–2571; TS/log.md:1475). G1 is explicit. -/
theorem cpCompat_of_srcFrame (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) : CPCompat p c E rho := by
  simp only [CPCompat_def, heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
  intro i x B hx hrows
  have hs := hsrc (fun e => FGBlock.Preceq e B ∨ FGBlock.Preceq B e) 0
    (ancestorClosed_compatible p B) (by
      simpa only [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using srcFrame_genesis_compatible p B 0) i x hx
    (fun y r a e ha hn _ => hrows y r a e ha (by
      simpa only [heightView_eq_simplex p, KitFG.simplexHeightView_def, KitFG.heightOf_def]
        using hn))
  have hc : ∀ W ∈ (storeAt p c E rho i x).fg.TF, ∀ e ∈ certified p W,
      FGBlock.Preceq e B ∨ FGBlock.Preceq B e :=
    fun W hW e he => hs.1 W hW e he (Nat.zero_le _)
  have hF := hs.2.1 (Nat.zero_le _)
  have hJ := hs.2.2.1 (Nat.zero_le _)
  let st := storeAt p c E rho i x
  have hinv := (hstore i x hx).1.fg
  have hcert := (fgCertificateLaws p).height
  have hjust := fgJustificationLaws p
  rw [heightView_eq_simplex p] at hinv hcert hjust
  have hcross : ∀ W ∈ st.fg.TF, ∀ U, FGBlock.Preceq U W →
      hOf p.E p.cfg U < hOf p.E p.cfg W →
      FGBlock.Preceq (derive p.E p.cfg U).T_h B ∨ FGBlock.Preceq B (derive p.E p.cfg U).T_h := by
    intro W hW U hU hlt
    apply hc W hW
    simp only [certified_def, heightView_eq_simplex p,
      KitFG.simplexHeightView_def, KitFG.heightOf_def]
    exact ⟨U, hU, Or.inr (Or.inr ⟨rfl, hlt⟩)⟩
  have hcontrols : R_at p c E rho i x = storeControls p.E p.cfg st.fg :=
    (hframe i x hx).1.trans (by
      simpa only [KitFG.fjControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
        using (storeControls_eq p st (hstore i x hx).1).symm.trans (controls_eq p st))
  refine ⟨hc, hF, hJ, ?_, ?_⟩
  · intro hB hFB
    have hr := KitFG.storeFrameView_retention_of_compatible_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust B hB hFB hJ hcross
    rcases hr with hr | hr
    · left
      rw [hcontrols]
      exact hr
    · right
      rw [← (hframe i x hx).2, fullTree_eq]
      exact hr
  · rw [hcontrols]
    exact KitFG.storeFrameView_contest_of_compatible_of_inv
      p.E (KitFG.simplexHeightView p.E p.cfg) hcert (finalityView p) st.fg hinv
        hjust B hJ hcross

end AvailableChain.FGSA.Run
end
