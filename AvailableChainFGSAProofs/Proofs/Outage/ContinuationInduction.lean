module
public import AvailableChainFGSAProofs.Proofs.Outage.Induction

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

section Prefix

variable [Fintype V]
variable (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hfault : (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))

set_option maxHeartbeats 1600000 in
-- The joint event proof has several model-state reductions.
include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamed in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §8.2–3; O-INDUCT plan §5. Class (iii).
DC: INTENTIONAL; one joint induction on tick and delivery prefixes.
The seeds have producers outage_arming_sources, outage_arming_duties,
and pending_gate_lease_or_F. INLINE channels: Foundations active/frame,
SrcFrameAbove, sourceDiscipline_tSrc, and sourceDiscipline_emittedName.
OUTPUT-DIRECT §1: the endpoint may equal expiry. Events at b₁ are excluded.
The original strict-endpoint theorem stays unchanged. -/
theorem outage_event_induction_le_expiry {B : Block} {β : FGBlock (Fin p.n)} {j : Slot} {b₁ : Time}
    (hβ : eraseFG β = B) (hend : b₁ ≤ SA.gateTime p.toParams j + L p)
    (hseedSource : OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hseedDuty : OutageDutyHistory p c E rho B j (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hseedLocal : ∀ y ∈ rho.honest,
      OutageProtection p B j (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams j)) y))
    (hseedHeads : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q → HeadTargetAtEmission p c E rho y o t H →
          Block.Preceq B H)
    {i : Nat} (hI : afterTicksIdx rho (SA.gateTime p.toParams j) ≤ i)
    (hK : i ≤ V2.D.Run.idxBefore rho b₁)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    OutageSourceHistory p c E rho B i ∧ OutageDutyHistory p c E rho B j i ∧
      OutageNamedHistory p c E rho β i ∧
      ∀ y ∈ rho.honest, OutageProtection p B j (storeAt p c E rho i y) := by
  have hs := hvalid.toScheduleWellFormed
  induction i, hI using Nat.le_induction with
  | base =>
    exact ⟨hseedSource, hseedDuty,
      outage_named_of_source_history (hroots := hroots) hβ hseedSource hnamed, hseedLocal⟩
  | succ i hI ih =>
    have hiK : i < V2.D.Run.idxBefore rho b₁ := by omega
    obtain ⟨hsource, hduty, hnames, hlocal⟩ := ih hiK.le
    have hil : i < rho.events.length := hiK.trans_le (arming_idxBefore_le_length rho b₁)
    have he : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem hil
    have htend := (Gen.V2.Duty.index_lt_idxBefore_iff hs he b₁).mp hiK
    cases hevent : rho.events[i] with
    | restart x t =>
      rw [hevent] at he
      exact (hnr i x t he).elim
    | deliver x o t =>
      rw [hevent] at he
      have hsource' := outage_source_history_delivery he hsource
      have hduty' : OutageDutyHistory p c E rho B j (i + 1) := by
        constructor
        intro k y u a hk hy hdu htick ha
        have hne : k ≠ i := by
          rintro rfl
          rw [he] at htick
          cases htick
        exact hduty.history k y u a (by omega) hy hdu htick ha
      refine ⟨hsource', hduty', outage_named_of_source_history (hroots := hroots) hβ hsource'
        hnamed, ?_⟩
      intro y hy
      rcases arming_store_succ hnr he y with heq | ⟨u, hu, _⟩ | ⟨a, u, hu, _⟩
      · rw [heq]
        exact hlocal y hy
      · cases hu
      · have hxy := (V2.Event.deliver.inj hu).1
        have hyx : y = x := hxy.symm
        subst y
        have hc := (outage_delivery_frame (hroots := hroots) (hstrat := hstrat)
          hstore hframe hsrc
          hnamed he hy hβ hsource).2.1
        have hc' : Block.Compatible (F_at p c E rho (i + 1) x) B := by
          change Block.compatible (F_at p c E rho (i + 1) x) B = true
          rw [block_compatible_comm]
          exact hc
        exact outage_delivery_protection he (hlocal x hy) hc'
    | tick x t =>
      rw [hevent] at he
      have hdt := outage_tick_after_cut hs he hI
      have htb : t < b₁ := by
        rw [hevent] at htend
        exact htend
      have hx : x ∈ rho.honest := hs.honest_only _ (List.mem_of_getElem? he)
      let st := storeAt p c E rho i x
      let P := FGSA.clockPre p st t
      let Q := FGSA.clock p st t
      have hpost : storeAt p c E rho (i + 1) x = Q := by
        change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
        rw [(V2.D.Run.step_tick_eq E rho he).1]
        exact tick_st (c := c) E rho _ x t
      have hcounts : ∀ r, SA.releaseTime p.toParams r = t →
          GridCO.releaseCount p.toParams.engine (FGSA.actView P) r B <
            SA.releaseThreshold p.toParams := by
        intro r hr
        have htick : rho.events[i]? = some (.tick x (SA.releaseTime p.toParams r)) := hr ▸ he
        have hbound := outage_release_bound (hroots := hroots) hvalid hnr hcstar hdelta htick
            (hr ▸ hdt)
          hseedHeads (fun k y u a hk hy hdu htick ha =>
            (hduty.history k y u a hk hy hdu htick ha).1)
          (i + 1) x
        have hoff : ∀ s, SA.gateTime p.toParams s ≠ t := fun s => hr ▸ outage_gate_ne_release p s r
        rw [hpost] at hbound
        change GridCO.releaseCount p.toParams.engine (FGSA.actView (FGSA.clock p st t)) r B ≤
          (Gen.V2.Duty.faulty rho).card at hbound
        rw [inclusion_clock_offGate p st t hoff] at hbound
        exact hbound.trans_lt hfault
      have hpP : OutageProtection p B j P := by
        constructor
        · rw [clockPre_stable]
          exact (hlocal x hx).1
        · rw [clockPre_fg]
          rcases (hlocal x hx).2 with hF | ⟨dl, hm, hd⟩
          · exact Or.inl hF
          · exact Or.inr ⟨dl, outage_clockPre_row p st t hm
              (htb.trans_le (hend.trans hd)) hcounts, hd⟩
      have hfP : Block.Compatible (eraseFG P.fg.F) B := by
        rw [clockPre_fg]
        exact (outage_frame_retains (hstrat := hstrat) hstore hframe hsrc hx hβ hnames (hlocal x
          hx).1).1
      have hpQ : OutageProtection p B j Q := by
        change OutageProtection p B j (FGSA.clock p st t)
        by_cases hg : ∃ s, SA.gateTime p.toParams s = t
        · obtain ⟨s, hs⟩ := hg
          rw [← hs, arming_clock_gate]
          exact outage_gateStep_protection p _
            (cstoreInv_clockPre p st (cstoreInv_stateBefore E rho i x) _)
            (by rw [hs]; exact hpP) (by rw [hs]; exact hfP)
            ((arming_gate_le_iff p j s).mp (hdt.le.trans_eq hs.symm))
        · rw [inclusion_clock_offGate p st t (fun s h => hg ⟨s, h⟩)]
          exact hpP
      have hroot : Block.Preceq B (FGSA.liveRoot p Q) := by
        have hinv := cstoreInv_clock p st (cstoreInv_stateBefore E rho i x) t
        have hbelow : LeaseBelowOutputStore p Q := by
          rw [← hpost]
          exact leaseBelowOutput_stateBefore E rho (i + 1) x
        have hret := (outage_frame_retains (hstrat := hstrat) hstore hframe hsrc hx hβ hnames
          (hlocal x hx).1).2
        have hfg : Q.fg = st.fg := clock_fg p st t
        have hdom : FGSA.fullTree p Q = FGSA.fullTree p st := by
          change KitFG.treeStoreFrameView (heightView p) Q.fg Q.fg.TF =
            KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF
          rw [hfg]
        have hZ : FGSA.controls p Q = FGSA.controls p st := by
          change KitFG.treeStoreControlsView (heightView p) Q.fg =
            KitFG.treeStoreControlsView (heightView p) st.fg
          rw [hfg]
        apply outage_liveRoot_covers p Q hinv hpQ.1 hbelow
        rcases hret with hF | hret
        · left
          rw [hfg]
          exact hF
        · rcases hpQ.2 with hF | ⟨dl, hm, hd⟩
          · exact Or.inl hF
          · right
            refine ⟨dl, arming_leaseOf p Q hinv hm, ?_, ?_⟩
            · change (FGSA.clock p st t).base.now < dl
              rw [(clock_vn st t).2]
              exact htb.trans_le (hend.trans hd)
            · rw [hdom, hZ]
              exact hret
      have hduties : ∀ a ∈ V2.D.Run.emitsAt E rho i,
          (∀ H, HeadTargetAtEmission p c E rho x a t H → Block.Preceq B H) ∧
          (∀ N, a.payload = .proposal N → Block.Preceq B N.parent.erase) := by
        intro a ha
        constructor
        · intro H hH
          obtain ⟨s, _, k, _, hthead, hk, hhead⟩ := arming_emit_head hvalid hx ⟨i, he, ha⟩ hH
          have hki := fgsa_tick_unique E rho hs hk he
          subst k
          have hpos : s ≠ 0 := by
            intro hz
            subst s
            rw [arming_vote_eq] at hthead
            have h6 : 6 * p.Δ ≤ SA.gateTime p.toParams j := by
              rw [arming_gate_eq]
              have : 0 ≤ 4 * p.Δ * (j : Int) := by have := p.deltaPos; positivity
              linarith
            have := p.deltaPos
            norm_num at hthead
            linarith
          rw [hhead]
          exact outage_head_of_root p Q hroot hpos
        · intro N hC
          obtain ⟨s, k, _, _, hk, hparent⟩ := arming_emit_proposal hvalid hx ⟨i, he, ha⟩ hC
          have hki := fgsa_tick_unique E rho hs hk he
          subst k
          rw [hparent]
          exact block_preceq_trans hroot (liveRoot_preceq_headInTree p Q _ _ _)
      have hsource' : OutageSourceHistory p c E rho B (i + 1) := by
        constructor
        intro k y r C hk hy htick hC
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | hki
        · exact hsource.history k y r C hki hy htick hC
        · subst k
          have hyx := (V2.Event.tick.inj (Option.some.inj (htick.symm.trans he))).1
          subst y
          have htime := (V2.Event.tick.inj (Option.some.inj (htick.symm.trans he))).2
          have hpP' : OutageProtection p B j
              (FGSA.clockPre p (storeAt p c E rho i x) (p.actionTime r)) := by
            rw [htime]
            exact hpP
          exact outage_tick_source_compatible hs htsrc htick hy hpP' hC
      have hduty' : OutageDutyHistory p c E rho B j (i + 1) := by
        constructor
        intro k y u a hk hy hdu htick ha
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | hki
        · exact hduty.history k y u a hki hy hdu htick ha
        · subst k
          obtain ⟨rfl, rfl⟩ := V2.Event.tick.inj (Option.some.inj (htick.symm.trans he))
          exact hduties a ha
      refine ⟨hsource', hduty', outage_named_of_source_history (hroots := hroots) hβ hsource'
        hnamed, ?_⟩
      intro y hy
      rcases arming_store_succ hnr he y with heq | ⟨u, hu, _⟩ | ⟨a, u, hu, _⟩
      · rw [heq]
        exact hlocal y hy
      · have hyx : y = x := (V2.Event.tick.inj hu).1.symm
        subst y
        rw [hpost]
        exact hpQ
      · cases hu

end Prefix

section Armed

variable [Fintype V]
variable (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho) (hdelta : E.Δ = p.Δ)
    (hfault : (Gen.V2.Duty.faulty rho).card < SA.releaseThreshold p.toParams)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hnamesFull : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))

include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamesFull in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §8.2–3; O-INDUCT plan §2, §5. Class (iii).
DC: INTENTIONAL; OUTPUT-DIRECT §1: the ArmingCert endpoint is independent
of the induction endpoint, which may equal expiry.
INLINE facts have the same producers as outage_event_induction. -/
theorem outageV_armed_to_expiry {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    {endpoint : Time} (hend : endpoint ≤ SA.gateTime p.toParams (l + 1) + L p)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∃ β : FGBlock (Fin p.n), eraseFG β = B ∧
      ∀ i, afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i →
        i ≤ V2.D.Run.idxBefore rho endpoint →
        OutageSourceHistory p c E rho B i ∧ OutageDutyHistory p c E rho B (l + 1) i ∧
          OutageNamedHistory p c E rho β i ∧
          ∀ y ∈ rho.honest, OutageProtection p B (l + 1) (storeAt p c E rho i y) := by
  have hlocal := outage_arming_local (hroots := hroots) (hstrat := hstrat)
    hvalid hnr hdelta
    hstore hframe hsrc hnamesFull hne hc hgate
  let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
  let st := storeAt p c E rho I u
  have hinv := cstoreInv_stateBefore E rho I u
  obtain ⟨S, hS, hSe⟩ := (hinv.baseTree _).mp hinv.Smem
  have hBS : Block.Preceq B (eraseFG S) := by
    rw [hSe]
    exact (hlocal u hc.origin_honest).1
  obtain ⟨β, _, hβ, _⟩ := eraseFG_ancestor_preceq hinv.fg.closed hS hBS
  have hnamesCond : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C) := by
    intro k x r a e ha he
    obtain ⟨e', C, G, he', hC, hn, hTC, hG, hCG, hf⟩ := hnamesFull k x r a ha
    exact ⟨C, G, hC, (Option.some.inj (he.symm.trans he')).trans hn, hTC, hG, hCG, hf⟩
  refine ⟨β, hβ, ?_⟩
  intro i hI hK
  exact outage_event_induction_le_expiry (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hcstar hdelta
    hfault hstore hframe hsrc htsrc
    hnamesCond hβ hend
    (outage_arming_sources hvalid.toScheduleWellFormed htsrc hc)
    (outage_arming_duties hvalid (l + 1) B) hlocal hc.inflight_heads hI hK

end Armed

/-- OUTPUT-DIRECT §10. DC: INTENTIONAL; inclusive reads use all events
at t, including horizon deliveries. This is the read adapter only; its
local S and F invariant must be proved by the joint continuation induction. -/
theorem outageV_inclusive_outputs {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {B : Block} {b₀ : Time}
    (hlocal : ∀ i, timeIdx rho b₀ ≤ i → i ≤ rho.events.length →
      ∀ y ∈ rho.honest, Block.Preceq B (S_at p c E rho i y) ∧
        Block.Compatible B (F_at p c E rho i y))
    {y : V} {t : Time} (hy : y ∈ rho.honest) (ht : b₀ ≤ t) :
    Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable y t) ∧
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed y t) ∧
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y) := by
  have hlen : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  obtain ⟨hS, hF⟩ := hlocal _ (arming_timeIdx_mono rho ht) hlen y hy
  have hstable := arming_stable_read hs y t
  have hconfirmed : V2.D.outputAt E rho (fgsaInterface p c).confirmed y t =
      S_at p c E rho (timeIdx rho t) y := hstable
  exact ⟨hS, hstable.symm ▸ hS, hconfirmed.symm ▸ hS, hF⟩

end AvailableChain.FGSA.Run
end
