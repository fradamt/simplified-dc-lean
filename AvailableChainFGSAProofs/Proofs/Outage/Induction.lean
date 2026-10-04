module
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceStep
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceFrame
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceRelease
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingDuty

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

private def BoundedTCompat (B : Block) (j : Slot) (b₁ : Time) : Prop :=
  ∀ x r C, x ∈ rho.honest → SA.gateTime p.toParams j ≤ p.actionTime r →
    p.actionTime r < b₁ → actionSource p c E rho x r = some (some C) → Block.Compatible C B

private theorem bounded_tCompat (hs : V2.D.ScheduleWellFormed E rho)
    {B : Block} {j : Slot} {b₁ : Time}
    (hist : OutageSourceHistory p c E rho B (V2.D.Run.idxBefore rho b₁)) :
    BoundedTCompat (p := p) (c := c) (E := E) (rho := rho) B j b₁ := by
  intro x r C hx _ hr hC
  have ht : ∃ k : Nat, rho.events[k]? =
      some (V2.Event.tick x (p.actionTime r) : V2.Event V (Obj p)) := by
    cases he : V2.D.Run.tickIdx? rho x (p.actionTime r) with
    | none =>
      have hn : actionSource p c E rho x r = none := by
        change ((postClock E rho x (p.actionTime r)).map _).map _ = _
        rw [postClock_def, preTick_def, he]
        rfl
      rw [hn] at hC
      cases hC
    | some k => exact ⟨k, V2.D.Run.tickIdx?_spec he⟩
  obtain ⟨k, hk⟩ := ht
  exact hist.history k x r C ((Gen.V2.Duty.index_lt_idxBefore_iff hs hk _).mpr hr) hx hk hC

/-- Blueprint 03 §8.1; O-INDUCT plan §2 handoff. Class (iii).
DC: INTENTIONAL; all old sources, including the pending action at d,
are compatible with B. The real ArmingCert fields give the two cases.
INLINE htsrc: sourceDiscipline_tSrc. -/
theorem outage_arming_sources (hs : V2.D.ScheduleWellFormed E rho)
    (htsrc : TSrc p c E rho) {fast : Bool} {T b₀ b₁ : Time} {B : Block}
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh) :
    OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) := by
  constructor
  intro k y r X hk hy htick hX
  have htime : p.actionTime r ≤ SA.gateTime p.toParams (l + 1) :=
    arming_tick_le hs htick (hk.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
  rcases htime.lt_or_eq with hlt | heq
  · exact block_compatible_of_common (hc.source_below y r X hy hlt hX) hc.max_read
  · obtain ⟨Xs, G, _, hXm, hG, hXG, _, _, _, _⟩ := htsrc y r X hy hX
    have hrj : r * p.R = l + 1 := by
      exact Nat.le_antisymm ((arming_gate_le_iff p _ _).mp heq.le)
        ((arming_gate_le_iff p _ _).mp heq.symm.le)
    have hgt : IsGateTick p c rho k y (l + 1) := by
      change rho.events[k]? = some (.tick y (SA.gateTime p.toParams (l + 1)))
      rw [← heq]
      exact htick
    obtain ⟨_, ⟨Cj, hraw, hDCj⟩, _⟩ := hc.pending_input k y hgt hy
    rw [hrj] at hG
    have hGj := (arming_gateResult_tick hs hgt).trans (congrArg some hraw)
    have hGC : G = Cj := Option.some.inj (Option.some.inj (hG.symm.trans hGj))
    rw [hGC] at hXG
    exact block_compatible_of_common (hXG X hXm) (block_preceq_trans hc.max_read hDCj)

/-- Blueprint 03 §8.1; O-INDUCT plan §2 all-ticks cut. Class (iii).
DC: INTENTIONAL; ticks at the pending gate emit no HEAD or proposal,
so the post-pending duty history is empty at the seed. -/
theorem outage_arming_duties (hvalid : V2.D.ExecutionValid E rho) (j : Slot) (B : Block) :
    OutageDutyHistory p c E rho B j (afterTicksIdx rho (SA.gateTime p.toParams j)) := by
  constructor
  intro k y t o hk hy hdt htick ho
  have htd : t ≤ SA.gateTime p.toParams j :=
    arming_tick_le hvalid.toScheduleWellFormed htick
      (hk.trans_le (preIdx_le_afterTicksIdx E rho hvalid.toScheduleWellFormed _).2)
  have hte : t = SA.gateTime p.toParams j := le_antisymm htd hdt
  constructor
  · intro H hH
    obtain ⟨s, _, _, _, he, _, _⟩ := arming_emit_head hvalid hy ⟨k, htick, ho⟩ hH
    exact (arming_gate_ne_vote p j s (hte.symm.trans he)).elim
  · intro X raw sup rows hX
    obtain ⟨s, _, _, he, _, _⟩ := arming_emit_proposal hvalid hy ⟨k, htick, ho⟩ hX
    exact (arming_gate_ne_proposal p j s (hte.symm.trans he)).elim

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
/-- ROOT-DIGEST W2b. Blueprint 03 §8.2–3; O-INDUCT plan §5. Class (iii).
DC: INTENTIONAL; one joint induction on tick and delivery prefixes.
The seeds have producers outage_arming_sources, outage_arming_duties,
and pending_gate_lease_or_F. INLINE channels: Foundations active/frame,
SrcFrameAbove, sourceDiscipline_tSrc, and sourceDiscipline_emittedName.
The strict endpoint prevents processing any event at b₁. -/
theorem outage_event_induction {B : Block} {β : FGBlock (Fin p.n)} {j : Slot} {b₁ : Time}
    (hβ : eraseFG β = B) (hend : b₁ < SA.gateTime p.toParams j + L p)
    (hseedSource : OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hseedDuty : OutageDutyHistory p c E rho B j (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hseedLocal : ∀ y ∈ rho.honest,
      OutageProtection p B j (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams j)) y))
    (hseedHeads : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q → o.payload = .head H → Block.Preceq B H)
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
      have htb : t < b₁ := by simpa only [hevent, V2.Event.time] using htend
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
        have hbound := outage_release_bound hvalid hnr hcstar hdelta htick (hr ▸ hdt)
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
              (htb.trans_le (hend.le.trans hd)) hcounts, hd⟩
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
          unfold FGSA.fullTree
          rw [hfg]
        have hZ : FGSA.controls p Q = FGSA.controls p st := by
          unfold FGSA.controls
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
              exact htb.trans_le (hend.le.trans hd)
            · rw [hdom, hZ]
              exact hret
      have hduties : ∀ a ∈ V2.D.Run.emitsAt E rho i,
          (∀ H, a.payload = .head H → Block.Preceq B H) ∧
          (∀ C raw sup rows, a.payload = .proposal C raw sup rows → Block.Preceq B C.parent) := by
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
        · intro C raw sup rows hC
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

omit [Fintype V] in
include hvalid hnr hdelta hstore hframe hsrc hnamesFull in
/-- ROOT-DIGEST W2b. Blueprint 03 §8.1; O-INDUCT plan §2. Class (iii).
DC: INTENTIONAL; the selected-row adapter of the real O-ARM handoff.
No field is added to ArmingData. INLINE names: Foundations emittedName. -/
theorem outage_arming_local {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ y ∈ rho.honest, OutageProtection p B (l + 1)
      (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y) := by
  intro y hy
  obtain ⟨hS, hF | ⟨_, _, dl, hlease, _, hd, _⟩⟩ :=
    arming_gate_core (hroots := hroots) (hstrat := hstrat)  hvalid hnr hdelta
      hstore hframe hsrc
      hnamesFull hne hc hgate y hy
  · exact ⟨hS, Or.inl hF⟩
  · exact ⟨hS, Or.inr ⟨dl, outage_row_of_lease p _
      (cstoreInv_stateBefore E rho _ y) hlease, hd⟩⟩

include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamesFull in
/-- ROOT-DIGEST W2b. Blueprint 03 §8.2–3; O-INDUCT plan §2, §5. Class (iii).
DC: INTENTIONAL; the joint induction is seeded by the landed ArmingCert.
INLINE facts have the same producers as outage_event_induction. -/
theorem outage_armed_induction {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∃ β : FGBlock (Fin p.n), eraseFG β = B ∧
      ∀ i, afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i →
        i ≤ V2.D.Run.idxBefore rho b₁ →
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
  exact outage_event_induction (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hcstar hdelta
    hfault hstore hframe hsrc htsrc
    hnamesCond hβ hc.end_lt_deadline
    (outage_arming_sources hvalid.toScheduleWellFormed htsrc hc)
    (outage_arming_duties hvalid (l + 1) B) hlocal hc.inflight_heads hI hK


variable {fast : Bool} {T b₀ b₁ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {u : V} {s : Slot} {C : Block} {iₛ : Nat} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hc : ArmingCert p c E rho fast T b₀ b₁ B l u s C iₛ D Dh)
    (hopen : SA.gateTime p.toParams (l + 1) < b₁) (hhor : b₁ ≤ rho.horizon)

include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamesFull hne hc hopen hhor in
/-- ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §3.4. Class (iii).
DC: INTENTIONAL; the expanded finite source projection. Its type does
not expose the private bounded compatibility predicate. -/
theorem outage_source_history
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ x r X, x ∈ rho.honest → SA.gateTime p.toParams (l + 1) ≤ p.actionTime r →
      p.actionTime r < b₁ → actionSource p c E rho x r = some (some X) →
        Block.Compatible X B := by
  obtain ⟨β, hβ, hhist⟩ := outage_armed_induction (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hcstar hdelta hfault hstore
    hframe hsrc htsrc hnamesFull hne hc (hopen.le.trans hhor)
  have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ V2.D.Run.idxBefore rho b₁ :=
    (preIdx_le_afterTicksIdx E rho hvalid.toScheduleWellFormed _).2.trans
      (arming_timeIdx_le_idxBefore rho hopen)
  exact bounded_tCompat hvalid.toScheduleWellFormed (hhist _ hI le_rfl).1

include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamesFull hne hc hopen hhor in
/-- ROOT-DIGEST W2b. Blueprint 03 §8.2; O-INDUCT plan §9.1. Class (iii).
DC: INTENTIONAL; the selected row survives every inclusive public read,
including the delivery suffix at d. The strict deadline gives t < dl. -/
theorem lease_or_F_persists
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    ∀ t y, SA.gateTime p.toParams (l + 1) ≤ t → t < b₁ → y ∈ rho.honest →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
          ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z)) := by
  obtain ⟨β, hβ, hhist⟩ := outage_armed_induction (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hcstar hdelta hfault hstore
    hframe hsrc htsrc hnamesFull hne hc (hopen.le.trans hhor)
  intro t y hdt htb hy st
  have hI : afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ timeIdx rho t :=
    (afterTicksIdx_mono rho hdt).trans
      (preIdx_le_afterTicksIdx E rho hvalid.toScheduleWellFormed t).2
  obtain ⟨_, _, hnames, hlocal⟩ := hhist _ hI (arming_timeIdx_le_idxBefore rho htb)
  have hret := (outage_frame_retains (hstrat := hstrat) hstore hframe hsrc hy hβ hnames (hlocal y
    hy).1).2
  rcases hret with hF | hret
  · exact Or.inl hF
  · rcases (hlocal y hy).2 with hF | ⟨dl, hm, hd⟩
    · exact Or.inl hF
    · exact Or.inr ⟨dl, arming_leaseOf p st (cstoreInv_stateBefore E rho _ y) hm,
        htb.trans_le (hc.end_lt_deadline.le.trans hd), hd, hret⟩

include hvalid hnr hcstar hdelta hfault hstore hframe hsrc htsrc hnamesFull hne hc hopen hhor in
/-- ROOT-DIGEST W2b. Blueprint 03 §8.2–3; O-INDUCT plan §9.1. Class (iii).
DC: INTENTIONAL; the exact expanded protected-read conclusion.
Compatibility starts at zero; output and duties start at b₀; the selected
lease starts at d. Every interval ends strictly before b₁. -/
theorem duties_and_outputs
    (hroots : NamedRootCollisionFree p c E rho)
    (hstrat : RStrat p c E rho) :
    (∀ y t, y ∈ rho.honest → b₀ ≤ t → t < b₁ →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y)) ∧
    (∀ y t o, y ∈ rho.honest → b₀ ≤ t → t < b₁ → V2.D.Run.emits E rho y o t →
      (∀ H, o.payload = .head H → Block.Preceq B H) ∧
      (∀ X raw sup rows, o.payload = .proposal X raw sup rows → Block.Preceq B X.parent)) ∧
    (∀ t y, 0 ≤ t → t < b₁ → y ∈ rho.honest →
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y)) ∧
    (∀ t y, SA.gateTime p.toParams (l + 1) ≤ t → t < b₁ → y ∈ rho.honest →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
          ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z))) := by
  obtain ⟨β, hβ, hhist⟩ := outage_armed_induction (hroots := hroots) (hstrat := hstrat)  hvalid hnr
    hcstar hdelta hfault hstore
    hframe hsrc htsrc hnamesFull hne hc (hopen.le.trans hhor)
  have hread (t : Time) (hdt : SA.gateTime p.toParams (l + 1) ≤ t) (htb : t < b₁) :=
    hhist (timeIdx rho t)
      ((afterTicksIdx_mono rho hdt).trans
        (preIdx_le_afterTicksIdx E rho hvalid.toScheduleWellFormed t).2)
      (arming_timeIdx_le_idxBefore rho htb)
  refine ⟨?_, ?_, ?_, lease_or_F_persists (hroots := hroots) (hstrat := hstrat)
    hvalid hnr hcstar
    hdelta hfault hstore hframe
    hsrc htsrc hnamesFull hne hc hopen hhor⟩
  · intro y t hy hbt htb
    rcases lt_or_ge t (SA.gateTime p.toParams (l + 1)) with htd | hdt
    · exact hc.pending_cover y t hy (hc.gate_le_cut.trans hbt) htd (htb.le.trans hhor)
    · exact ((hread t hdt htb).2.2.2 y hy).1
  · intro y t o hy hbt htb hem
    rcases lt_or_ge t (SA.gateTime p.toParams (l + 1)) with htd | hdt
    · exact hc.pending_duties y o t hy (hc.gate_le_cut.trans hbt) htd hem
    · obtain ⟨k, hk, ho⟩ := hem
      exact (hread t hdt htb).2.1.history k y t o
        ((arming_lt_timeIdx_iff hvalid.toScheduleWellFormed t hk).mpr le_rfl) hy hdt hk ho
  · intro t y h0 htb hy
    rcases lt_or_ge t (SA.gateTime p.toParams (l + 1)) with htd | hdt
    · exact hc.pending_compat y t hy h0 htd (htb.le.trans hhor)
    · obtain ⟨_, _, hnames, hlocal⟩ := hread t hdt htb
      have hcomp := (outage_frame_retains (hstrat := hstrat) hstore hframe hsrc hy hβ hnames
        (hlocal y hy).1).1
      change Block.compatible B (F_at p c E rho (timeIdx rho t) y) = true
      rw [block_compatible_comm]
      exact hcomp

end Armed

end AvailableChain.FGSA.Run
end
