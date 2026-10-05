module
public import AvailableChainFGSAProofs.Proofs.Outage.Induction
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingMain
public import AvailableChainFGSAProofs.Proofs.Shared.Regimes
public import AvailableChainFGSAClaims.Statements.Packages.Outage
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {pt : PtOut} {ΔF : Time}
variable (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho pt.b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ pt.b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : fast = false → ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho pt.b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ pt.b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
  hsavedKeep hsOrigin hmono hcleanGate in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §§6–9; O-INDUCT plan §9.1–2. Class (iii).
DC: INTENTIONAL; split on the canonical pending gate before calling its
boundary producer. INLINE Foundations inputs: activeViewAt, frameAt,
SrcFrameAbove, tSrc, emittedName. INLINE Clean inputs: cleanHistoryAt,
cleanGateAt, and the individual projections of cleanTruncAt at b₀. -/
theorem outage_protected_read (h : OutagePrem p c fast E rho pt ΔF)
    {x : V} {B : Block} (hx : x ∈ rho.honest)
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T))
    (hne : B ≠ .genesis)
    (hstrat : RStrat p c E rho) :
    (∀ y t, y ∈ rho.honest → pt.b₀ ≤ t → t < pt.b₁ →
      Block.Preceq B (S_at p c E rho (timeIdx rho t) y)) ∧
    (∀ y t o, y ∈ rho.honest → pt.b₀ ≤ t → t < pt.b₁ → V2.D.Run.emits E rho y o t →
      (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
      (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)) ∧
    (∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
      Block.Compatible B (F_at p c E rho (timeIdx rho t) y)) ∧
    (∀ t y, SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) ≤ t →
      t < pt.b₁ → y ∈ rho.honest →
      let st := storeAt p c E rho (timeIdx rho t) y
      Block.Preceq B (eraseFG st.fg.F) ∨
        ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
          SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) + L p ≤ dl ∧
          ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
            Block.Preceq B (eraseFG (FGSA.controls p st).Z))) := by
  let l : Slot := ((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat
  by_cases hopen : SA.gateTime p.toParams (l + 1) < pt.b₁
  all_goals
    have harm : ArmingData p c E rho fast pt.T pt.b₀ pt.b₁ B := by
      cases fast with
      | true =>
        exact fast_arming (hroots := h.set.pre.base.idealization)
          (hstrat := hstrat)
          pt.T pt.b₀ pt.b₁ ΔF h.set.pre.base.valid h.set.pre.base.cstar
          h.set.pre.base.noRestart h.set.pre.base.delta h.set.pre.cut h.set.pre.healthy
          h.set.pre.partBefore h.set.order h.set.budget x B hx hread hne
          hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
          hsOrigin hmono hcleanGate h.set.lag (h.set.fastPart rfl)
      | false =>
        exact slow_arming (hroots := h.set.pre.base.idealization)
          (hstrat := hstrat)
          pt.T pt.b₀ pt.b₁ ΔF h.set.pre.base.valid h.set.pre.base.cstar
          h.set.pre.base.noRestart h.set.pre.base.delta h.set.pre.cut h.set.pre.healthy
          h.set.pre.partBefore h.set.order h.set.budget x B hx hread hne
          hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
          (hsavedKeep rfl) hsOrigin hmono hcleanGate h.set.lag
    rw [ArmingData_def] at harm
    obtain ⟨u, s, C, iₛ, D, Dh, hc⟩ := harm
  · have hvt : SA.voteTime p.toParams (l + 1) < pt.b₀ :=
      (arming_vote_lt_early p (l + 1)).1.trans_le
        (hc.early_eq_gate.trans_le hc.gate_le_cut)
    have hv0 : 0 ≤ SA.voteTime p.toParams (l + 1) := by
      rw [arming_vote_eq]
      have := p.deltaPos
      positivity
    have hah := h.set.pre.partBefore _ hv0 hvt
    have hcard : rho.honest.card = p.n - (Gen.V2.Duty.faulty rho).card := by
      rw [Gen.V2.Duty.faulty_def,
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        card_eq_n_of_linked h.set.pre.base.linked]
      have hn := Finset.card_le_univ rho.honest
      rw [card_eq_n_of_linked h.set.pre.base.linked] at hn
      omega
    have hhn : (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams (l + 1))).card ≤
        p.n - (Gen.V2.Duty.faulty rho).card := by
      rw [Gen.V2.Duty.awakeHonest_def, ← hcard]
      exact Finset.card_filter_le _ _
    have hfault := outage_fault_lt_release p hah hhn
    exact duties_and_outputs (hroots := h.set.pre.base.idealization) (hstrat := hstrat)
      h.set.pre.base.valid h.set.pre.base.noRestart h.set.pre.base.cstar
      h.set.pre.base.delta hfault hstore hframe hsrc htsrc hnamed hne hc hopen h.set.order.2.2.2
  · have hbd : pt.b₁ ≤ SA.gateTime p.toParams (l + 1) := le_of_not_gt hopen
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y t hy hbt htb
      exact hc.pending_cover y t hy (hc.gate_le_cut.trans hbt) (htb.trans_le hbd)
        (htb.le.trans h.set.order.2.2.2)
    · intro y t o hy hbt htb hem
      exact hc.pending_duties y o t hy (hc.gate_le_cut.trans hbt) (htb.trans_le hbd) hem
    · intro t y h0 htb hy
      exact hc.pending_compat y t hy h0 (htb.trans_le hbd) (htb.le.trans h.set.order.2.2.2)
    · intro t y hdt htb hy
      exact (not_lt_of_ge (hbd.trans hdt) htb).elim

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
O-INDUCT plan §9.1 public-read conversion. Class (iii).
DC: INTENTIONAL; finalizedOut uses the same inclusive prefix as S. -/
theorem outage_finalized_read (hs : V2.D.ScheduleWellFormed E rho) (y : V) (t : Time) :
    V2.D.outputAt E rho finalizedOut y t = F_at p c E rho (timeIdx rho t) y := by
  change eraseFG (V2.D.Run.readAt E rho t y).st.fg.F = _
  rw [V2.D.Engine.readAt_eq_stateBefore hs t]
  rfl

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
  hsavedKeep hsOrigin hmono hcleanGate in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §9; O-INDUCT plan §9.2. Class (iii).
DC: INTENTIONAL; the exact expanded OutageCompat body. All cross-lane
facts stay inline and have the producers listed on outage_protected_read. -/
theorem outage_compat_body (h : OutagePrem p c fast E rho pt ΔF)
    (hstrat : RStrat p c E rho) :
    ((∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, x ∈ rho.honest → Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
        ServedOn (· ∈ rho.honest) (fun t y => V2.D.outputAt E rho g y t) B
          (fun t => pt.b₀ ≤ t ∧ t < pt.b₁)) ∧
    (∀ x B, x ∈ rho.honest →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      (∀ y t o, y ∈ rho.honest → pt.b₀ ≤ t → t < pt.b₁ → V2.D.Run.emits E rho y o t →
        (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
        (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)) ∧
      (∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
        Block.Compatible B (V2.D.outputAt E rho finalizedOut y t)))) ∧
    (∀ x B, x ∈ rho.honest →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) → B ≠ .genesis →
      ∀ t y, SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) ≤ t →
        t < pt.b₁ → y ∈ rho.honest →
        let st := storeAt p c E rho (timeIdx rho t) y
        Block.Preceq B (eraseFG st.fg.F) ∨
          ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
            SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z))) := by
  have hs := h.set.pre.base.valid.toScheduleWellFormed
  constructor
  · constructor
    · intro g hg x B hx hread t y ht hy
      change Block.Preceq B (V2.D.outputAt E rho g y t)
      by_cases hgen : B = .genesis
      · subst B
        exact block_genesis_preceq _
      · rw [fgsa_outputAt_eq_S_at E rho hs g hg x pt.T] at hread
        have hstable : Block.Preceq B
            (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) := by
          rw [arming_stable_read hs]
          exact hread
        have hp := outage_protected_read (hstrat := hstrat) (hstore := hstore)
          (hframe := hframe)
          (hsrc := hsrc)
          (htsrc := htsrc)
          (hnamed := hnamed)
          (hordered := hordered)
          (hnonempty := hnonempty)
          (htransfer := htransfer)
          (hbelow := hbelow)
          (hleaseOrigin := hleaseOrigin)
          (hsavedKeep := hsavedKeep)
          (hsOrigin := hsOrigin)
          (hmono := hmono)
          (hcleanGate := hcleanGate) h hx hstable hgen
        rw [fgsa_outputAt_eq_S_at E rho hs g hg y t]
        exact hp.1 y t hy ht.1 ht.2
    · intro x B hx hread
      by_cases hgen : B = .genesis
      · subst B
        refine ⟨?_, ?_⟩
        · intro y t o hy hbt htb hem
          exact ⟨fun H _ => block_genesis_preceq H,
            fun N _ => block_genesis_preceq N.parent.erase⟩
        · intro t y h0 htb hy
          exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
      · have hp := outage_protected_read (hstrat := hstrat) (hstore := hstore)
          (hframe := hframe)
          (hsrc := hsrc)
          (htsrc := htsrc)
          (hnamed := hnamed)
          (hordered := hordered)
          (hnonempty := hnonempty)
          (htransfer := htransfer)
          (hbelow := hbelow)
          (hleaseOrigin := hleaseOrigin)
          (hsavedKeep := hsavedKeep)
          (hsOrigin := hsOrigin)
          (hmono := hmono)
          (hcleanGate := hcleanGate) h hx hread hgen
        refine ⟨hp.2.1, ?_⟩
        intro t y h0 htb hy
        rw [outage_finalized_read hs]
        exact hp.2.2.1 t y h0 htb hy
  · intro x B hx hread hne
    exact (outage_protected_read (hstrat := hstrat) (hstore := hstore)
          (hframe := hframe)
          (hsrc := hsrc)
          (htsrc := htsrc)
          (hnamed := hnamed)
          (hordered := hordered)
          (hnonempty := hnonempty)
          (htransfer := htransfer)
          (hbelow := hbelow)
          (hleaseOrigin := hleaseOrigin)
          (hsavedKeep := hsavedKeep)
          (hsOrigin := hsOrigin)
          (hmono := hmono)
          (hcleanGate := hcleanGate) h hx hread hne).2.2.2

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
  hsOrigin hmono hcleanGate in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §9.1; O-INDUCT plan §9.3. Class (iii).
DC: INTENTIONAL; the exact expanded FastP1 body returns the P1 pair. -/
theorem fast_p1_body (h : OutagePrem p c true E rho pt ΔF)
    (hstrat : RStrat p c E rho) :
    (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, x ∈ rho.honest → Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
        ServedOn (· ∈ rho.honest) (fun t y => V2.D.outputAt E rho g y t) B
          (fun t => pt.b₀ ≤ t ∧ t < pt.b₁)) ∧
    (∀ x B, x ∈ rho.honest →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      (∀ y t o, y ∈ rho.honest → pt.b₀ ≤ t → t < pt.b₁ → V2.D.Run.emits E rho y o t →
        (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
        (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)) ∧
      (∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
        Block.Compatible B (V2.D.outputAt E rho finalizedOut y t))) := by
  exact (outage_compat_body (hstrat := hstrat) (fast := true) (hstore := hstore)
    (hframe := hframe)
    (hsrc := hsrc)
    (htsrc := htsrc)
    (hnamed := hnamed)
    (hordered := hordered)
    (hnonempty := hnonempty)
    (htransfer := htransfer)
    (hbelow := hbelow)
    (hleaseOrigin := hleaseOrigin)
    (hsOrigin := hsOrigin)
    (hmono := hmono)
    (hcleanGate := hcleanGate)
    (hsavedKeep := fun h => nomatch h) h).1

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow hleaseOrigin
  hsOrigin hmono hcleanGate in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §9.2; O-INDUCT plan §9.4. Class (iii).
DC: INTENTIONAL; the exact expanded SlowP1 body retains the lease field. -/
theorem slow_p1_body
    (hsavedKeepSlow : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (h : OutagePrem p c false E rho pt ΔF)
    (hstrat : RStrat p c E rho) :
    ((∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ∀ x B, x ∈ rho.honest → Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
        ServedOn (· ∈ rho.honest) (fun t y => V2.D.outputAt E rho g y t) B
          (fun t => pt.b₀ ≤ t ∧ t < pt.b₁)) ∧
    (∀ x B, x ∈ rho.honest →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
      (∀ y t o, y ∈ rho.honest → pt.b₀ ≤ t → t < pt.b₁ → V2.D.Run.emits E rho y o t →
        (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
        (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)) ∧
      (∀ t y, 0 ≤ t → t < pt.b₁ → y ∈ rho.honest →
        Block.Compatible B (V2.D.outputAt E rho finalizedOut y t)))) ∧
    (∀ x B, x ∈ rho.honest →
      Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) → B ≠ .genesis →
      ∀ t y, SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) ≤ t →
        t < pt.b₁ → y ∈ rho.honest →
        let st := storeAt p c E rho (timeIdx rho t) y
        Block.Preceq B (eraseFG st.fg.F) ∨
          ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
            SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z))) := by
  exact outage_compat_body (hstrat := hstrat) (fast := false) (hstore := hstore)
    (hframe := hframe)
    (hsrc := hsrc)
    (htsrc := htsrc)
    (hnamed := hnamed)
    (hordered := hordered)
    (hnonempty := hnonempty)
    (htransfer := htransfer)
    (hbelow := hbelow)
    (hleaseOrigin := hleaseOrigin)
    (hsOrigin := hsOrigin)
    (hmono := hmono)
    (hcleanGate := hcleanGate)
    (hsavedKeep := fun _ => hsavedKeepSlow) h

end AvailableChain.FGSA.Run
end
