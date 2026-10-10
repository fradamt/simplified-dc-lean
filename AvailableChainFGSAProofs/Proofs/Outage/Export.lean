module
public import AvailableChainFGSAProofs.Proofs.Outage.Suppliers
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthConsumer
public import AvailableChainFGSAProofs.Proofs.Outage.Close
public import AvailableChainFGSAProofs.Proofs.Shared.Claims
-- shake: keep (Clean cut statement boundary)


public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable (p : Params)

section CleanClaims

-- Each supplier has the same binders and conclusion as its reviewed projection.
variable
    (hstore : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RStore p c E rho)
    (hframe : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RFrameExactNext p c E rho)
    (hstrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → RStrat p c E rho)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hordered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
        confirmedReader p c E rho x (SA.gateTime p.toParams r) →
        confirmedReader p c E rho y (SA.gateTime p.toParams s) →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ j x s, j < timeIdx rho pt.b₀ → x ∈ rho.honest → enabledGateAt p c E rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ pt.b₀ → gateResult p c E rho x s = some (some B) →
        joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
        vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i v, i ≤ timeIdx rho pt.b₀ → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → enabledGateAt p c E rho j v s →
          V2.D.restartFree rho v j i → FGSA.activeCompatible st C = true →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, V2.D.restartFree rho v j i ∧
          enabledGateAt p c E rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, enabledGateAt p c E rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)))
    (hrows : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i j x r a e, i ≤ timeIdx rho pt.b₀ → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))

-- The internal services cover in-horizon early reads and actual relay vote ticks.
variable
    (hInputs : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF → InclusionReceiverInputs E rho)

include hstore hframe hstrat hsrc hordered hnonempty htransfer hleases hrows hInputs

/-- ROOT-DIGEST W2b. Blueprint 03 §4; DC available/stableIncludedFast: INTENTIONAL exact HEAD.
The supplier projections restore the frozen claim, including sleep silence. -/
theorem outage_exactProposalClaim_of : ExactProposalClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hv : 0 < SA.voteTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hv.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hv.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  exact ⟨fun x hx hJ => inclusion_exact_receipt (_hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
    E rho ΔF h.set (hInputs c E rho () ⟨h.set⟩)
    (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor x ⟨hx, hJ⟩,
    inclusion_exact_head (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
      E rho ΔF h.set (hInputs c E rho () ⟨h.set⟩) (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor,
    inclusion_sleep_silence E rho pt.s⟩

variable
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ rho.events.length))
    (hScopes : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF → ∀ s i x, x ∈ rho.honest →
        enabledGateAt p c E rho i x s ∨
          confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams s))
            (SA.gateTime p.toParams s) →
        IsGateTick p c rho i x s → GateReceiptScope E rho i x s)

include hmono hScopes

/-- ROOT-DIGEST W2b. Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL post-gate event
read.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionPostGateClaim_of : CleanInclusionPostGateClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hg.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  have hHistory : InclusionHistoryBounds E rho := ⟨by
    intro i x hi hx
    have hb := hl i x hi hx
    exact ⟨hb.1, hb.2.1, hb.2.2.1,
      fun row hr => (hb.2.2.2.1 row hr).1,
      fun r C hC => (hb.2.2.2.2.1 r C hC).1⟩⟩
  exact clean_inclusion_post_gate_body (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩) E rho ΔF
    h.set (hInputs c E rho () ⟨h.set⟩) hHistory (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor (hmono c E rho () ⟨h.set⟩)
    (hScopes c E rho () ⟨h.set⟩ pt.s)

variable
    (hReaderGate : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
        enabledGateAt p c E rho i x q →
        ∃ C, gateResultAt p c E rho i = some (some C) ∧
          Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x))
    (hReaderMono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      ScopedMono (confirmedReader p c E rho)
        (fun t x => S_at p c E rho (timeIdx rho t) x)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))

include hReaderGate hReaderMono

omit hmono in
/-- ROOT-DIGEST W2b. Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL inclusive public
reads.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionClaim_of : CleanInclusionClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  obtain ⟨hs, ho, hn, ht, hl, hr⟩ :=
    outage_supplier_history p hsrc hordered hnonempty htransfer hleases hrows
      c E rho h.set (hg.trans_le h.hhor)
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  have hHistory : InclusionHistoryBounds E rho := ⟨by
    intro i x hi hx
    have hb := hl i x hi hx
    exact ⟨hb.1, hb.2.1, hb.2.2.1,
      fun row hr => (hb.2.2.2.1 row hr).1,
      fun r C hC => (hb.2.2.2.2.1 r C hC).1⟩⟩
  exact clean_inclusion_body (hstrat := hstrat c E rho () ⟨h.set.pre.base, hq⟩)
    E rho ΔF h.set (hInputs c E rho () ⟨h.set⟩) hHistory
    (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor (hScopes c E rho () ⟨h.set⟩ pt.s)
    (outage_supplier_later_origins E rho h.set.pre.base
      (hReaderGate c E rho () ⟨h.set⟩) (hReaderMono c E rho () ⟨h.set⟩) pt.s)


end CleanClaims

/-- P20: only the two scoped growth suppliers are parameters. The preceding
CleanClaims include lists do not apply outside that section. -/
theorem outage_cleanGrowthClaim_of (p : Params)
    (hcompatible : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time),
      CleanSet p c E rho ΔF →
      ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u)) :
    CleanGrowthClaim p := by
  exact clean_growth_claim_body p hcompatible hinclusion


section OutageClaims

variable
    (hstore : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RStore p c E rho)
    (hframe : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RFrameExactNext p c E rho)
    (hstrat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → RStrat p c E rho)
    (hsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho)
    (hordered : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
        gateResult p c E rho x r = some (some B) →
        gateResult p c E rho y s = some (some C) →
        (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ j x s, j < timeIdx rho pt.b₀ → x ∈ rho.honest → IsGateTick p c rho j x s →
        ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
        SA.gateTime p.toParams s ≤ pt.b₀ → gateResult p c E rho x s = some (some B) →
        vHead p c E rho y s = some H → Block.Preceq B H)
    (htsrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      BasePrem p c E rho pt →
      ∀ y r C, y ∈ rho.honest → actionSource p c E rho y r = some (some C) →
        ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
          gateResult p c E rho y (r * p.R) = some (some G) ∧
          (∀ A ∈ X, Block.Preceq A G) ∧
          (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
          ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      BasePrem p c E rho pt →
      ∀ i y r a, HonestRowAt p c E rho i y r a →
        ∃ e C G, namedEntry a.payload.height_pair = some e ∧
          actionSourceFG p c E rho y r = some (some C) ∧
          e = ((heightView p C).h, (heightView p C).T_h.root) ∧
          FGBlock.Preceq (heightView p C).T_h C ∧
          gateResult p c E rho y (r * p.R) = some (some G) ∧
          Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C))
    (hbelow : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
          below (S_at p c E rho i y))
    (hleaseOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
        ∀ row ∈ (storeAt p c E rho i y).base.obligations,
          ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧ gatePassedAt p c E rho q ∧
            gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
        ∀ q s C, q < i → IsGateTick p c rho q y s →
          gateResultAt p c E rho q = some (some C) →
          GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
        S_at p c E rho i y = .genesis ∨
        (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
          gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
        (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ y, y ∈ rho.honest → ∀ i k, i ≤ k → k ≤ timeIdx rho pt.b₀ →
        Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ r y, SA.gateTime p.toParams r ≤ pt.b₀ → y ∈ rho.honest →
        ∃ C, gateResult p c E rho y r = some (some C) ∧
          (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
          Block.Preceq C (S_at p c E rho
            (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
          ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
            Block.Preceq C' C)

include hstore hframe hstrat hsrc htsrc hnamed hordered hnonempty htransfer hbelow
  hleaseOrigin hsOrigin hmono hcleanGate

include hsavedKeep in
/-- ROOT-DIGEST W2b. Blueprint 03 §9. The suppliers prove the frozen OutageCompatClaim.
The outage premise and point come from the claim binders. -/
theorem outage_outageCompatClaim_of : OutageCompatClaim p := by
  intro V _ _ In c E rho fast pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hc : CleanCutPrem p c E rho ⟨pt.b₀⟩ ΔF := ⟨h.set.pre⟩
  exact outage_compat_body (hstrat := hstrat c E rho ()
    ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstore := hstore c E rho) (hframe := hframe c E rho)
    (hsrc := hsrc c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := htsrc c E rho () hb) (hnamed := hnamed c E rho () hb)
    (hordered := hordered c E rho ⟨pt.b₀⟩ hc)
    (hnonempty := hnonempty c E rho ⟨pt.b₀⟩ hc)
    (htransfer := htransfer c E rho ⟨pt.b₀⟩ hc)
    (hbelow := hbelow c E rho ⟨pt.b₀⟩ hc)
    (hleaseOrigin := hleaseOrigin c E rho ⟨pt.b₀⟩ hc)
    (hsOrigin := hsOrigin c E rho ⟨pt.b₀⟩ hc)
    (hmono := hmono c E rho ⟨pt.b₀⟩ hc)
    (hcleanGate := hcleanGate c E rho ⟨pt.b₀⟩ hc)
    (hsavedKeep := fun _ => hsavedKeep c E rho ⟨pt.b₀⟩ hc) h

/-- ROOT-DIGEST W2b. Blueprint 03 §9. The suppliers prove the frozen FastP1Claim.
The outage premise and point come from the claim binders. -/
theorem outage_fastP1Claim_of : FastP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hc : CleanCutPrem p c E rho ⟨pt.b₀⟩ ΔF := ⟨h.set.pre⟩
  exact fast_p1_body (hstrat := hstrat c E rho ()
    ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstore := hstore c E rho) (hframe := hframe c E rho)
    (hsrc := hsrc c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := htsrc c E rho () hb) (hnamed := hnamed c E rho () hb)
    (hordered := hordered c E rho ⟨pt.b₀⟩ hc)
    (hnonempty := hnonempty c E rho ⟨pt.b₀⟩ hc)
    (htransfer := htransfer c E rho ⟨pt.b₀⟩ hc)
    (hbelow := hbelow c E rho ⟨pt.b₀⟩ hc)
    (hleaseOrigin := hleaseOrigin c E rho ⟨pt.b₀⟩ hc)
    (hsOrigin := hsOrigin c E rho ⟨pt.b₀⟩ hc)
    (hmono := hmono c E rho ⟨pt.b₀⟩ hc)
    (hcleanGate := hcleanGate c E rho ⟨pt.b₀⟩ hc)
    h

include hsavedKeep in
/-- ROOT-DIGEST W2b. Blueprint 03 §9. The suppliers prove the frozen SlowP1Claim.
The outage premise and point come from the claim binders. -/
theorem outage_slowP1Claim_of : SlowP1Claim p := by
  intro V _ _ In c E rho pt ΔF h
  have hb : BasePrem p c E rho () := ⟨h.set.pre.base⟩
  have hc : CleanCutPrem p c E rho ⟨pt.b₀⟩ ΔF := ⟨h.set.pre⟩
  exact slow_p1_body (hstrat := hstrat c E rho ()
    ⟨h.set.pre.base, h.set.faultQ⟩)
    (hstore := hstore c E rho) (hframe := hframe c E rho)
    (hsrc := hsrc c E rho () ⟨h.set.pre.base, h.set.faultQ⟩)
    (htsrc := htsrc c E rho () hb) (hnamed := hnamed c E rho () hb)
    (hordered := hordered c E rho ⟨pt.b₀⟩ hc)
    (hnonempty := hnonempty c E rho ⟨pt.b₀⟩ hc)
    (htransfer := htransfer c E rho ⟨pt.b₀⟩ hc)
    (hbelow := hbelow c E rho ⟨pt.b₀⟩ hc)
    (hleaseOrigin := hleaseOrigin c E rho ⟨pt.b₀⟩ hc)
    (hsOrigin := hsOrigin c E rho ⟨pt.b₀⟩ hc)
    (hmono := hmono c E rho ⟨pt.b₀⟩ hc)
    (hcleanGate := hcleanGate c E rho ⟨pt.b₀⟩ hc)
    (hsavedKeepSlow := hsavedKeep c E rho ⟨pt.b₀⟩ hc) h

end OutageClaims

section OutageCut

variable {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {pt : PtOut} {ΔF : Time}

/-- ROOT-DIGEST W2b. Blueprint 03 §9. One Clean cut result supplies all nine Clean inputs.
Monotonicity applies only up to the inclusive cut at b₀. -/
theorem outage_compat_body_of_cut
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
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
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho y (r * p.R) (eraseFG C))
    (hcut : CleanHistoryAt p c E rho pt.b₀ ∧ CleanTruncAt p c E rho pt.b₀)
    (h : OutagePrem p c fast E rho pt ΔF)
    (hstrat : RStrat p c E rho) : OutageCompatAt p c E rho pt := by
  have hl := hcut.1.2.2.2.1
  exact outage_compat_body (hstrat := hstrat)
    (hstore := hstore) (hframe := hframe) (hsrc := hsrc)
    (htsrc := htsrc) (hnamed := hnamed)
    (hordered := hcut.1.1) (hnonempty := hcut.1.2.1) (htransfer := hcut.1.2.2.1)
    (hbelow := fun i y hi hy => ⟨(hl i y hi hy).1,
      (hl i y hi hy).2.1, (hl i y hi hy).2.2.1⟩)
    (hleaseOrigin := fun i y hi hy row hrow => ((hl i y hi hy).2.2.2.1 row hrow).2)
    (hsavedKeep := fun _ i y hi hy => (hl i y hi hy).2.2.2.2.2.1)
    (hsOrigin := fun i y hi hy => (hl i y hi hy).2.2.2.2.2.2.2)
    (hmono := fun y hy i k hik hk => hcut.2.2.1 i k y (hik.trans hk) hk hik hy)
    (hcleanGate := hcut.2.2.2.2.2.2) h

end OutageCut

end AvailableChain.FGSA.Run
end
