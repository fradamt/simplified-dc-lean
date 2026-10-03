module
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody
public import AvailableChainFGSAClaims.Claims.Outage

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable (p : Params)

-- Each supplier has the same binders and conclusion as its reviewed projection.
variable
    (hstore : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RStore p c E rho)
    (hframe : ∀ {In V : Type} [DecidableEq V] (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)), RFrameExact p c E rho)
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
    (hleases : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i v, i ≤ timeIdx rho pt.b₀ → v ∈ rho.honest →
        let st := storeAt p c E rho i v
        let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
        below (F_at p c E rho i v) ∧ below (J_at p c E rho i v) ∧
        below (S_at p c E rho i v) ∧
        (∀ row ∈ st.base.obligations, below row.1 ∧
          ∃ j < i, ∃ s B, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
        (∀ s C, GridCO.savedGenuine st.base s = some (some C) → below C ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gateResultAt p c E rho j = some (some C)) ∧
        (∀ j s C, j < i → IsGateTick p c rho j v s →
          gateResultAt p c E rho j = some (some C) →
          GridCO.savedGenuine st.base s = some (some C)) ∧
        (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] → below X ∧
          ∃ j < i, IsGateTick p c rho j v s ∧ gatePassedAt p c E rho j ∧
            ∃ C, gateResultAt p c E rho j = some (some C) ∧
              Block.Preceq X C ∧ fastAt p c E rho v s X) ∧
        (S_at p c E rho i v = .genesis ∨
          (∃ j < i, ∃ s, IsGateTick p c rho j v s ∧
            gateResultAt p c E rho j = some (some (S_at p c E rho i v))) ∨
          (∃ j ≤ i, S_at p c E rho i v = F_at p c E rho j v)))
    (hrows : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : PtB₀),
      CleanCutPrem p c E rho pt ΔF →
      ∀ i j x r a e, i ≤ timeIdx rho pt.b₀ → j < i → HonestRowAt p c E rho j x r a →
        namedEntry a.payload.height_pair = some e →
        ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
          BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))

include hstore hframe hsrc hordered hnonempty htransfer hleases hrows

/-- Blueprint 03 §4; DC available/stableIncludedFast: INTENTIONAL exact HEAD.
The supplier projections restore the frozen claim, including sleep silence. -/
theorem outage_exactProposalClaim_of : ExactProposalClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hv : 0 < SA.voteTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hv.trans_le h.hhor)
  have hs := hsrc c E rho () ⟨h.set.pre.base, hq⟩
  have ho := hordered c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hn := hnonempty c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have ht := htransfer c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hl := hleases c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hr := hrows c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  exact ⟨inclusion_exact_receipt E rho ΔF h.set (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor,
    inclusion_exact_head E rho ΔF h.set (hstore c E rho) (hframe c E rho)
      hs ho hn ht hbelow hr pt h.prop h.hhor,
    inclusion_sleep_silence E rho pt.s⟩

variable
    (hmono : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {ΔF : Time} (pt : Unit),
      CleanPrem p c E rho pt ΔF →
      MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length))

include hmono

/-- Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL post-gate event read.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionPostGateClaim_of : CleanInclusionPostGateClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  have hs := hsrc c E rho () ⟨h.set.pre.base, hq⟩
  have ho := hordered c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hn := hnonempty c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have ht := htransfer c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hl := hleases c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hr := hrows c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  exact clean_inclusion_post_gate_body E rho ΔF h.set (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor (hmono c E rho () ⟨h.set⟩)

/-- Blueprint 03 §5; DC available/stableIncludedFast: INTENTIONAL inclusive public reads.
The supplier projections restore the frozen claim at the finite Clean horizon. -/
theorem outage_cleanInclusionClaim_of : CleanInclusionClaim p := by
  intro V _ _ In c E rho pt ΔF h
  have hg : 0 < SA.gateTime p.toParams pt.s := by
    change 0 < 4 * p.Δ * (pt.s : Time) + 6 * p.Δ
    have hd := p.deltaPos
    positivity
  have hq := h.set.pre.toCleanCut.faultQ_of_pos (hg.trans_le h.hhor)
  have hs := hsrc c E rho () ⟨h.set.pre.base, hq⟩
  have ho := hordered c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hn := hnonempty c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have ht := htransfer c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hl := hleases c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hr := hrows c E rho (ΔF := ΔF) ⟨rho.horizon⟩ ⟨h.set.pre.toCleanCut⟩
  have hbelow : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1 :=
    fun i v hi hv row hrow => ((hl i v hi hv).2.2.2.1 row hrow).1
  exact clean_inclusion_body E rho ΔF h.set (hstore c E rho) (hframe c E rho)
    hs ho hn ht hbelow hr pt h.prop h.hhor (hmono c E rho () ⟨h.set⟩)

end AvailableChain.FGSA.Run
end
