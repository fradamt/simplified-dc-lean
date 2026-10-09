module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepGateHistory
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepReconcile
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepFacts

public section

/-! WC plan §6.5; DC the ordered handler cases preserve and identify the output. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC plan §6.5; DC a fresh accepted gate normalizes an already compatible output. -/
private theorem gate_output {j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j x s)
    (hB : gateResultAt p c E rho j = some (some B)) (hpass : gatePassedAt p c E rho j)
    (hcompat : Block.Compatible (S_at p c E rho j x) B) :
    S_at p c E rho (j + 1) x = GridCO.advance (S_at p c E rho j x) B ∧
      Block.Preceq (S_at p c E rho j x) (S_at p c E rho (j + 1) x) := by
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch ht,
      gateResult_eq_saved p c E rho hsch ht, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch ht
  have hraw := Option.some.inj (hrawAt.symm.trans hB)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.symm.trans ht))
  have hlabel : r = s := by
    have ht := hevent.2
    change 4 * p.Δ * (r : Int) + 6 * p.Δ = 4 * p.Δ * (s : Int) + 6 * p.Δ at ht
    have hcast : (r : Int) = s := by nlinarith [p.deltaPos]
    exact Int.ofNat_inj.mp hcast
  have hxy := hevent.1
  subst y
  subst r
  have heq : G = B := Option.some.inj (hG.symm.trans hraw)
  subst G
  have hview := fgsa_clockPre_gateView p (storeAt p c E rho j x) s
  have hraw' : (fgsaAC E rho).raw j s x = some B := by
    rw [clockPre_fg] at hraw
    have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F) v s) hview
    exact he.symm.trans hraw
  have hguard' : ∀ lease ∈ ((fgsaAC E rho).gateView j x s).obligations,
      Block.Compatible (Gen.AC.Lease.target lease) B := by
    intro lease hm
    have he : (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).base.obligations =
        ((fgsaAC E rho).gateView j x s).obligations := by
      have he' := congrArg GridCO.State.obligations hview
      exact he'
    rw [← he] at hm
    have hg := List.any_eq_false.mp hguard lease hm
    simpa only [Gen.AC.Lease.target, Block.Compatible, Bool.not_eq_true',
      Bool.not_eq_false] using hg
  have hc := hcompat
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  rcases (fgsaAC_gate_write E rho j s x ht).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch ht
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = some result at hsaved
    change GridCO.savedGenuine (storeAt p c E rho j x).base s = none at hfresh
    rw [hfresh] at hsaved
    cases hsaved
  · have hw := (hrun.accept B hraw' hguard').1
    change S_at p c E rho (j + 1) x = Gen.AC.normalizeOutput (F_at p c E rho j x)
      (GridCO.advance (S_at p c E rho j x) B) at hw
    have hn : Block.preceq (F_at p c E rho j x)
        (GridCO.advance (S_at p c E rho j x) B) = true :=
      block_preceq_trans (nestOK_stateBefore E rho j x) hadv
    rw [Gen.AC.normalizeOutput_def, ite_eq_left hn] at hw
    exact ⟨hw, hw ▸ hadv⟩

/-- WC plan §6.5; DC expiry, duties, delivery and reconciliation keep S or take this gate. -/
theorem wc_outputStep [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hnr : V2.D.NoRestart rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ s, w.u + 1 ≤ s → SA.voteTime p.toParams s ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card <
      (Gen.V2.Duty.awakeHonest E rho (SA.voteTime p.toParams s)).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreCumul p c E rho)
  (_hmono : RMono p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNext p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar → ∀ i, iStar ≤ i → i < rho.events.length →
    WCInv p c E rho w iStar i → ∀ e, rho.events[i]? = some e →
    ∀ x ∈ rho.honest,
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        ∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv _e _he x hx
  have keep (heq : S_at p c E rho (i + 1) x = S_at p c E rho i x) :
      Block.Preceq (S_at p c E rho i x) (S_at p c E rho (i + 1) x) ∧
      (S_at p c E rho (i + 1) x = S_at p c E rho i x ∨
        ∃ s, IsGateTick p c rho i x s ∧ w.u < s ∧
          gateResultAt p c E rho i = some (some (S_at p c E rho (i + 1) x))) := by
    exact ⟨heq ▸ block_preceq_refl _, Or.inl heq⟩
  rcases fgsaAC_output_step E rho i x with hsame | ⟨s, ht⟩ | hrc | ⟨t, hr, _⟩
  · exact keep hsame
  · have hslabel := (wc_gate_cut_iff hvalid.toScheduleWellFormed hs ht).mp hi
    obtain ⟨B, hB, hpass, _, _, _, hcompat⟩ := wc_gateResult ΔF w iStar hvalid hlinked
      hcstar hnr hdelta hroots hsync hdeltaF
      hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
      hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
      hscopeRows hfinalHead
      hs i x s hi hilen inv ht hslabel
    obtain ⟨heq, hmono⟩ := gate_output hvalid.toScheduleWellFormed ht hB hpass hcompat
    refine ⟨hmono, ?_⟩
    unfold GridCO.advance at heq
    split at heq
    · exact Or.inl heq
    · exact Or.inr ⟨s, ht, hslabel, heq ▸ hB⟩
  · obtain ⟨o, t, B, he, _, _, hout⟩ := hrc
    have hbelow := wc_reconcileBound ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots
      hsync hdeltaF
      hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
      hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
      hscopeRows hfinalHead hs i hi hilen inv x o t he x x hx hx
    change S_at p c E rho (i + 1) x = Gen.AC.normalizeOutput
      (F_at p c E rho (i + 1) x) (S_at p c E rho i x) at hout
    change Block.preceq (F_at p c E rho (i + 1) x) (S_at p c E rho i x) = true at hbelow
    rw [Gen.AC.normalizeOutput_def, ite_eq_left hbelow] at hout
    exact keep hout
  · exact (hnr i x t hr).elim

end AvailableChain.FGSA.Run
end
