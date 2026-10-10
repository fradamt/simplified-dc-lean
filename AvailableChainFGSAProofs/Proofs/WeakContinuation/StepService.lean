module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Epoch
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepInit -- shake: keep (WC init API)
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Safety
public import AvailableChainFGSARun.Proofs.AC

public section

/-! WC plan §6.6; DC finite service follows the proved joint history. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.6; DC a completed guard writes its result into the local output. -/
private theorem gate_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x) := by
  obtain ⟨C, hC, _, hpass⟩ := hi.nonempty j x s hr.afterCut hr.completed
    hr.honest (hr.enabled hsch) hr.label
  have hrawAt : gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
    rw [gateResultAt_eq_gateResult p c E rho hsch hr.event,
      gateResult_eq_saved p c E rho hsch hr.event, clockPre_fg]
    exact fgsa_gate_saved_result E rho hsch hr.event
      (fgsa_gate_joined_of_enabled E rho (hr.enabled hsch))
  have hraw := Option.some.inj (hrawAt.symm.trans hr.value)
  obtain ⟨y, r, he, _, G, hG, hguard⟩ := hpass
  have hevent := V2.Event.tick.inj (Option.some.inj (he.symm.trans hr.event))
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
  have hc := wc_result_output_compatible hi hr hr.afterCut (Nat.le_of_lt hr.completed)
    hr.honest
  have hadv : Block.Preceq (S_at p c E rho j x) (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · exact block_preceq_refl _
    · next hn =>
      rcases Bool.or_eq_true_iff.mp hc with h | h
      · exact h
      · exact (hn h).elim
  have hb : Block.Preceq B (GridCO.advance (S_at p c E rho j x) B) := by
    unfold GridCO.advance
    split
    · assumption
    · exact block_preceq_refl _
  rcases (fgsaAC_gate_write E rho j s x
    (wc_gate_pre_joined (hr.enabled hsch)) hr.event).effects with hskip | hrun
  · obtain ⟨result, hsaved⟩ := hskip.1
    have hfresh := fgsa_gate_fresh E rho hsch hr.event
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
    rwa [hw, Gen.AC.normalizeOutput_def, ite_eq_left hn]

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.6; DC finite service needs only history through the requested read. -/
theorem wc_service4_prefix :
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
  WCSeed p c E rho w iStar → ∀ n, WCInv p c E rho w iStar n →
    ∀ j x s B, WCResult p c E rho w iStar n j x s B →
    SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
    ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i → i ≤ n →
      y ∈ rho.honest → Block.Preceq B (S_at p c E rho i y) := by
  intro hvalid _hlinked _hcstar _hnr hdelta _hroots _hsync _hdeltaF _hfault _hfaultQ
    _hfaultX _hpart _hstore _hcumul _hmono _hactive _hframe _hmeta _hrec _hgeo _hcert
    _hsrc _hlabel _hqc _hstrat _hnoslash _hemitted _htargets _hlease _hfast _hdeadlines
    _hheldRows _hscopeRows _hfinalHead _hs n inv j x s B hr hhor i y hcut hin hy
  have hsch := hvalid.toScheduleWellFormed
  have hi := inv
  have hj := hr.afterCut
  have ht := hr.event
  have hlabel := hr.label
  have hnext : SA.gateTime p.toParams (s + 1) = SA.gateTime p.toParams s + 4 * p.Δ := by
    change 4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ =
      (4 * p.Δ * (s : Int) + 6 * p.Δ) + 4 * p.Δ
    push_cast
    ring
  have hclock : ((4 * (s + 1) + 6 : Nat) : Time) * p.Δ =
      SA.gateTime p.toParams (s + 1) := by
    change ((4 * (s + 1) + 6 : Nat) : Int) * p.Δ =
      4 * p.Δ * ((s + 1 : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hsch hdelta y hy (4 * (s + 1) + 6)
    (by rw [hclock, hnext]; exact hhor)
  rw [hclock] at hk
  have hjk : j < k := V2.D.Engine.eventIndex_lt_of_time_lt hsch ht hk
    (by
      change SA.gateTime p.toParams s < SA.gateTime p.toParams (s + 1)
      rw [hnext]
      exact lt_add_of_pos_right _ (by linarith [p.deltaPos]))
  have hkc : k < afterTicksIdx rho (SA.gateTime p.toParams (s + 1)) := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hsch
      (cutPred (SA.gateTime p.toParams (s + 1))) (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hk
    have hc : cutPred (SA.gateTime p.toParams (s + 1))
        (.tick y (SA.gateTime p.toParams (s + 1)) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true le_rfl
    rw [hc] at hf
    cases hf
  have hki : k + 1 ≤ i := (Nat.succ_le_of_lt hkc).trans (hnext ▸ hcut)
  have hklen : k < n := (Nat.lt_succ_self k).trans_le (hki.trans hin)
  have hik : iStar ≤ k := hj.trans (Nat.le_of_lt hjk)
  obtain ⟨C, hC, _, _⟩ :=
    hi.nonempty k y (s + 1) hik hklen hy hk (hlabel.trans (Nat.lt_succ_self s))
  have hrC : WCResult p c E rho w iStar n k y (s + 1) C :=
    ⟨hy, hik, hklen, hlabel.trans (Nat.lt_succ_self s), hk, hC⟩
  have hBC := hi.ordered j k x y s (s + 1) B C hr hrC (Nat.lt_succ_self s)
  have hCout := gate_served hsch hi hrC
  have mono : ∀ l, k + 1 ≤ l → l ≤ n →
      Block.Preceq (S_at p c E rho (k + 1) y) (S_at p c E rho l y) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => intro _; exact block_preceq_refl _
    | succ l hkl ih =>
      intro hln
      exact block_preceq_trans (ih (by omega))
        (hi.transitions l y (hik.trans (by omega)) (by omega) hy)
  exact block_preceq_trans hBC (block_preceq_trans hCout (mono i hki hin))

/-- WC plan §6.6; DC the next covered gate serves the result at every honest reader. -/
theorem wc_service4 : WCService4Statement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs hinv j x s B hx hj ht hlabel' hB hhor i y hcut hilen hy
  exact wc_service4_prefix hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs rho.events.length (hinv rho.events.length ⟨hs.within, le_rfl⟩)
    j x s B ⟨hx, hj, (List.getElem?_eq_some_iff.mp ht).1, hlabel', ht, hB⟩
    hhor i y hcut hilen hy

end AvailableChain.FGSA.Run
end
