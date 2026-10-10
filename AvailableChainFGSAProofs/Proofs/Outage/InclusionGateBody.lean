module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateService
public import AvailableChainGeneric.Statements.Pure.Props

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 03:418–458; S3a Q12:3454; plan I-GATE, G6. Class (iii).
DC: INTENTIONAL; this is the unfolded InclusionPostGateAt body.
The event-prefix monotonicity conjunct has the approved confirmed-reader scope. -/
theorem clean_inclusion_post_gate_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hmono : ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
      (· ≤ rho.events.length))
    (hScopes : ∀ i x, x ∈ rho.honest →
      enabledGateAt p c E rho i x pt.s ∨
        confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams pt.s))
          (SA.gateTime p.toParams pt.s) →
      IsGateTick p c rho i x pt.s → GateReceiptScope E rho i x pt.s)
    (hstrat : RStrat p c E rho) :
    ScopedServed (fun x i => confirmedReaderAtIdx p c E rho x i
      (SA.gateTime p.toParams pt.s)) (S_at p c E rho) pt.P
      (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
    ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
      (· ≤ rho.events.length) := by
  refine ⟨?_, hmono⟩
  intro k x hk hx
  subst k
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have he : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    change ((4 * pt.s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hset.pre.base.delta x hx.1
    (4 * pt.s + 6) (he ▸ hhor) (he ▸ hx.2.1)
  rw [he] at hi
  have hout := (inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered
    hnonempty
    htransfer hleases hrows pt hprop hhor hx.1
    (hScopes i x hx.1 (Or.inr hx) hi)).2.2.2
  have hnode := (afterTicks_node E rho hs hi).trans (V2.D.Run.step_tick_eq E rho hi).1.symm
  rw [afterTicks_eq_stateBefore E rho hs] at hnode
  have hS := congrArg (fun nd : Node p => nd.st.base.stableRecord) hnode
  change Block.Preceq pt.P (S_at p c E rho (afterTicksIdx rho _) x)
  rw [show S_at p c E rho (afterTicksIdx rho _) x = S_at p c E rho (i + 1) x from
    by rw [S_at_def, S_at_def]; exact hS, hout]
  exact block_preceq_refl _

/-- ROOT-DIGEST W2b. Blueprint 03:418–458; S3a Q12:3454; plan I-READ, G7. Class (iii).
DC: INTENTIONAL; the later-read supplier gives an actual enabled gate origin
at or after the inclusion label. Ordering gives inclusion at the public read.
The origin supplier remains owned work; it is not a public claim premise. -/
theorem clean_inclusion_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hScopes : ∀ i x, x ∈ rho.honest →
      enabledGateAt p c E rho i x pt.s ∨
        confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams pt.s))
          (SA.gateTime p.toParams pt.s) →
      IsGateTick p c rho i x pt.s → GateReceiptScope E rho i x pt.s)
    (hOrigins : ∀ t x, SA.gateTime p.toParams pt.s ≤ t → t ≤ rho.horizon →
      confirmedReader p c E rho x t →
      ∃ q i B, pt.s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
        enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x))
    (hstrat : RStrat p c E rho) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
        (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon) := by
  have hs := hset.pre.base.valid.toScheduleWellFormed
  obtain ⟨z, hz, _, _, j, hG⟩ := inclusion_joined_gate_witness E rho hset pt.s hhor
  have hExact := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hz
    (hScopes j z hz (Or.inl hG) hG.1)
  intro g hg t x ht hx
  obtain ⟨q, i, B, hsq, hqt, hGX, hB, hBS⟩ := hOrigins t x ht.1 ht.2 hx
  have hBR : gateResult p c E rho x q = some (some B) :=
    (gateResultAt_eq_gateResult p c E rho hs hGX.1) ▸ hB
  have hPB : Block.Preceq pt.P B := by
    rcases hsq.lt_or_eq with hlt | rfl
    · exact (hordered z x pt.s q pt.P B hz hx.1 hhor (hqt.trans ht.2)
        hExact.1 hBR).1 hlt
    · have hX := inclusion_gate_exact (hstrat := hstrat) E rho ΔF hset hInputs hHistory
        hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor hx.1
        (hScopes i x hx.1 (Or.inl hGX) hGX.1)
      have he := Option.some.inj (Option.some.inj (hBR.symm.trans hX.1))
      rw [he]
      exact block_preceq_refl _
  have hread : V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact block_preceq_trans hPB hBS

end AvailableChain.FGSA.Run
end
