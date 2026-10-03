module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateService
public import AvailableChainGeneric.Statements.Pure.Props

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 03:418–458; S3a Q12:3454; plan I-GATE, G6. Class (iii).
DC: INTENTIONAL; this is the unfolded InclusionPostGateAt body.
The event-prefix monotonicity conjunct is the supplied hmono field. -/
theorem clean_inclusion_post_gate_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
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
    (hmono : Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length)) :
    Gen.Pure.ServedOn (· ∈ rho.honest) (S_at p c E rho) pt.P
      (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
    Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) := by
  refine ⟨?_, hmono⟩
  intro k x hk hx
  subst k
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have he : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    change ((4 * pt.s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hset.pre.base.delta x hx
    (4 * pt.s + 6) (he ▸ hhor)
  rw [he] at hi
  have hout := (inclusion_gate_exact E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hx hi).2.2.2
  have hnode := (afterTicks_node E rho hs hi).trans (V2.D.Run.step_tick_eq E rho hi).1.symm
  rw [afterTicks_eq_stateBefore E rho hs] at hnode
  have hS := congrArg (fun nd : Node p => nd.st.base.stableRecord) hnode
  change Block.Preceq pt.P (S_at p c E rho (afterTicksIdx rho _) x)
  rw [show S_at p c E rho (afterTicksIdx rho _) x = S_at p c E rho (i + 1) x from
    by rw [S_at_def, S_at_def]; exact hS, hout]
  exact block_preceq_refl _

/-- Blueprint 03:418–458; S3a Q12:3454; plan I-READ, G7. Class (iii).
DC: INTENTIONAL; this is the unfolded InclusionAt body. The inclusive
public read uses hmono after the tick cut, including deliveries at d.
Both getters read S. All read times are within the finite horizon. -/
theorem clean_inclusion_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      IsGateTick p c rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
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
    (hmono : Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length)) :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.ServedOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) pt.P
        (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon) := by
  have hpost := clean_inclusion_post_gate_body E rho ΔF hset hstore hframe hsrc hordered
    hnonempty htransfer hleases hrows pt hprop hhor hmono
  have hs := hset.pre.base.valid.toScheduleWellFormed
  intro g hg t x ht hx
  have hij : afterTicksIdx rho (SA.gateTime p.toParams pt.s) ≤ timeIdx rho t :=
    (preIdx_le_afterTicksIdx E rho hs _).2.trans (V2.D.Engine.read_length_mono _ _ ht.1)
  have hkN : afterTicksIdx rho (SA.gateTime p.toParams pt.s) ≤ rho.events.length :=
    List.length_filter_le _ _
  have hjN : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
  have hb := hpost.1 (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) x rfl hx
  have hm := hmono _ _ x hkN hjN hij hx
  have hread : V2.D.outputAt E rho g x t = S_at p c E rho (timeIdx rho t) x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;>
      change (V2.D.Run.readAt E rho t x).st.base.stableRecord = _ <;>
      rw [S_at_def, V2.D.Engine.readAt_eq_stateBefore hs t] <;> rfl
  change Block.Preceq pt.P (V2.D.outputAt E rho g x t)
  rw [hread]
  exact block_preceq_trans hb hm

end AvailableChain.FGSA.Run
end
