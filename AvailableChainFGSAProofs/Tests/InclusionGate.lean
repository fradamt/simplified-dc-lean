module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Run.Tests.InclusionGate

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

section Fields

variable
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hstore : RStore p c E rho) (hframe : RFrameExact p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hstrat : RStrat p c E rho)
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
    (hmono : Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length))

include hset hstore hframe hsrc hordered hnonempty htransfer hleases hrows hprop hhor hmono

-- G6 accepts exactly the inherited fields plus gate horizon and hmono.
example :
    Gen.Pure.ServedOn (· ∈ rho.honest) (S_at p c E rho) pt.P
      (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
    Gen.Pure.MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length) :=
  clean_inclusion_post_gate_body (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hmono

-- G7 keeps both getters and every read in the closed interval.
example :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      Gen.Pure.ServedOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) pt.P
        (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon) :=
  clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hmono

-- The last gate tick is included when d equals the horizon.
example (hd : SA.gateTime p.toParams pt.s = rho.horizon) {x : V} (hx : x ∈ rho.honest) :
    ∃ i, IsGateTick p c rho i x pt.s ∧ gatePassedAt p c E rho i ∧
      S_at p c E rho (i + 1) x = pt.P := by
  have he : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    change ((4 * pt.s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hset.pre.base.valid.toScheduleWellFormed
    hset.pre.base.delta x hx (4 * pt.s + 6) (he ▸ hd.le)
  rw [he] at hi
  have hg := inclusion_gate_exact (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hd.le hx hi
  exact ⟨i, hi, hg.2.2.1, hg.2.2.2⟩

-- s = 1 uses transfer at label 0. Its older-label branch is empty.
example (hfirst : pt.s = 1) {x : V} (hx : x ∈ rho.honest) :
    ∀ B, (0, B) ∈ cleanResults p c E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams pt.s)) → Block.Preceq B pt.P := by
  have hh := inclusion_headAtLabel (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor
  exact inclusion_prior_results_below E rho hset.pre.base.valid.toScheduleWellFormed
    hset.pre.base.delta hordered hnonempty htransfer pt.s pt.P (hfirst ▸ Nat.one_pos)
    hhor hh hx 0

-- A sleeping receiver reads P at v and has S = P after its gate tick.
example {x : V} (hx : x ∈ rho.honest)
    (_hv : E.awake x (SA.voteTime p.toParams pt.s) = false)
    (_hd : E.awake x (SA.gateTime p.toParams pt.s) = false)
    {i : Nat} (hi : IsGateTick p c rho i x pt.s) :
    headAtLabel p c E rho x pt.s = some pt.P ∧ S_at p c E rho (i + 1) x = pt.P := by
  exact ⟨inclusion_headAtLabel (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor x hx,
    (inclusion_gate_exact (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
      htransfer hleases hrows pt hprop hhor hx hi).2.2.2⟩

-- At d, the inclusive read crosses same-time deliveries by the supplied hmono.
example {x y : V} (hx : x ∈ rho.honest) (o : Obj p) {j : Nat}
    (hd : rho.events[j]? = some (.deliver y o (SA.gateTime p.toParams pt.s))) :
    cutPred (P := fgsa p c) (SA.gateTime p.toParams pt.s)
      (.deliver y o (SA.gateTime p.toParams pt.s)) = false ∧
      (.deliver y o (SA.gateTime p.toParams pt.s) : V2.Event V (Obj p)) ∈
        rho.events.filter (fun e => decide (e.time ≤ SA.gateTime p.toParams pt.s)) ∧
      Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).confirmed x
        (SA.gateTime p.toParams pt.s)) := by
  refine ⟨?_, List.mem_filter.mpr ⟨List.mem_of_getElem? hd, by simp [V2.Event.time]⟩, ?_⟩
  · simp [cutPred, V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.toLex_le_toLex]
  · exact clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
      htransfer hleases hrows pt hprop hhor hmono (fgsaInterface p c).confirmed
      (by simp) _ x ⟨le_rfl, hhor⟩ hx

-- Both getters also work at the last public read, including a sleeping node.
example {x : V} (hx : x ∈ rho.honest) :
    Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).stable x rho.horizon) ∧
      Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).confirmed x rho.horizon) := by
  have hi := clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hmono
  exact ⟨hi _ (by simp) _ x ⟨hhor, le_rfl⟩ hx, hi _ (by simp) _ x ⟨hhor, le_rfl⟩ hx⟩

end Fields

/- Full execution fixtures are not supplied here. The following tests need
such fixtures: n = 5, a = 1, h_v = 2 below the fast threshold; s = 1 with
both lease tests failing; Byzantine late-only votes and equivocation; several
honest gate ticks plus a delivery at d; later finalization, expiry and release;
a gate after the horizon; and a run with DeltaF greater than Delta.
The examples above check theorem instantiation and event-cut boundaries.
They do not claim these full execution tests. -/

end AvailableChain.FGSA.Run.Tests.InclusionGate
end
