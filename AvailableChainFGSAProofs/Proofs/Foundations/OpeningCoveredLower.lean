module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission
public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- SO-COV for the lower source at its exact-service gate, blueprint
21 H.7 / H.9 and spec client 1600–1630, 1672–1679. In an uncontested
phase the live floor is m - 1. ExactService supplies the actual source,
and IF.3(b) plus send-once history supplies a complete matching row.
These are the lower-height and uncontested branches of TCommon at q = rR.
DC: INTENTIONAL W source and exact-service contract; no fresh emission
or caller-supplied client permission is assumed. -/
theorem openingCovered_lower_gate (G : Time) (h : HealingPrem p c G E rho ())
    (u : Time) (m : Nat) (J : Option (FGBlock (Fin p.n)))
    (r : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n))
    (hGST : E.t_GST ≤ u) (hQ : eraseFG Qfg = Q)
    (hh : (heightView p Qfg).h = m - 1)
    (hservice : ExactService p c E rho (r * p.R) Q)
    (hu : u ≤ SA.proposalTime p.toParams (r * p.R))
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J false) :
    OpeningCovered p c E rho r Q := by
  have hut : u < p.actionTime r := by
    change u ≤ 4 * p.Δ * ((r * p.R : Nat) : Time) at hu
    change u < 4 * p.Δ * ((r * p.R : Nat) : Time) + 6 * p.Δ
    have := p.deltaPos
    linarith
  intro x hx
  have hs := (hservice.2 hphase.2.1 x hx).2.2.2.2 r rfl
  change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = some (some Q) at hs
  obtain ⟨src, hsrc, he⟩ := Option.map_eq_some_iff.mp hs
  obtain ⟨K, hKsrc, hKe⟩ := Option.map_eq_some_iff.mp he
  subst src
  have hKQ : K = Qfg := eraseFG_injective (hKe.trans hQ.symm)
  subst K
  rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hsrc; contradiction
  | some i =>
    have ht := V2.D.Run.tickIdx?_spec hi
    let nd := (fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)
    have hnd : postClock E rho x (p.actionTime r) = some nd := by
      rw [postClock_def, preTick_def, hi]; rfl
    have hsel : FGSA.fgSource p nd.st = some Qfg := by
      simpa only [hi, Option.map_some, Option.some.injEq] using hsrc
    have hread : actionSourceFG p c E rho x r = some (some Qfg) := by
      rw [actionSourceFG_def, hnd]; exact congrArg some hsel
    have hd : Qfg ∈ FGSA.fullTree p nd.st := by
      rw [fgSource_eq_jointSource] at hsel
      have hm := (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hsel).1).1
      rw [fullTree_eq]
      simpa only [domainR_eq_storeFrame, treeT_def] using hm
    have hil : timeIdx rho u ≤ i := by
      apply Nat.le_of_not_gt
      intro hil
      have hb := (V2.D.Engine.index_lt_read_length_iff
        h.set.base.valid.toScheduleWellFormed u ht).mp hil
      exact (not_le_of_gt hut) hb
    have hih : i ≤ timeIdx rho (p.actionTime r) :=
      Nat.le_of_lt ((V2.D.Engine.index_lt_read_length_iff
        h.set.base.valid.toScheduleWellFormed (p.actionTime r) ht).mpr le_rfl)
    have hlocal := hphase.2.2.2 i x hil hih hx
    have hH := hlocal.1
    have hH' : (FGSA.controls p nd.st).H = m := by
      change (FGSA.clock p _ _).fg.h_max = m
      rw [FGSA.clock_fg]
      exact hH
    have hlo : (FGSA.controls p nd.st).lo ≤ hOf p.E p.cfg Qfg := by
      rw [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p), hh]
      have hcontest : (FGSA.controls p nd.st).contest = false := by
        change (FGSA.controls p (FGSA.clock p _ _)).contest = false
        rw [FGSA.controls_eq, FGSA.clock_fg]
        rw [← FGSA.controls_eq]
        exact hlocal.2.1
      change (if (FGSA.controls p nd.st).contest then _ else _) ≤ m - 1
      rw [hcontest, hH']
      exact le_rfl
    obtain ⟨j, rSent, a, hr, ha, hn⟩ := rowPermission_covered E rho h.set.base h.set.fault
      x hx r nd hnd Qfg hread hd hlo (h.set.awake x hx _ (hGST.trans hut.le) hphase.2.1)
    exact ⟨Qfg, nd, j, rSent, a, hnd, hread, hd, hQ ▸ Gen.Pure.block_preceq_refl _, hr, ha, hn⟩
end AvailableChain.FGSA.Run
