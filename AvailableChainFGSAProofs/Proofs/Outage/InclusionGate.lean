module
public import AvailableChainFGSARun.Proofs.ReadFacts
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 03:350–417 (§4 exact adoption), 03:418–458 (§5); plan I-GATE, G1.
Class (iii).
DC: INTENTIONAL; the exact strict read is a scheduled HEAD read for every
honest node. The tick does not need an awake node. -/
theorem inclusion_headAtLabel [Fintype V]
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
    (hstrat : RStrat p c E rho) :
    ∀ y ∈ rho.honest, headAtLabel p c E rho y pt.s = some pt.P := by
  have hs := hset.pre.base.valid.toScheduleWellFormed
  have hv := (fgsa_vote_lt_gate p pt.s).le.trans hhor
  have hhead := inclusion_exact_head (hstrat := hstrat) E rho ΔF hset hstore hframe hsrc hordered
    hnonempty
    htransfer hleases hrows pt hprop hv
  intro y hy
  have he : ((4 * pt.s + 1 : Nat) : Time) * p.Δ = SA.voteTime p.toParams pt.s := by
    change ((4 * pt.s + 1 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hset.pre.base.delta y hy
    (4 * pt.s + 1) (he ▸ hv)
  rw [he] at hi
  change (postClock E rho y (SA.voteTime p.toParams pt.s)).map _ = _
  rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hi]
  simp only [Option.map_some]
  rw [fgsa_preTick_eq_timeRead E rho hs hset.pre.base.noRestart hi, hhead y hy]

/-- Blueprint 03:418–458; plan I-GATE, G2. Class (iii).
DC: INTENTIONAL; transfer at s minus one bounds its raw results by P.
Ordering bounds all older results. At s = 1 there is no older label. -/
theorem inclusion_prior_results_below
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hDelta : E.Δ = p.Δ)
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
    (s : Slot) (P : Block) (hpos : 0 < s)
    (hhor : SA.gateTime p.toParams s ≤ rho.horizon)
    (hhead : ∀ y ∈ rho.honest, headAtLabel p c E rho y s = some P)
    {y : V} (hy : y ∈ rho.honest) :
    ∀ r B, (r, B) ∈ cleanResults p c E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams s)) → Block.Preceq B P := by
  have hprev : (s - 1 : Nat) + 1 = s := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  have hgh : SA.gateTime p.toParams (s - 1) ≤ rho.horizon := by
    refine le_trans ?_ hhor
    change 4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ ≤
      4 * p.Δ * (s : Int) + 6 * p.Δ
    have hsle : ((s - 1 : Nat) : Int) ≤ (s : Int) := by exact_mod_cast Nat.sub_le s 1
    nlinarith [p.deltaPos]
  have hvh : vHead p c E rho y (s - 1) = some P := by
    rw [vHead_def, hprev]
    exact hhead y hy
  intro r B hB
  obtain ⟨j, hj, x, ht, hB⟩ := hB
  have htime := (Gen.V2.Duty.index_lt_idxBefore_iff hs ht _).mp hj
  have hrs : r < s := by
    change 4 * p.Δ * (r : Int) + 6 * p.Δ < 4 * p.Δ * (s : Int) + 6 * p.Δ at htime
    have hr : (r : Int) < (s : Int) := by nlinarith [p.deltaPos]
    exact_mod_cast hr
  have hx := hs.honest_only _ (List.mem_of_getElem? ht)
  have hgr : gateResult p c E rho x r = some (some B) :=
    (gateResultAt_eq_gateResult p c E rho hs ht) ▸ hB
  have hgrhor := htime.le.trans hhor
  by_cases heq : r = s - 1
  · subst r
    exact htransfer x y (s - 1) B P hx hy hgh hgr hvh
  · have hlt : r < s - 1 := by
      simp only [Slot] at hrs heq ⊢
      omega
    have he : ((4 * (s - 1) + 6 : Nat) : Time) * p.Δ =
        SA.gateTime p.toParams (s - 1) := by
      change ((4 * (s - 1) + 6 : Nat) : Int) * p.Δ =
        4 * p.Δ * ((s - 1 : Nat) : Int) + 6 * p.Δ
      push_cast
      ring
    obtain ⟨j0, hj0, _⟩ := fgsa_tick_total E rho hs hDelta y hy
      (4 * (s - 1) + 6) (he ▸ hgh)
    rw [he] at hj0
    obtain ⟨C, hC, _⟩ := hnonempty j0 y (s - 1)
      ((V2.D.Engine.index_lt_read_length_iff hs rho.horizon hj0).mpr hgh) hy hj0
    have hC' : gateResult p c E rho y (s - 1) = some (some C) :=
      (gateResultAt_eq_gateResult p c E rho hs hj0) ▸ hC
    exact block_preceq_trans ((hordered x y r (s - 1) B C hx hy hgrhor hgh hgr hC').1 hlt)
      (htransfer y y (s - 1) C P hy hy hgh hC' hvh)

end AvailableChain.FGSA.Run
end
