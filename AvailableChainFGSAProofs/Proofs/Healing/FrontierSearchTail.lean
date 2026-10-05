module
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierSearchStop
public import AvailableChainFGSAProofs.Proofs.Healing.FrontierService
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts

public section

/-! Blueprint 21 HG.4:1698--1720; frontier plan §3.3.
The row tail uses HG.1 across same-frontier events. A rise supplies an
earlier row through RCap. This module does not assert the terminal rise tail.
INLINE writes: fgsa_leaseOrigins_lastWrite (Foundations/Leases).
INLINE rowCoverage: rowPermission_covered (Foundations/RowPermission). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 HG.4 and IF.3(a); frontier plan §3.3/§4.
DC: SAME first honest height-m row within P-4Δ of the saved seed.
The closed horizon includes equality. No phase through this endpoint is assumed. -/
theorem healing_frontierTail_row [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho) (cap : RCap p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (rowCoverage : ∀ x, x ∈ rho.honest → ∀ r nd,
      postClock E rho x (p.actionTime r) = some nd → ∀ C,
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st →
      (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))
    {m : Nat} {t : Time} (hserved : StrongServed p c E rho m t)
    (hhor : t + (P p - 4 * p.Δ) ≤ rho.horizon) :
    FirstHeightRowBy p c E rho m (t + (P p - 4 * p.Δ)) := by
  classical
  obtain ⟨u, J, contested, q, Q, Qfg, hgst, hQ, hErase, hHeight, hService,
    hseed, hu, hphase, hqt, _, _⟩ := (strongServed_iff p c E rho m t).mp hserved
  let D := t + (P p - 4 * p.Δ)
  have hm : 1 ≤ m := hphase.2.2.1
  have hs := hrec.base.valid.toScheduleWellFormed
  have hP : 0 ≤ P p := by
    change 0 ≤ 4 * (p.R : Time) * p.Δ
    have hd := p.deltaPos
    positivity
  by_cases hhigh : ∃ x, x ∈ rho.honest ∧
      m < (storeAt p c E rho (timeIdx rho D) x).fg.h_max
  · obtain ⟨x, hx, hh⟩ := hhigh
    obtain ⟨W, hW, hWh⟩ := healing_phase_frontier_witness p c E rho (timeIdx rho D) x
    obtain ⟨j, z, r, a, e, hj, hr, hn, _⟩ := cap (m - 1) (timeIdx rho D) x W
      ⟨hx, hW⟩ (by simp only [Height] at *; omega)
    have hn' : namedEntry a.payload.height_pair = some (m, e) := by
      simpa only [Nat.sub_add_cancel hm] using hn
    exact frontierSearch_first_row p c E rho ⟨j, z, a, e, hr, hn'⟩
      (frontierSearch_event_time_le p c E rho hs hr.2.1 hj)
  · have hcap (i : Nat) (x : V) (hi : i ≤ timeIdx rho D) (hx : x ∈ rho.honest) :
        (storeAt p c E rho i x).fg.h_max ≤ m := by
      have hfront : frontierAtIdx p c E rho (timeIdx rho D) ≤ m :=
        Finset.sup_le (fun y hy => le_of_not_gt (fun hh => hhigh ⟨y, hy, hh⟩))
      exact (healing_phase_local_le_frontier p c E rho hx).trans
        ((healing_frontier_mono p c E rho hrec.base.noRestart hi).trans hfront)
    have hex : ∃ r, q ≤ r * p.R := by
      refine ⟨q, ?_⟩
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left q (show 1 ≤ p.R by have := p.RLarge; omega)
    let r := Nat.find hex
    have hqr : q ≤ r * p.R := Nat.find_spec hex
    have hfirst : ∀ r', q ≤ r' * p.R → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
    obtain ⟨hlo, hhi⟩ := common_first_time_bound (p := p) q r hqr hfirst
    have har : p.actionTime r ≤ D := by dsimp only [D]; linarith
    have hqD : SA.gateTime p.toParams q ≤ D := by linarith
    have hf := frontier_service E rho hrec mono crossing writes rowCoverage
      u D m J contested q Q Qfg hgst hQ hErase hHeight hService
      ((frontierSeedQualification_iff p E u q).mp hseed) hu hphase hqD hhor
      (fun i x _ hi hx => hcap i x hi hx)
    obtain ⟨hc, ⟨e, he⟩, _⟩ := hf.2.2 r hqr har
    let x := V2.D.proposerOf rho (fgsaInterface p c) q
    have hx : x ∈ rho.honest := hQ.1.2
    obtain ⟨K, nd, j, rSent, a, _, hK, _, _, hrs, hr, hn⟩ := hc x hx
    have hKh := (he x K hx hK).1
    rw [hKh] at hn
    have hrow : HeightRow p c E rho rSent m := ⟨j, x, a, _, hr, hn⟩
    apply frontierSearch_first_row p c E rho hrow
    have hrsI : (rSent : Time) ≤ r := by exact_mod_cast hrs
    have hat : p.actionTime rSent ≤ p.actionTime r := by
      rw [actionTime_periodW, actionTime_periodW]
      have hmul := mul_le_mul_of_nonneg_right hrsI hP
      linarith only [hmul]
    exact hat.trans har

end AvailableChain.FGSA.Run
end
