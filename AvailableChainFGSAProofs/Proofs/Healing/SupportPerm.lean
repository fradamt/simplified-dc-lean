module
public import AvailableChainFGSAProofs.Proofs.Healing.SupportSlow

public section

/-! H-SUPPORT S4 assembly (plan §6–§7; ruling B31). Both PhaseBody arms give the three
Transfers clauses. The S3 output clause carries the B31 guard d_s + 4Δ ≤ v, so the
result is the frozen TPerm (`healing_tPerm`). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- Blueprint 21:620–715 (H.4, H.4-S, H.2 S1–S3); plan H-SUPPORT §6, ruling B31.
DC: INTENTIONAL the TPerm conclusion for one phase and one body, with the S3 output
clause under the B31 guard d_s + 4Δ ≤ v. -/
theorem healing_phase_transfers [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {s : Slot} {B : Block} (hhead : u ≤ SA.voteTime p.toParams s)
    (hgate : SA.gateTime p.toParams s ≤ v) (hbody : PhaseBody p c E rho s B) :
    (∀ x i H, x ∈ rho.honest → s + 1 ≤ i → SA.voteTime p.toParams i ≤ v →
      headAtLabel p c E rho x i = some H → Block.Preceq B H) ∧
    (∀ i Q, s + 2 ≤ i → SA.proposalTime p.toParams i ≤ v →
      HonestProposal E rho (fgsaInterface p c) i Q → Block.Preceq B Q.parent) ∧
    (∀ i x, x ∈ rho.honest → SA.gateTime p.toParams s + 4 * p.Δ ≤ v →
      afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
      i ≤ timeIdx rho v → Block.Preceq B (S_at p c E rho i x)) := by
  obtain ⟨x, hx, hfast | ⟨hgw, st, C, jx, hst, hres, _, hBC, hel, hjx, _⟩⟩ := hbody
  · obtain ⟨nd, hnd, hB⟩ := hfast
    refine ⟨fun z i H hz hi hv hH => ?_, ?_, fun i z hz hguard => ?_⟩
    · exact healing_fast_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx hnd
        hB i hi hv z hz H hH
    · exact healing_fast_proposals E rho hrec mono crossing writes hgst hphase hhead hgate hx
        hnd hB
    · exact healing_fast_output E rho hrec mono crossing writes hgst hphase hhead hgate hguard
        hx hnd hB i z hz
  · refine ⟨fun z i H hz hi hv hH => ?_, ?_, fun i z hz hguard => ?_⟩
    · exact healing_slow_heads E rho hrec mono crossing writes hgst hphase hhead hgate hx hgw
        hst hres hBC hel hjx i hi hv z hz H hH
    · exact healing_slow_proposals E rho hrec mono crossing writes hgst hphase hhead hgate hx
        hgw hst hres hBC hel hjx
    · exact healing_slow_output E rho hrec mono crossing writes hgst hphase hhead hgate hguard
        hx hgw hst hres hBC hel hjx i z hz

/-- T-PERM, bp.phaseSourcePermanence.v1 (00:962–966; 21 H.4/H.4-S:628–680); plan
H-SUPPORT §6–§7 (S4), ruling B31.
DC: SAME the frozen TPerm with the B31-guarded S3 clause, from `healing_phase_transfers`.
The `writes` premise is the inline last-write structure (ruling B27). -/
theorem healing_tPerm [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          GridCO.savedGenuine pre.base w = none →
          SA.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy p.toParams.engine p.n
            (actView pre) w C) :
    TPerm p c E rho := by
  intro u v m J contested s B hgst hphase hhead hgate hbody
  exact healing_phase_transfers E rho hrec mono crossing writes hgst hphase hhead hgate hbody

end AvailableChain.FGSA.Run
end
