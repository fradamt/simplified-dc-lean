module
public import AvailableChainFGSAProofs.Proofs.Healing.RepairH6S
public import AvailableChainFGSAProofs.Proofs.Shared.RetainedConsumersH6S

public section

/-! HG.1 seed (blueprint 21:1333–1350, 1570–1574; TF-SEED Q4).
The qualification is the two-arm premise in the frozen `TFrontier`.
The initial phase includes the q+1 proposal and HEAD reads.
This module supplies their lease cover. It does not extend the phase to the q+1 gate.
The INLINE `writes` producer is `fgsa_leaseOrigins_lastWrite` (Foundations/Leases:392).
That producer is used at Assembly; this module imports only the Healing lane. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Blueprint 21 H.6:915–944 and H.6-S:988–1025.
DC: SAME the two-arm seed premise of the frozen TFrontier. -/
def FrontierSeedQualification (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : Prop :=
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q)

/-- Blueprint 21:1333–1350; TF-SEED Q4.
DC: SAME an explicit equation adapter for the frozen two-arm seed premise. -/
theorem frontierSeedQualification_iff (p : Params) {V : Type} (E : Generic.Env V)
    (u : Time) (q : Slot) : FrontierSeedQualification p E u q ↔
  (∃ β : Slot,
    u < SA.proposalTime p.toParams β ∧
    (∀ b, u < SA.proposalTime p.toParams b → β ≤ b) ∧
    SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams q) ∨
  (∃ b : Slot,
    u ≤ SA.voteTime p.toParams b ∧
    (∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i) ∧
    p.k ≤ b + 1 ∧
    E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k) ∧
    SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams q) := Iff.rfl


variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21 H.6:915–986; TF-SEED Q1.
DC: SAME the unchanged H.6 repair output supplies the seed qualification. -/
theorem tfSeed_two_from_tRepair (h : TRepair p c E rho)
    {G u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β)
    (hmin : ∀ b, u < SA.proposalTime p.toParams b → β ≤ b)
    (hbudget : u + ρΓ p G ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q ≤ u + ρΓ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  obtain ⟨q, Q, hlt, hgate, hp, hs⟩ :=
    (h G u v m J contested hgap hG hgst hphase).1 β hβ hmin |>.2 hbudget
  exact ⟨q, Q, Or.inl ⟨β, hβ, hmin, hlt⟩, hgate, hp, hs⟩

/-- Blueprint 21 H.6-S:988–1033; TF-SEED Q1.
DC: SAME the H.6-S repair output and its inputs supply the seed qualification. -/
theorem tfSeed_one_from_tRepair (h : TRepair p c E rho)
    {G u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hgap : ProposalGap p c E rho G) (hG : 4 * p.Δ ≤ G)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hmin : ∀ i, u ≤ SA.voteTime p.toParams i → b ≤ i)
    (hkb : p.k ≤ b + 1) (hwindow : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k))
    (hbudget : u + ρ₁ p G ≤ v) :
    ∃ q Q, FrontierSeedQualification p E u q ∧
      SA.gateTime p.toParams q < u + ρ₁ p G ∧
      HonestProposal E rho (fgsaInterface p c) q Q ∧ ExactService p c E rho q Q := by
  obtain ⟨q, Q, hlt, hgate, hp, hs⟩ :=
    (h G u v m J contested hgap hG hgst hphase).2 b hb hmin hkb hwindow |>.2 hbudget
  exact ⟨q, Q, Or.inr ⟨b, hb, hmin, hkb, hwindow, hlt⟩, hgate, hp, hs⟩

omit [DecidableEq V] in
/-- Blueprint 21 HG.1:1333–1350; TF-SEED Q1.
DC: SAME later proposals keep the repair threshold and phase-start qualification. -/
theorem tfSeed_later {u : Time} {q s : Slot} (hseed : FrontierSeedQualification p E u q)
    (hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams s) :
    FrontierSeedQualification p E u s := by
  rcases hseed with ⟨β, hβ, hmin, hlt⟩ | ⟨b, hb, hmin, hkb, hwindow, hlt⟩
  · exact Or.inl ⟨β, hβ, hmin, hlt.trans hlater⟩
  · exact Or.inr ⟨b, hb, hmin, hkb, hwindow, hlt.trans hlater⟩

variable {p c}

/-- Blueprint 21:925–944, 1004–1025, 1570–1574; TF-SEED Q4 steps 1–2.
DC: INTENTIONAL the frozen seed premise gives the q+1 lease cover in the initial phase.
The q+1 gate needs a separate proof under the frontier cap. -/
theorem tfSeed_qSucc_lease_cover [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (crossing : RXing p c E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q) : RepairLeaseCover E rho (q + 1) := by
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  rcases hseed with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, hwindow, hlt⟩
  · exact repair_lease_cover_two E rho hrec mono crossing writes hgst hphase hβ
      (hlt.trans hlater) hvs
  · exact repair_lease_cover_one E rho hrec mono crossing writes hgst hphase hb hwindow
      (hlt.trans hlater) hvs

/-- Blueprint 21:925–944, 1004–1025, 1570–1574; plan §3.1 step 7.
DC: INTENTIONAL the retained H.6 input at both actual q+1 reads in the initial phase.
Both seed arms use the checked lease cover. No phase through the q+1 gate is used. -/
theorem frontier_seed_qSucc_input [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (crossing : RXing p c E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams (q + 1))))
    {ih : Nat} {y : V} (hy : y ∈ rho.honest)
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1)))) :
    RetainedH6Input p
      (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
      (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1) := by
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hhead : u ≤ SA.voteTime p.toParams q := by
    rcases tfSeed_later p E hseed hlater with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
    · exact repair_head_after_two hβ hlt
    · exact repair_head_after_one hb hlt
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  exact repair_h6_input E rho hrec mono crossing hgst hphase hhead hvs
    (tfSeed_qSucc_lease_cover E rho hrec mono crossing writes hgst hphase hseed) hx hip hy hih

/-- ROOT-DIGEST W2b. Blueprint 21:956–958, 1004–1025, 1570–1574; plan §3.1 step 7.
DC: INTENTIONAL every honest q+1 HEAD is the honest q+1 proposal.
The two arms consume `fgsa_retainedReads_H6` and `fgsa_retainedReads_H6S`, respectively. -/
theorem frontier_seed_qSucc_head [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
    (crossing : RXing p c E rho)
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
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool} {q : Slot}
    (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.gateTime p.toParams q) m J contested)
    (hseed : FrontierSeedQualification p E u q)
    {B : Block} (hp : HonestProposal E rho (fgsaInterface p c) (q + 1) B) :
    ∀ y ∈ rho.honest, headAtLabel p c E rho y (q + 1) = some B := by
  have hd := p.deltaPos
  have hlater : SA.proposalTime p.toParams q < SA.proposalTime p.toParams (q + 1) := by
    change 4 * p.Δ * (q : Int) < 4 * p.Δ * ((q + 1 : Nat) : Int)
    push_cast
    linarith
  have hhead : u ≤ SA.voteTime p.toParams q := by
    rcases tfSeed_later p E hseed hlater with ⟨β, hβ, _, hlt⟩ | ⟨b, hb, _, _, _, hlt⟩
    · exact repair_head_after_two hβ hlt
    · exact repair_head_after_one hb hlt
  have hvs : SA.voteTime p.toParams (q + 1) ≤ SA.gateTime p.toParams q := by
    change 4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (q : Int) + 6 * p.Δ
    push_cast
    linarith
  have hE := hrec.base.valid
  have hN := hrec.base.noRestart
  have hDelta := hrec.base.delta
  obtain ⟨ip, x, raw, sup, rows, hx, hip, hseat, hem⟩ := repair_proposal_emission E rho hp
  have hGST : E.t_GST ≤ SA.proposalTime p.toParams (q + 1) - p.Δ := by
    refine hgst.trans (hhead.trans ?_)
    change 4 * p.Δ * (q : Int) + p.Δ ≤ 4 * p.Δ * ((q + 1 : Nat) : Int) - p.Δ
    push_cast
    linarith
  have hhor : SA.voteTime p.toParams (q + 1) ≤ rho.horizon := hvs.trans hphase.2.1
  have hpt : SA.proposalTime p.toParams (q + 1) - p.Δ + E.Δ ≤
      SA.voteTime p.toParams (q + 1) := by
    rw [hDelta]
    change 4 * p.Δ * ((q + 1 : Nat) : Int) - p.Δ + p.Δ ≤
      4 * p.Δ * ((q + 1 : Nat) : Int) + p.Δ
    linarith
  have hSync := Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _
    hrec.sync (fgsaDelay_nonrow E.Δ _) hGST hpt hhor
  have hinput : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1))) →
      RetainedH6Input p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1) := by
    intro y hy ih hih
    exact frontier_seed_qSucc_input E rho hrec mono crossing writes hgst hphase hseed
      hx hip hy hih
  have hreads : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams (q + 1))) →
      ∃ Kc, RetainedReadPremises p
        (clock p (rho.stateBefore E ip x).st (SA.proposalTime p.toParams (q + 1)))
        (clock p (rho.stateBefore E ih y).st (SA.voteTime p.toParams (q + 1))) (q + 1)
        (controls p (clock p (rho.stateBefore E ip x).st
          (SA.proposalTime p.toParams (q + 1)))).Z B Kc := by
    rcases hseed with _h6 | _h6s
    · exact fgsa_retainedReads_H6 (hroots := hrec.base.idealization)
        E rho hE hN hDelta (q + 1) hSync hx hip hseat B raw sup
        rows hem hinput
    · exact fgsa_retainedReads_H6S (hroots := hrec.base.idealization) E rho hE hN hDelta (q + 1)
        hSync hx hip hseat B raw sup
        rows hem hinput
  exact exactService_head_of_retained_proposal_recovery E rho G hrec (q + 1) hGST hx hip
    hseat B raw sup rows hem _ hreads hhor

end AvailableChain.FGSA.Run
end
