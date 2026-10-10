module
public import AvailableChainFGSAProofs.Proofs.Healing.CommonEntryFacts

public section

/-! H-COMMON height branches and the second opening (plan §3F.3–4).
H-GATE supplies a retained source above Qfg at the first opening and above an actual
selected body K at the second opening. Each opening has its own phase premise. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

section Service
variable [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time} (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (services : OpeningServiceScopes E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)

include hrec mono crossing services writes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: SAME each selected source extends Qfg and
its own height is capped by the first-opening phase. -/
theorem common_sources_extend_and_cap
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested) :
    ∀ x K, x ∈ rho.honest → actionSourceFG p c E rho x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (heightView p K).h ≤ m := by
  intro x K hx hK
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨i, ht⟩ := common_source_tick E rho hK
  obtain ⟨hsrc, _, _, _⟩ := opening_source_body E rho hS ht hK
  obtain ⟨L, hL, hQL⟩ := later_opening_source_extends E rho hrec mono crossing services
    writes hgst hQ
    hQfg hexact hu hqr hphase hx ht
  have he : L = K := Option.some.inj (hL.symm.trans hsrc)
  exact ⟨he ▸ hQL, common_source_height_le E rho hS hphase hx hK⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3. DC: SAME a high Qfg fixes the first-opening
height and T_h.root by the plateau. -/
theorem common_entry_at_high
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    (hh : (heightView p Qfg).h = m) : OpeningEntry p c E rho r m :=
  common_entry_of_plateau E rho r m Qfg hh
    (common_sources_extend_and_cap E rho hrec mono crossing services writes hgst hQ hQfg
      hexact hu hqr
      hphase)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.4. DC: INTENTIONAL with the new phase premise,
each source of the next opening extends the actual selected body K. Service for K
comes from next_opening_body_service; K needs no HonestProposal. -/
theorem common_next_sources_extend_and_cap
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K)) :
    ∀ x L, x ∈ rho.honest → actionSourceFG p c E rho x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (heightView p L).h ≤ m := by
  intro x L hx hL
  have hS := hrec.base.valid.toScheduleWellFormed
  obtain ⟨i, ht⟩ := common_source_tick E rho hL
  obtain ⟨D, hserv, hdom, hKD, _⟩ := next_opening_body_service E rho hrec mono crossing
    services writes
    hgst hQ hQfg hexact hu hqr hphase hy hK hx ht
  have hcut : E.t_GST ≤ slotStartZ p (((r + 1) * p.R : Nat) : Int) := by
    have hqrI : (q : Int) ≤ ((r * p.R : Nat) : Int) := by exact_mod_cast hqr
    have hrr : ((r * p.R : Nat) : Int) ≤ (((r + 1) * p.R : Nat) : Int) := by
      exact_mod_cast (Nat.mul_le_mul_right p.R (Nat.le_succ r))
    change E.t_GST ≤ 4 * p.Δ * (((r + 1) * p.R : Nat) : Int)
    change u ≤ 4 * p.Δ * (q : Int) at hu
    nlinarith [p.deltaPos]
  have enabled := healing_gate_enabled_of_recovery hrec.toRecovery₂ hx ht hphase.2.1 hcut
  have hcand := openingSource_candidate_of_gateService E rho hS i x (r + 1) (eraseFG D) ht
    enabled hserv
  obtain ⟨L', hL', hDL'⟩ := openingSource_extends_served E rho i x (r + 1) D hdom hcand
  obtain ⟨hsrc, _, _, _⟩ := opening_source_body E rho hS ht hL
  have he : L' = L := Option.some.inj (hL'.symm.trans hsrc)
  exact ⟨he ▸ KitFG.preceq_trans hKD hDL', common_source_height_le E rho hS hphase hx hL⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.4. DC: INTENTIONAL an actual high witness at r
fixes the next opening's entry only under the phase through a_(r+1). -/
theorem common_next_entry
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    {y : V} {K : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hK : actionSourceFG p c E rho y r = some (some K)) (hh : (heightView p K).h = m)
    (hphase : PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested) :
    OpeningEntry p c E rho (r + 1) m :=
  common_entry_of_plateau E rho (r + 1) m K hh
    (common_next_sources_extend_and_cap E rho hrec mono crossing services writes hgst hQ hQfg hexact
      hu hqr hphase hy hK)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.9; plan §3F.3–4. DC: INTENTIONAL the low pivot gives either
one low entry or an actual high source with the conditional second-opening entry. -/
theorem common_entry_at_low
    {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {q r : Nat} {Q : Block} {Qfg : FGBlock (Fin p.n)}
    (hgst : E.t_GST ≤ u) (hQ : HonestProposal E rho (fgsaInterface p c) q Q)
    (hQfg : eraseFG Qfg = Q) (hexact : ExactService p c E rho q Q)
    (hu : u ≤ SA.proposalTime p.toParams q) (hqr : q ≤ r * p.R)
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J contested)
    (hh : (heightView p Qfg).h = m - 1) :
    OpeningEntry p c E rho r (m - 1) ∨
      ((∃ x K, x ∈ rho.honest ∧ actionSourceFG p c E rho x r = some (some K) ∧
          (heightView p K).h = m) ∧
        (PhaseInterval p c E rho u (p.actionTime (r + 1)) m J contested →
          OpeningEntry p c E rho (r + 1) m)) := by
  rcases common_low_or_high E rho r m Qfg hh
      (common_sources_extend_and_cap E rho hrec mono crossing services writes hgst hQ hQfg
        hexact hu hqr
        hphase) with hlow | hhigh
  · exact Or.inl hlow
  · obtain ⟨x, K, hx, hK, hhK⟩ := hhigh
    exact Or.inr ⟨⟨x, K, hx, hK, hhK⟩, common_next_entry E rho hrec mono crossing services
      writes hgst
      hQ hQfg hexact hu hqr hx hK hhK⟩

end Service
end AvailableChain.FGSA.Run
end
