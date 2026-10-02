module
public import AvailableChainFGSAClaims.Statements.Packages.Healing

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params)

/-- RowPermissionAt: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RowPermissionAt {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ u v m J contested r x C nd,
    E.t_GST ≤ u → PhaseInterval p c E rho u v m J contested →
    u ≤ p.actionTime r → p.actionTime r ≤ v → x ∈ rho.honest →
    postClock E rho x (p.actionTime r) = some nd →
    actionSourceFG p c E rho x r = some (some C) →
    C ∈ FGSA.fullTree p nd.st →
    (FGSA.controls p nd.st).lo ≤ hOf p.E p.cfg C → hOf p.E p.cfg C ≤ m →
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair = some (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root)

/-- RowPermissionClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RowPermissionClaim : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    HealingPrem p c G E rho pt → RowPermissionAt p c E rho

/-- HealingInputClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def HealingInputClaim : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtW),
    HealingInputPrem p c G E rho pt → HealingInput p c E rho pt.w

/-- HTimeConcl: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def HTimeConcl {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) : Prop :=
  ∃ w, HealingInput p c E rho w ∧
    tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
    p.actionTime w.rStar + Γ p G + 4 * p.Δ < E.t_GST + B_H p G

/-- HTimeClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def HTimeClaim : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    HealingTimePrem p c G E rho pt → HTimeConcl p c E rho G

/-- ResetArrivalConcl: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def ResetArrivalConcl {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) : Prop :=
  ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar < E.t_GST + B'_reset p G

/-- ResetArrivalClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def ResetArrivalClaim : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    ResetArrivalPrem p c G E rho pt → ResetArrivalConcl p c E rho G

/-- RenewedPromotionConcl: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RenewedPromotionConcl {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G : Time) (r : Nat) : Prop :=
  ∀ u m J contested l q Q height,
    E.t_GST ≤ u → PhaseInterval p c E rho u (p.actionTime r) m J contested →
    u ≤ SA.proposalTime p.toParams q → q ≤ r * p.R →
    SA.proposalTime p.toParams l < SA.proposalTime p.toParams q →
    HonestProposal E rho (fgsaInterface p c) q Q → ExactService p c E rho q Q →
    OpeningEntry p c E rho r height → OpeningCovered p c E rho r Q →
    (∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v) →
    (∃ i ev, afterTicksIdx rho (p.actionTime r) ≤ i ∧
      rho.events[i]? = some ev ∧ EffectiveEvent p c E rho i ∧
      ev.time ≤ p.actionTime r + 2 * P p + Γ p G - 9 * p.Δ) ∨
    (∃ s X, HonestProposal E rho (fgsaInterface p c) s (eraseFG X) ∧ X.slot = s ∧
      ↑r * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      height + 1 ≤ hOf p.E p.cfg X ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ nd.st.fg.TF) (SA.proposalTime p.toParams s + p.Δ) y) ∧
      (PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
        ExactService p c E rho s (eraseFG X) ∧
        SA.gateTime p.toParams s ≤ p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ))

/-- RenewedPromotionClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RenewedPromotionClaim : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtR),
    RenewedPromotionPrem p c G E rho pt → RenewedPromotionConcl p c E rho G pt.r

end AvailableChain.FGSA.Run
end
