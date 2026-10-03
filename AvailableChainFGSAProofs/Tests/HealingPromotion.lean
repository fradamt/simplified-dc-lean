module
public import AvailableChainFGSAProofs.Proofs.Healing.PromotionArithmetic -- shake: keep (arithmetic tests)
public import AvailableChainFGSAProofs.Proofs.Healing.Promotion -- shake: keep (promotion helper tests)
public import AvailableChainFGSAProofs.Proofs.Healing.SupportPerm -- shake: keep (TPerm supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (RMono supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (last-write supplier)
public import AvailableChainFGSAProofs.Proofs.Foundations.RowService -- shake: keep (Assembly receipt supplier)

set_option linter.privateModule false

/-! H-PROMOTE helper tests. The full renewed theorem and HG.2 acceptance
remain open. These tests do not assume either conclusion.
The same-time examples check event cuts, not a valid execution. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPromotion
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- Fixed action, with height one. Sources can differ and rows can be old.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) {r : Nat} {Q : Block}
    (hentry : OpeningEntry p c E rho r 1) (hcovered : OpeningCovered p c E rho r Q) :
    ∃ U : FGBlock (Fin p.n), EntryAt p U 1 := by
  obtain ⟨U, hU, _⟩ := healing_promotion_fixed_rows
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (height := 1) (Q := Q)
    (hentry := hentry) (hcovered := hcovered)
  exact ⟨U, hU⟩

example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat)
    (hgst : E.t_GST ≤ p.actionTime r)
    (hhor : p.actionTime r + 2 * P p + Γ p G - 4 * p.Δ ≤ rho.horizon) :
    ∃ s, (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤
        p.actionTime r + 2 * P p + Γ p G - 10 * p.Δ ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s := by
  obtain ⟨_, s, hlo, hhi, hs, _⟩ := healing_promotion_gap
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (hgst := hgst) (hhor := hhor)
  exact ⟨s, hlo, hhi, hs⟩

-- Discharge the exact inline receipt binder with its main Assembly producer.
example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (hbound : LivenessBoundW p ΔF) {r j rSent : Nat} {y : V} {a : RowWire p.n}
    (hr : rSent ≤ r) (ha : HonestRowAt p c E rho j y rSent a)
    (hgst : E.t_GST ≤ p.actionTime r) {s : Slot}
    (hs : (r : Time) * P p + 2 * P p ≤ SA.proposalTime p.toParams s)
    (hhor : SA.proposalTime p.toParams s ≤ rho.horizon) :
    max (p.actionTime rSent) E.t_GST + ΔF < SA.proposalTime p.toParams s ∧
    ∀ x ∈ rho.honest,
      HeldBefore p c E rho x a (max (p.actionTime rSent) E.t_GST + ΔF) ∧
      HeldBefore p c E rho x a (p.actionTime r + ΔF) :=
  healing_promotion_row_receipt (p := p) (c := c) (E := E) (rho := rho)
    (G := G) (ΔF := ΔF) (hrec := hrec) (hbound := hbound)
    (rowsReceipt := fgsa_tRowsReceipt (p := p) (c := c) (E := E) (rho := rho)
      (ΔF := ΔF) (hΔ := hrec.base.delta) (hv := hrec.base.valid)
      (hnr := hrec.base.noRestart) (hsync := hrec.sync) (hΔF := hrec.deltaF))
    (r := r) (j := j) (rSent := rSent) (y := y) (a := a)
    (hr := hr) (ha := ha) (hgst := hgst) (s := s) (hs := hs) (hhor := hhor)

omit [Fintype V] in
example {x : V} {r : Nat} {K : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    PhaseBody p c E rho (r * p.R) (eraseFG K) :=
  healing_promotion_source_body (p := p) (c := c) (E := E) (rho := rho)
    (x := x) (r := r) (K := K) (hx := hx) (hK := hK)

example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (crossing : RXing p c E rho) {u : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool} {r : Nat} {s : Slot}
    {x : V} {K : FGBlock (Fin p.n)} {Q : Block} (hgst : E.t_GST ≤ u)
    (hphase : PhaseInterval p c E rho u (SA.proposalTime p.toParams s) m J contested)
    (hu : u ≤ SA.voteTime p.toParams (r * p.R))
    (hgate : p.actionTime r ≤ SA.proposalTime p.toParams s)
    (hx : x ∈ rho.honest) (hK : actionSourceFG p c E rho x r = some (some K))
    (hs : r * p.R + 2 ≤ s) (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    Block.Preceq (eraseFG K) Q.parent :=
  healing_promotion_source_parent (p := p) (c := c) (E := E) (rho := rho)
    (perm := healing_tPerm (p := p) (c := c) (E := E) (rho := rho)
      (G := G) (ΔF := ΔF) (hrec := hrec)
      (mono := fgsa_rMono (p := p) (c := c) (E := E) (rho := rho)) (crossing := crossing)
      (writes := fgsa_leaseOrigins_lastWrite (p := p) (c := c) (E := E) (rho := rho)
        (hs := hrec.base.valid.toScheduleWellFormed)))
    (u := u) (m := m) (J := J) (contested := contested) (r := r) (s := s)
    (x := x) (K := K) (Q := Q) (hgst := hgst) (hphase := hphase) (hu := hu)
    (hgate := hgate) (hx := hx) (hK := hK) (hs := hs) (hQ := hQ)

omit [Fintype V] in
example {u : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    {l s : Slot} {Q : Block}
    (hrepair : ∀ v, PhaseInterval p c E rho u v m J contested → RepairAfter p c E rho l v)
    (hafter : SA.proposalTime p.toParams l < SA.proposalTime p.toParams s)
    (hQ : HonestProposal E rho (fgsaInterface p c) s Q) :
    PhaseInterval p c E rho u (SA.gateTime p.toParams s) m J contested →
      ExactService p c E rho s Q :=
  healing_promotion_continuing_service (p := p) (c := c) (E := E) (rho := rho)
    (u := u) (m := m) (J := J) (contested := contested) (l := l) (s := s) (Q := Q)
    (hrepair := hrepair) (hafter := hafter) (hQ := hQ)

example {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF) (r : Nat) (q : Slot)
    (hgst : E.t_GST ≤ (r : Time) * P p)
    (hhor : max (p.actionTime r + Γ p G + 4 * p.Δ + epsF p ΔF)
      (SA.proposalTime p.toParams q + 2 * P p + Γ p G + 2 * p.Δ) ≤ rho.horizon) :
    let U_F := max ((r : Time) * P p + betaF p ΔF - 4 * p.Δ)
      (SA.proposalTime p.toParams q + 2 * P p - 4 * p.Δ)
    ∃ s, U_F < SA.proposalTime p.toParams s ∧
      SA.proposalTime p.toParams s ≤ U_F + Γ p G ∧
      Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) s := by
  obtain ⟨_, s, hlo, hhi, hs, _, _⟩ := healing_promotion_age_gap
    (p := p) (c := c) (E := E) (rho := rho) (G := G) (ΔF := ΔF)
    (hrec := hrec) (r := r) (q := q) (hgst := hgst) (hhor := hhor)
  exact ⟨s, hlo, hhi, hs⟩

-- q = rR uses the initial exact gate. No strict later-opening call is used.
omit [Fintype V] in
example (r : Nat) (Q : Block) (hservice : ExactService p c E rho (r * p.R) Q)
    (hhor : p.actionTime r ≤ rho.horizon) (x : V) (hx : x ∈ rho.honest) :
    actionSource p c E rho x r = some (some Q) := by
  have hg : SA.gateTime p.toParams (r * p.R) ≤ rho.horizon := by
    rwa [← fgsa_grid_action_gate, fgsa_grid_action_time]
  exact (hservice.2 hg x hx).2.2.2.2 r rfl

-- A receipt at time 10 is outside the strict cut at 10 and inside the inclusive cut.
-- A tick at that time is before the delivery in the post-tick cut.
omit [Fintype V] in
example (x : V) (o : Obj p) :
    let same := { rho with events := [.tick x 10, .deliver x o 10] }
    V2.D.Run.idxBefore same 10 = 0 ∧ timeIdx same 10 = 2 ∧ afterTicksIdx same 10 = 1 := by
  change 0 = 0 ∧ 2 = 2 ∧ 1 = 1
  decide

end AvailableChain.FGSA.Run.Tests.HealingPromotion
end

namespace AvailableChain.FGSA.Run.Tests.HealingPromotion
open AvailableChain.SimplexFG

private def promotionParams : Params where
  Δ := 1
  n := 4
  k := 2
  η := 0
  deltaPos := by decide
  nPos := by decide
  kLarge := by decide
  etaNonneg := by decide
  R := 3
  δt := 6
  RLarge := by decide

-- ΔF = 6 > Δ = 1, κ = R = 3, and G = 10 has a nonzero grid remainder.
example : let p := promotionParams
    p.Δ < 6 ∧ betaF p 6 = 12 ∧ epsF p 6 = 4 ∧ Γ p 10 = 8 ∧
      p.actionTime 1 + 6 = carrierTimeW p 6 1 := by decide

example : Γ (promotionParams) 10 ≤ 10 ∧
    10 < Γ (promotionParams) 10 + 4 * (promotionParams).Δ :=
  healing_promotion_gap_remainder (p := promotionParams) (G := 10)

-- Height-one entry and two-period maturity, with the same unequal row delay fixture.
example : EntryAt (promotionParams) (.genesis : FGBlock (Fin 4)) 1 := ⟨rfl, rfl⟩

example : (.genesis : FGBlock (Fin 4)).slot + (promotionParams).δt ≤ 9 :=
  healing_promotion_maturity (p := promotionParams) (hδ := rfl)
    (r := 1) (s := 9) (U := .genesis) (hU := by decide) (hs := by decide)

-- Each arm can set U_F. These values check both terminal and gate budgets.
example : let p := promotionParams
    max ((2 : Time) * P p + betaF p 6 - 4 * p.Δ)
      (SA.proposalTime p.toParams 0 + 2 * P p - 4 * p.Δ) = 32 ∧
    max ((1 : Time) * P p + betaF p 6 - 4 * p.Δ)
      (SA.proposalTime p.toParams 3 + 2 * P p - 4 * p.Δ) = 32 ∧
    max (p.actionTime 1 + Γ p 10 - p.Δ + epsF p 6)
      (SA.proposalTime p.toParams 3 + 2 * P p + Γ p 10 - 3 * p.Δ) = 41 ∧
    max (p.actionTime 1 + Γ p 10 + 4 * p.Δ + epsF p 6)
      (SA.proposalTime p.toParams 3 + 2 * P p + Γ p 10 + 2 * p.Δ) = 46 := by decide

end AvailableChain.FGSA.Run.Tests.HealingPromotion
