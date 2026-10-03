module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetLeaseStep -- shake: keep (J4-A fixtures)

set_option linter.privateModule false

/-! Blueprint 21 H.15:2894–2914; plan J4-A; B1/B13/B17/B18.
Conditional package: an actual passed write on a prefix with no emitted
source. The domain remains an explicit input; this is an A1 consumer.
No successor producer or concrete H0Reset run is claimed. -/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPostResetLeaseStep
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- conditional package, anti-vacuity: A1 covers an actual written prefix
-- that has no emitted source. Its synchrony comes from the reset cut.
example [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMono p c E rho)
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
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {ix : Nat} {x : V} {s : Slot} {C : Block} {g : Nat}
    (hx : x ∈ rho.honest) (hix : IsGateTick p c rho ix x s)
    (hpass : gatePassedAt p c E rho ix)
    (hres : gateResultAt p c E rho ix = some (some C))
    {B : FGBlock (Fin p.n)} (hCB : Block.Preceq w.CStar (eraseFG B))
    (hne : eraseFG B ≠ w.CStar)
    (hkey : (eraseFG B, g) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy
      p.toParams.engine p.n
      (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s C)
    (hgw : E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k))
    (hnotSource : ¬ ∃ r, SrcN p c E rho B r)
    {iy : Nat} {y : V} (hy : y ∈ rho.honest)
    (hiy : rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    {X : Finset (FGBlock (Fin p.n))}
    (hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho iy y)
      (SA.voteTime p.toParams (s + 1))) (s + 1))
    (hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq A W → A ∈ X)
    (hD : B ∈ D_at p c E rho iy y X) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho iy (s + 1)) ∧
      gatePassedAt p c E rho ix ∧ eraseFG B ≠ w.CStar ∧ ¬ ∃ r, SrcN p c E rho B r := by
  obtain ⟨hmem, _, hBC, _, hcase⟩ := healing_support_key_cases p hkey
  have hgst := postReset_written_sync p c E rho hrec h0r hx hix hCB hmem
  have harm : SA.releaseThreshold p.toParams ≤ SA.prefixSupport p.toParams
        (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
        (eraseFG B) ∨
      (E.t_GST ≤ SA.voteTime p.toParams (s + 1 - p.k) ∧
        GridCO.slowEligible p.toParams.engine
          (actView (clockPre p (storeAt p c E rho ix x) (SA.gateTime p.toParams s))) s
          (eraseFG B) = true) := hcase.imp_right (fun hel => ⟨hgw, hel⟩)
  exact ⟨healing_first_transfer_written p c E rho hrec mono writes hx hix hres hBC
    hgst.le harm hy hiy hXv hXc hD, hpass, hne, hnotSource⟩

-- conditional package: the causal cut gives strict label synchrony even
-- without a gate result or an emitted action source for the prefix.
example [Fintype V] {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {y : V} {s : Slot} {B : Block}
    (hy : y ∈ rho.honest) (ht : IsGateTick p c rho i y s)
    (hCB : Block.Preceq w.CStar B)
    (hB : B ∈ (actView (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams s))).blocks) : E.t_GST < SA.voteTime p.toParams s :=
  postReset_written_sync p c E rho hrec h0r hy ht hCB hB

end AvailableChain.FGSA.Run.Tests.HealingPostResetLeaseStep
end
