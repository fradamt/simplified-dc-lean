module
public import AvailableChainFGSAProofs.Proofs.Assembly.Outage -- shake: keep (body-to-claim checks)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.OutageExport

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {fast : Bool} {pt : PtOut} {ΔF : Time}
variable (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : ∀ y r C, y ∈ rho.honest →
      actionSource p c E rho y r = some (some C) →
      ∃ X G, candidatesAt p c E rho y r = some X ∧ C ∈ X ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        (∀ A ∈ X, Block.Preceq A G) ∧
        (∀ A ∈ X, fastAt p c E rho y (r * p.R) A) ∧
        ∃ i, IsGateTick p c rho i y (r * p.R) ∧ gatePassedAt p c E rho i)
    (hnamed : ∀ i y r a, HonestRowAt p c E rho i y r a →
      ∃ e C G, namedEntry a.payload.height_pair = some e ∧
        actionSourceFG p c E rho y r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho y (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧
        fastAt p c E rho y (r * p.R) (eraseFG C))
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ pt.b₀ → SA.gateTime p.toParams s ≤ pt.b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    (hnonempty : ∀ i y s, i < timeIdx rho pt.b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams s ≤ pt.b₀ →
      gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hbelow : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hleaseOrigin : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i y).base.obligations,
      ∃ q < i, ∃ s C, IsGateTick p c rho q y s ∧
        gatePassedAt p c E rho q ∧
        gateResultAt p c E rho q = some (some C) ∧ Block.Preceq row.1 C)
    (hsavedKeep : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      ∀ q s C, q < i → IsGateTick p c rho q y s →
      gateResultAt p c E rho q = some (some C) →
      GridCO.savedGenuine (storeAt p c E rho i y).base s = some (some C))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho pt.b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hmono : ∀ y, y ∈ rho.honest → ∀ i k,
      i ≤ k → k ≤ timeIdx rho pt.b₀ →
      Block.Preceq (S_at p c E rho i y) (S_at p c E rho k y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ pt.b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho
          (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') →
          Block.Preceq C' C)

include hstore hframe hsrc htsrc hnamed hordered hnonempty htransfer hbelow
  hleaseOrigin hsOrigin hmono hcleanGate

include hsavedKeep in
/-- The expanded compatibility body has the frozen full claim conclusion. -/
example (h : OutagePrem p c fast E rho pt ΔF) : OutageCompatAt p c E rho pt := by
  exact outage_compat_body
    (hstrat := sourceDiscipline_strat p c E rho (pt := ())
      ⟨h.set.pre.base, h.set.faultQ⟩ hstore)
    (hstore := hstore) (hframe := hframe) (hsrc := hsrc)
    (htsrc := htsrc) (hnamed := hnamed)
    (hordered := hordered) (hnonempty := hnonempty) (htransfer := htransfer)
    (hbelow := hbelow) (hleaseOrigin := hleaseOrigin) (hsOrigin := hsOrigin)
    (hmono := hmono) (hcleanGate := hcleanGate)
    (hsavedKeep := fun _ => hsavedKeep) h

/-- The expanded fast body has the frozen P1 conclusion. -/
example (h : OutagePrem p c true E rho pt ΔF) : P1Concl p c E rho pt := by
  exact fast_p1_body
    (hstrat := sourceDiscipline_strat p c E rho (pt := ())
      ⟨h.set.pre.base, h.set.faultQ⟩ hstore)
    (hstore := hstore) (hframe := hframe) (hsrc := hsrc)
    (htsrc := htsrc) (hnamed := hnamed)
    (hordered := hordered) (hnonempty := hnonempty) (htransfer := htransfer)
    (hbelow := hbelow) (hleaseOrigin := hleaseOrigin) (hsOrigin := hsOrigin)
    (hmono := hmono) (hcleanGate := hcleanGate) h

include hsavedKeep in
/-- The expanded slow body has the P1 conclusion as its first clause. -/
example (h : OutagePrem p c false E rho pt ΔF) : P1Concl p c E rho pt := by
  exact (slow_p1_body
    (hstrat := sourceDiscipline_strat p c E rho (pt := ())
      ⟨h.set.pre.base, h.set.faultQ⟩ hstore)
    (hstore := hstore) (hframe := hframe) (hsrc := hsrc)
    (htsrc := htsrc) (hnamed := hnamed)
    (hordered := hordered) (hnonempty := hnonempty) (htransfer := htransfer)
    (hbelow := hbelow) (hleaseOrigin := hleaseOrigin) (hsOrigin := hsOrigin)
    (hmono := hmono) (hcleanGate := hcleanGate)
    (hsavedKeepSlow := hsavedKeep) h).1

end AvailableChain.FGSA.Run.Tests.OutageExport
