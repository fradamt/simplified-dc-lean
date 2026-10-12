module
public import AvailableChainFGSAProofs.Proofs.Finality.Middle

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- The actual reachable store supplies the root premise for the generic batch draft. -/
private theorem p0d7a3_reachable_root_leaf (p : Params) (st : State p.n)
    (hr : Reachable p st) : ViewRootInj st.fg.TF :=
  viewRootInj_TF p st (storeInvariant p st hr)

#print axioms p0d7a3_reachable_root_leaf

private def p0d7a3_lookup_parent : FGBlock (Fin 1) := .node .genesis 1 ⟨1⟩ 0 []
private def p0d7a3_lookup_opening : FGBlock (Fin 1) := .node p0d7a3_lookup_parent 2 ⟨2⟩ 0 []
private def p0d7a3_lookup_store : State 1 :=
  { initial 1 with fg := { (initial 1).fg with TF := {.genesis, p0d7a3_lookup_parent} } }

-- The actual lookup operations agree after exactly one parent step.
private theorem p0d7a3_parent_lookup_eq (st : State 1) (Q : Block) :
    parentFG st Q = fgBlockOf st Q.parent := rfl

-- Two non-genesis blocks expose both incorrect specializations.
-- This is a lookup fixture, not an ExecutionValid run.
private theorem p0d7a3_non_genesis_lookup :
    parentFG p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) = some p0d7a3_lookup_parent ∧
    fgBlockOf p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening).parent =
      some p0d7a3_lookup_parent ∧
    fgBlockOf p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) = none ∧
    parentFG p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening).parent =
      some .genesis := by
  decide

private theorem p0d7a3_carrier_lookup :
    (fun nd Q => fgBlockOf nd Q.parent) p0d7a3_lookup_store (eraseFG p0d7a3_lookup_opening) =
      some p0d7a3_lookup_parent := by decide

#print axioms p0d7a3_parent_lookup_eq
#print axioms p0d7a3_non_genesis_lookup
#print axioms p0d7a3_carrier_lookup

private theorem p0d7a3_reset_before_start (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (w : HealingWitness) (h : H0 p c E rho w) : p.actionTime w.rStar < tstar p w := by
  have hgap : w.rStar * p.R + 2 ≤ w.u := h.label ▸ h.proposal_lower
  have hd := p.deltaPos
  change 4 * p.Δ * (w.rStar * p.R : Nat) + 6 * p.Δ <
    4 * p.Δ * (w.u : Time) + 6 * p.Δ
  have hcast : (w.rStar * p.R : Time) + 2 ≤ w.u := by exact_mod_cast hgap
  push_cast
  nlinarith

private theorem p0d7a3_constructed_run
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (pt : KernelPt)
    (hδ : p.δt = 2 * p.R)
    (hK : KernelPrem_W p c G ΔF E rho pt)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t)
    (hBatch : BatchCoverage p ΔF .target)
    (hSOCOVTarget : ∀ x ∈ rho.honest, ∀ (r : Nat) (C : FGBlock (Fin p.n)),
      actionSourceFG p c E rho x r = some (some C) → high p pt.w C →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        RowComplete p c rho x a ∧
        a.payload.height_pair = .vote (heightView p C).h (heightView p C).T_h.root false)
    (A : Block)
    (hA : HonestProposal E rho (fgsaInterface p c) (pt.r * p.R) A) :
    ∃ m : KernelMiddleWitness_W p c E rho ΔF pt A,
      m.A₀ ≠ .genesis ∧ pt.w.M + 1 ≤ (heightView p m.A₀).h ∧
      FGBlock.Preceq m.A₀ m.U ∧ m.A₀ ≠ m.U ∧
      (heightView p m.U).h = (heightView p m.A₀).h + 1 ∧
      (heightView p m.X_D).J = m.U ∧
      (∀ x C, x ∈ rho.honest →
        actionSourceFG p c E rho x (pt.r + 2) = some (some C) →
        (heightView p C).h ≤ m.d + 2) ∧
      (∀ i x W, i ≤ rho.events.length → i ≤ afterTicksIdx rho (p.actionTime (pt.r + 2)) →
        HeldAt p c E rho i x W → (heightView p W).h ≤ m.d + 2) ∧
      (∃ j x a C, HonestRowAt p c E rho j x pt.w.rStar a ∧
        actionSourceFG p c E rho x pt.w.rStar = some (some C) ∧
        p.actionTime pt.w.rStar < tstar p pt.w ∧
        (heightView p C).h = pt.w.M + 1 ∧ (heightView p C).h ≤ (heightView p m.A₀).h) ∧
      (∀ j x r a h, r < pt.r → HonestRowAt p c E rho j x r a → rowHeight a = some h →
        p.actionTime r < tstar p pt.w → h ≤ (heightView p m.A₀).h) := by
  obtain ⟨m⟩ := kernel_opening_and_middle p c E rho G ΔF pt hδ hK hNames hOrigin
    hBatch hSOCOVTarget A hA
  obtain ⟨hp, hn, hh, _⟩ := kernel_middle_fresh_U p c E rho ΔF pt A m
  refine ⟨m, ?_, ?_, hp, hn, hh, m.justifiedD, ?_, m.capThroughFinalAction, ?_, ?_⟩
  · intro he
    have hl := (kmid_kernel_bounds hK).2.2.2.2.1
    have hs := m.slotA
    rw [he] at hs
    change (0 : Nat) = pt.r * p.R at hs
    have hp : 2 ≤ pt.r * p.R := (Nat.le_add_left 2 pt.w.sStar).trans hl
    rw [← hs] at hp
    exact (by decide : ¬ (2 : Nat) ≤ 0) hp
  · rw [m.heightA]
    exact m.highA
  · intro x C hx hC
    exact kernel_middle_source_cap p c E rho ΔF pt A m
      hK.set.base.valid.toScheduleWellFormed hx hC
  · obtain ⟨j, x, a, C, ha, _, hs, _, hc⟩ := hK.input.wit.fresh
    refine ⟨j, x, a, C, ha, hs, p0d7a3_reset_before_start p c E rho pt.w hK.input.wit, hc, ?_⟩
    rw [hc, m.heightA]
    exact m.highA
  · intro j x r a h hr ha hh _
    exact kmid_rows_below_opening p c E rho pt.w hK.input.t.h2 hNames pt.r m.A₀
      (by rw [m.eraseA]; exact hA) (by rw [m.heightA]; exact m.highA)
      j x r a h hr ha hh

#print axioms p0d7a3_reset_before_start
#print axioms p0d7a3_constructed_run

end AvailableChain.FGSA.Run
end
