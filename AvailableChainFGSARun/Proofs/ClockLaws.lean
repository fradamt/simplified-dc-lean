module
public import AvailableChainFGSARun.Proofs.Excludes
public import AvailableChainFGSARun.Proofs.Restore
public import AvailableChainKitV2.DutyClockLaws
public import AvailableChainFGSARun.Proofs.RetainedClock
public import AvailableChainGeneric.Statements.V2.Duty.Reads

public section

/-! The base clock and the restore premises for FG-SA (plan T7.4). -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In)

/-- [P3 r3.5.6 F0.2] An ancestor of F stays an ancestor through each local step. -/
theorem fgsa_monoAlong_preceq_F (X : FGBlock (Fin p.n)) :
    Gen.V2.Duty.MonoAlong (P := fgsa p c) (fun nd => FGBlock.Preceq X nd.st.fg.F) := by
  rw [Gen.V2.Duty.MonoAlong_def]
  refine ⟨?_, ?_, ?_⟩
  · intro nd t h
    change FGBlock.Preceq X (clock p nd.st t).fg.F
    rwa [clock_F_eq]
  · intro nd o h
    exact KitFG.preceq_trans h (process_F_mono p nd.st (toWire p o))
  · intro nd o h
    exact h

/-- A predicate true of reset stores at every clock holds after restore. -/
theorem fgsa_hrestore_retained (Q : FGSA.State p.n → Prop)
    (hQ : ∀ t, Q (FGSA.initialAt p.n t)) :
    ∀ nd : Node p, Q ((fgsa p c).restore ((fgsa p c).durable nd)).st := by
  intro nd
  exact hQ nd.st.base.now

/-- A list field empty in every reset store has no members after restore. -/
theorem fgsa_hrestore_field_retained {α : Type} (field : FGSA.State p.n → List α)
    (hfield : ∀ t, field (FGSA.initialAt p.n t) = []) :
    ∀ (nd : Node p) x, x ∈ field ((fgsa p c).restore ((fgsa p c).durable nd)).st →
      x ∈ field nd.st := by
  intro nd x hx
  change x ∈ field (FGSA.initialAt p.n nd.st.base.now) at hx
  rw [hfield] at hx
  exact (List.not_mem_nil hx).elim

end AvailableChain.FGSA.Run

end
