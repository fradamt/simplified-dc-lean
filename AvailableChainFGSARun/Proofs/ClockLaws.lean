module
public import AvailableChainFGSARun.Proofs.Excludes
public import AvailableChainKitV2.ClockLaws

public section

/-! The base clock and the restore premises for FG-SA (plan T7.4). -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In : Type} (c : AppCodec In)

/-- The run clock is the store's base clock. -/
def fgsaClock : V2.Engine.ClockLaws (fgsa p c) where
  now nd := nd.st.base.now
  init := rfl
  clock nd t := (clock_vn nd.st t).2
  process nd o := process_base_now nd.st (toWire p o)
  recordOwn_now _ _ := rfl

/-- Restore resets the base clock to zero, for every durable record. -/
theorem fgsa_restore_now_eq :
    ∀ d, (fgsaClock p c).now ((fgsa p c).restore d) = 0 := by
  intro d
  rfl

/-- The restore clock bound used by the Kit follows from the equality. -/
theorem fgsa_hrestore_now :
    ∀ d, (fgsaClock p c).now ((fgsa p c).restore d) ≤ 0 := by
  intro d
  rw [fgsa_restore_now_eq]

/-- A store predicate that holds initially holds after restore. -/
theorem fgsa_hrestore (Q : FGSA.State p.n → Prop) (hQ : Q (FGSA.initial p.n)) :
    ∀ nd : Node p, Q ((fgsa p c).restore ((fgsa p c).durable nd)).st := by
  intro nd
  exact hQ

/-- A list field that is empty initially has no members after restore. -/
theorem fgsa_hrestore_field {α : Type} (field : FGSA.State p.n → List α)
    (hfield : field (FGSA.initial p.n) = []) :
    ∀ (nd : Node p) x, x ∈ field ((fgsa p c).restore ((fgsa p c).durable nd)).st →
      x ∈ field nd.st := by
  intro nd x hx
  change x ∈ field (FGSA.initial p.n) at hx
  rw [hfield] at hx
  exact (List.not_mem_nil hx).elim

end AvailableChain.FGSA.Run

end
