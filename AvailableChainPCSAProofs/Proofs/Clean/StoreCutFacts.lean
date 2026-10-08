module
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.GateAdvance
public import AvailableChainPCSAProofs.Proofs.Clean.CutReads

public section

/-! C6 StoreCutFacts: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Every lock at an inclusive read is below an own result at an already completed gate. -/
theorem pcsa_lock_storeAt_timed_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (x : V) (t : Time) (row : Block × Nat × Time)
    (hr : row ∈ (storeAt p c E rho x t).base.obligations) :
    ∃ (k : Nat) (i : Slot) (X : Block),
      rho.events[k]? = some (V2.Event.tick x (SA.gateTime p.toParams i)) ∧
      SA.gateTime p.toParams i ≤ t ∧ gateResultAt p c E rho x i = some (some X) ∧
        Block.Preceq row.1 X := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore h.valid.toScheduleWellFormed] at hr
  obtain ⟨k, hk, i, X, he, hX, hb, _⟩ := pcsa_lock_stateBefore_origin E rho h _ x row hr
  exact ⟨k, i, X, he,
    (V2.D.Engine.index_lt_read_length_iff h.valid.toScheduleWellFormed t he).mp hk, hX, hb⟩
end AvailableChain.PCSA.Run

end
