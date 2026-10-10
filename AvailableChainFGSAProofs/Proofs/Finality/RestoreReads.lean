module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Finalized ancestry survives restore because F is durable. -/
theorem finality_restore_preceq_F (X : FGBlock (Fin p.n)) :
    ∀ nd t, FGBlock.Preceq X nd.st.fg.F →
      FGBlock.Preceq X ((fgsa p c).restore ((fgsa p c).durable nd) t).st.fg.F := by
  intro nd t h
  change FGBlock.Preceq X (acRestart p nd.st t).fg.F
  rwa [acRestart_fg]

/-- A strict-before index witness gives acceptance across sleep and restore. -/
theorem finality_acceptsFinalBefore_of_idx
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)} {d : Time}
    (h : ∃ i ≤ rho.events.length,
      (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
      FGBlock.Preceq X (storeAt p c E rho i x).fg.F) :
    AcceptsFinalBefore p c E rho x X d :=
  (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs (fgsa_monoAlong_preceq_F p c X)
    (finality_restore_preceq_F p c X)).mpr h

/-- A later deadline preserves acceptance of durable finality. -/
theorem finality_acceptsFinalBefore_mono_deadline
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)}
    {d d' : Time} (hdd : d ≤ d') (h : AcceptsFinalBefore p c E rho x X d) :
    AcceptsFinalBefore p c E rho x X d' := by
  obtain ⟨i, hi, hbefore, hX⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx_restore hs (fgsa_monoAlong_preceq_F p c X)
      (finality_restore_preceq_F p c X)).mp h
  apply finality_acceptsFinalBefore_of_idx p c E rho hs
  refine ⟨i, hi, ?_, hX⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hbefore k hk
  exact ⟨e, he, ht.trans_le hdd⟩

/-- Acceptance of a descendant also accepts its ancestor at a later deadline. -/
theorem finality_acceptsFinalBefore_mono_ancestor
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X U : FGBlock (Fin p.n)}
    {d d' : Time} (hXU : FGBlock.Preceq X U) (hdd : d ≤ d')
    (h : AcceptsFinalBefore p c E rho x U d) : AcceptsFinalBefore p c E rho x X d' := by
  have hU := finality_acceptsFinalBefore_mono_deadline p c E rho hs hdd h
  exact KitFG.preceq_trans hXU hU

end AvailableChain.FGSA.Run
end
