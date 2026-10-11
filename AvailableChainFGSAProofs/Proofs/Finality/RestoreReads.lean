module
public import AvailableChainFGSAProofs.Proofs.Shared.RowReads -- shake: keep (source declarations)

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

/-- Durable rows remain held at a later proposal read across restore. -/
theorem finality_heldBefore_at_proposal (hs : V2.D.ScheduleWellFormed E rho)
    {s : Slot} {a : RowWire p.n} {d : Time} {st : State p.n}
    (hst : proposalStateAt p c E rho s = some st)
    (hheld : HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) s) a d)
    (hd : d ≤ SA.proposalTime p.toParams s) : heldAtProposal p c E rho s a := by
  refine ⟨st, hst, ?_⟩
  change (postClock E rho (V2.D.proposerOf rho (fgsaInterface p c) s)
    (V2.D.proposalTime (fgsaInterface p c) s)).map (·.st) = some st at hst
  rw [postClock_def, preTick_def] at hst
  cases hj : V2.D.Run.tickIdx? rho (V2.D.proposerOf rho (fgsaInterface p c) s)
      (V2.D.proposalTime (fgsaInterface p c) s) with
  | none => rw [hj] at hst; cases hst
  | some k =>
    rw [hj] at hst
    have hk := V2.D.Run.tickIdx?_spec hj
    have hst' : ((fgsa p c).clock (V2.D.Run.stateBefore E rho k
        (V2.D.proposerOf rho (fgsaInterface p c) s))
        (V2.D.proposalTime (fgsaInterface p c) s)).st = st := Option.some.inj hst
    have hik : V2.D.Run.idxBefore rho d ≤ k := by
      by_contra hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk d).mp (Nat.lt_of_not_ge hn)
      exact (not_lt.mpr hd) ht
    change rowHeld p (V2.D.Run.stateBeforeTime E rho d
      (V2.D.proposerOf rho (fgsaInterface p c) s)).st a at hheld
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho d hs] at hheld
    have hcumul := fgsa_store_durable p c E rho hik
      (V2.D.proposerOf rho (fgsaInterface p c) s)
    rw [← hst']
    rcases hheld with hp | hb
    · left
      change a ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _).rowPool
      rw [clock_rowPool]
      exact hcumul.2.2.2.subset hp
    · right
      change a ∈ allBlockRows _ at hb
      change a ∈ allBlockRows (FGSA.clock p (V2.D.Run.stateBefore E rho k _).st _)
      unfold allBlockRows at hb ⊢
      rw [clock_proposals]
      obtain ⟨xs, hxs, ha⟩ := List.mem_flatten.mp hb
      obtain ⟨w, hw, hdec⟩ := List.mem_filterMap.mp hxs
      exact List.mem_flatten.mpr ⟨xs,
        List.mem_filterMap.mpr ⟨w, hcumul.2.2.1.subset hw, hdec⟩, ha⟩

end AvailableChain.FGSA.Run
end
