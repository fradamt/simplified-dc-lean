module
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalReceipt

public section

/-! C6 ProposalStore: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem proposal_store_norm (st : State n) :
    (normalizeS st).proposals = st.proposals := by
  delta normalizeS
  split <;> rfl
private theorem proposal_store_reconcile (st : State n) :
    (reconcile st).proposals = st.proposals := by
  delta reconcile
  rw [proposal_store_norm]
private theorem proposal_store_collect (st : State n) :
    (collectPCs st).proposals = st.proposals := by
  apply collectPCs_preserves State.proposals
  intro st C
  rw [installPC_def]
  split <;> rfl
private theorem proposal_store_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
private theorem proposal_store_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
private theorem proposal_store_rows (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).proposals = st.proposals := by
  apply List.foldlRecOn (motive := fun acc : State p.n => acc.proposals = st.proposals)
  · rfl
  · intro acc hh a _
    exact (proposal_store_row p acc a).trans hh
private theorem proposal_store_raws (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).proposals = st.proposals := by
  apply List.foldlRecOn (motive := fun acc : State n => acc.proposals = st.proposals)
  · rfl
  · intro acc hh a _
    exact (proposal_store_raw acc a).trans hh
/-- A passed proposal admission appends exactly its full signed wire. -/
theorem pcsa_admitBlock_proposals (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (hn : namedParentHeld st N = true) (hp : parentFG st N.erase = some P)
    (ha : blockAccepted p st s N P = true) :
    (admitBlock p st s N).proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩] := by
  delta admitBlock
  rw [hn]
  change (match parentFG st N.erase with
    | none => st
    | some P => if blockAccepted p st s N P then _ else st).proposals = _
  rw [hp]
  change (if blockAccepted p st s N P then _ else st).proposals = _
  rw [ite_eq_left ha]
  rw [proposal_store_rows, proposal_store_collect, proposal_store_raws]
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st2 := match N.pc with
    | none => st1
    | some C => if pcValid st1 C && !st1.pcs.any
        (fun old => old.slot == C.slot && old.target == C.target)
      then deleteConflictingLeases st1 C else st1
  let st3 : State p.n := { st2 with
    fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  change (if st3.fg.F = st.fg.F then st3 else reconcile st3).proposals = _
  split
  · rfl
  · exact proposal_store_reconcile st3
/-- Every delivery preserves the exact proposal pool. -/
theorem pcsa_process_proposals_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.proposals ⊆ (process p st o).proposals := by
  delta process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body => rw [proposal_store_row]
    | ack s i r =>
      change st.proposals ⊆ (collectPCs (poolAck p st _)).proposals
      rw [proposal_store_collect]
      delta poolAck
      cases AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact List.Subset.refl _
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact List.Subset.refl _
        · split <;> exact List.Subset.refl _
    | pc C =>
      dsimp only
      delta admitPC
      split
      · rw [proposal_store_collect, proposal_store_raws]
      · exact List.Subset.refl _
    | block s N =>
      dsimp only
      by_cases hn : namedParentHeld st N = true
      · cases hp : parentFG st N.erase with
        | none =>
          delta admitBlock
          rw [hn, hp]
          exact List.Subset.refl _
        | some P =>
          by_cases ha : blockAccepted p st s N P = true
          · rw [pcsa_admitBlock_proposals p st s N P hn hp ha]
            exact fun _ hm => List.mem_append_left _ hm
          · delta admitBlock
            rw [hn, hp]
            change st.proposals ⊆ (if blockAccepted p st s N P then _ else st).proposals
            rw [ite_eq_right ha]
      · have hf : namedParentHeld st N = false := Bool.eq_false_iff.mpr hn
        delta admitBlock
        rw [hf]
        exact List.Subset.refl _
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- Without restarts, an exact admitted proposal remains in every later local pool. -/
theorem pcsa_proposals_stateBefore_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (a k : Nat) (x : V) (hak : a ≤ k) :
    (V2.D.Run.stateBefore E rho a x).st.proposals ⊆ (V2.D.Run.stateBefore E rho k x).st.proposals
      := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho a x).st.proposals ⊆ nd.st.proposals)
    hak x ?_ (List.Subset.refl _)
  intro j e _ _ he hy ih
  cases e with
  | restart y t => exact (hn j y t he).elim
  | tick y t =>
    change y = x at hy
    subst y
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t
    rw [ht, pcsa_clock_proposals]
    exact ih
  | deliver y o t =>
    change y = x at hy
    subst y
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals
    rw [Function.update_self]
    exact List.Subset.trans ih (pcsa_process_proposals_mono p _ (toWire p o))
end AvailableChain.PCSA.Run

end
