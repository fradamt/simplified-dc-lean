module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainPCSAProofs.Proofs.Shared.TreeReceipt
public import AvailableChainFGSA.Proofs.WindowStore
public import AvailableChainFGSA.Proofs.HeadDomain

public section

/-! Stored tree correspondence for Formation receipts and source selection.
Reachable stores keep the cumulative resolution domain unset. -/

namespace AvailableChain.PCSA
open AvailableChain.SimplexFG

/-- A held PC target is frame-active in a reachable stage-1 store. -/
theorem pcsa_formation_frame_active_of_target (p : Params) (st : State p.n) (C : PC p.n)
    (hReach : Reachable p st) (hFrame : Run.FrameVacuous p st)
    (hTarget : C.target ∈ st.base.blocks) : frameActive p st C = true := by
  rw [frameActive_def, pcsa_fullTree_of_frame p st hFrame]
  exact decide_eq_true ((pcsa_tree_correspondence p st hReach C.target).mp hTarget)

private theorem headDomain_installPC (st : State n) (c : PC n) :
    (installPC st c).base.headDomain = st.base.headDomain := by
  rw [installPC_def]
  split
  · rfl
  · rfl

private theorem headDomain_collect (st : State n) :
    (collectPCs st).base.headDomain = st.base.headDomain :=
  collectPCs_preserves (fun s => s.base.headDomain) headDomain_installPC st

private theorem headDomain_raws (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base.headDomain = st.base.headDomain := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, (poolAckRaw_frame st a).2.2.1]

private theorem headDomain_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.headDomain = st.base.headDomain := by
  delta admitRow
  cases a.decode? <;> dsimp only
  split <;> rfl

private theorem headDomain_rows (p : Params) (st : State p.n) (as : List (RowWire p.n)) :
    (as.foldl (admitRow p) st).base.headDomain = st.base.headDomain := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, headDomain_row]

private theorem headDomain_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.headDomain = st.base.headDomain := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some val =>
    rcases val with ⟨s, i, r⟩
    dsimp only
    split_ifs <;> rfl

private theorem headDomain_process (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.headDomain = st.base.headDomain := by
  cases hd : o.decode with
  | none => delta process; rw [hd]
  | some d =>
    cases d with
    | vote s i r =>
      delta process
      rw [hd]
      exact FGSA.admitVote_headDomain _ _ _
    | row i body => delta process; rw [hd, headDomain_row]
    | ack s i r =>
      delta process
      rw [hd]
      change (collectPCs (poolAck p st ⟨o.auth, r⟩)).base.headDomain = _
      rw [headDomain_collect, headDomain_pool]
    | pc C =>
      delta process
      rw [hd]
      change (admitPC st C).base.headDomain = _
      delta admitPC
      split
      · rw [headDomain_collect, headDomain_raws]
      · rfl
    | block s N =>
      delta process
      rw [hd]
      change (admitBlock p st s N).base.headDomain = _
      delta admitBlock
      split
      · rfl
      · cases parentFG st N.erase with
        | none => rfl
        | some B =>
          dsimp only
          split
          · rw [headDomain_rows, headDomain_collect, headDomain_raws]
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | exact FGSA.admitProposal_headDomain _ _ _ _ _
              | (delta reconcile normalizeS; dsimp only; split_ifs <;>
                  exact FGSA.admitProposal_headDomain _ _ _ _ _)
          · rfl

private theorem headDomain_gate (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.headDomain = st.base.headDomain := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some result =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State p.n => acc.base.headDomain = st.base.headDomain)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc' : State p.n => acc'.base.headDomain = st.base.headDomain)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem headDomain_clock (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).base.headDomain = st.base.headDomain := by
  have hp : (clockPre p st t).base.headDomain = st.base.headDomain := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    delta normalizeS
    split <;> split <;>
      first
      | exact hp
      | (rw [headDomain_gate]; exact hp)
  · exact hp

/-- Every reachable PC-SA store keeps the cumulative resolution domain unset. -/
theorem pcsa_reachable_headDomain_none (p : Params) (st : State p.n)
    (h : Reachable p st) : st.base.headDomain = none := by
  induction h with
  | init => rfl
  | tick t _ ih => rw [headDomain_clock, ih]
  | deliver o _ ih => rw [headDomain_process, ih]

end AvailableChain.PCSA
end
