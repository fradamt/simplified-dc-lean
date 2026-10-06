module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationEvidence
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame
public import AvailableChainFGSA.Proofs.Admission
public import AvailableChainFGSA.Proofs.WindowStore

public section

/-! Stored tree correspondence for Formation receipts and source selection. -/

namespace AvailableChain.PCSA
open AvailableChain.SimplexFG

private def FormationTreeCorr {n : Nat} (st : State n) : Prop :=
  ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b

private theorem formation_fg_erasure {n : Nat} (P : FGBlock (Fin n)) (b : Block)
    (rows : List (RowWire n)) (hne : b ≠ .genesis) (hp : eraseFG P = b.parent)
    (hr : rowsOk b rows = true) : eraseFG (fgBlock P b rows) = b := by
  cases b with
  | genesis => exact (hne rfl).elim
  | node parent slot root body =>
    have hb : body = packBody (appOf body) rows := beq_iff_eq.mp hr
    change Block.node (eraseFG P) slot root (packBody (appOf body) rows) = _
    rw [hp, ← hb]
    rfl

private theorem formation_accepted_trees (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : FGBlock (Fin p.n))
    (hTree : FormationTreeCorr st) (hParent : parentFG st N.erase = some P)
    (hAcc : blockAccepted p st s N P = true) :
    FormationTreeCorr { st with
      base := GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
      fg := FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows) } := by
  have hLook : P ∈ st.fg.TF ∧ eraseFG P = N.erase.parent := by
    have hm := FGSA.pickPair_some_spec st.fg.TF _ hParent
    exact ⟨hm.1, of_decide_eq_true hm.2⟩
  have hf := hAcc
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at hf
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hGen, hSlot⟩, hFresh⟩, hF⟩, hPS⟩, hS⟩, _⟩, _⟩, hContent⟩ := hf
  have hRows : rowsOk N.erase N.rows = true := by
    change (_ && _) = true at hContent
    exact (Bool.and_eq_true_iff.mp hContent).1
  have hErase := formation_fg_erasure P N.erase N.rows hGen hLook.2 hRows
  have hNot : N.erase ∉ st.base.blocks := by
    intro hb
    obtain ⟨B, hB, he⟩ := (hTree _).mp hb
    apply hFresh
    exact ⟨B, hB, by rw [← he]; cases B <;> rfl⟩
  have hBase := FGSA.admitProposal_of_accept p.toParams.engine st.base s
    (.proposal N.erase (N.raw.map baseHead) (N.support.map baseHead)) N.erase
    (N.raw.map baseHead) hSlot ((hTree _).mpr ⟨P, hLook.1, hLook.2⟩)
    hNot hPS hS
  have hBlocks := (FGSA.foldVotes_fields p.toParams.engine (N.raw.map baseHead)
    { st.base with
      blocks := st.base.blocks ++ [N.erase]
      blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
      proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }).1
  have hBaseBlocks : (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks =
      st.base.blocks ++ [N.erase] :=
    (congrArg (fun v : GridCO.State p.n .root => v.blocks) hBase).trans hBlocks
  have hFG : (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF =
      insert (fgBlock P N.erase N.rows) st.fg.TF := by
    rw [FGSA.Window.window_on_block_of_accepted p p.K_W st.fg _]
    · exact FGSA.Window.window_update_finality_TF p p.K_W _ _
    · simp only [not_or, Bool.not_eq_false, not_le]
      refine ⟨?_, fun hm => hm hLook.1, hF, ?_⟩
      · intro hm
        apply hFresh
        refine ⟨fgBlock P N.erase N.rows, hm, ?_⟩
        rw [← hErase]
        cases N.erase <;> rfl
      · have hs : (eraseFG P).slot = P.slot := by cases P <;> rfl
        change P.slot < N.erase.slot
        rw [← hs, hLook.2]
        exact hPS
  change ∀ b, b ∈ (GridCO.admitProposal p.toParams.engine st.base
    (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks ↔
    ∃ B ∈ (FGSA.Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)).TF, eraseFG B = b
  rw [hBaseBlocks, hFG]
  intro b
  rw [List.mem_append, List.mem_singleton]
  constructor
  · rintro (hb | rfl)
    · obtain ⟨B, hB, he⟩ := (hTree b).mp hb
      exact ⟨B, Finset.mem_insert_of_mem hB, he⟩
    · exact ⟨_, Finset.mem_insert_self _ _, hErase⟩
  · rintro ⟨B, hB, he⟩
    rcases Finset.mem_insert.mp hB with hB | hB
    · subst B
      exact Or.inr (he.symm.trans hErase)
    · exact Or.inl ((hTree b).mpr ⟨B, hB, he⟩)

private theorem formation_normalize_tree {n : Nat} (st : State n) (h : FormationTreeCorr st) :
    FormationTreeCorr (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem formation_reconcile_tree {n : Nat} (st : State n) (h : FormationTreeCorr st) :
    FormationTreeCorr (reconcile st) := by
  apply formation_normalize_tree
  exact h

private theorem formation_collect_tree {n : Nat} (st : State n) (h : FormationTreeCorr st) :
    FormationTreeCorr (collectPCs st) := by
  change ∀ b, b ∈ (collectPCs st).base.blocks ↔ ∃ B ∈ (collectPCs st).fg.TF, eraseFG B = b
  rw [(collectPCs_frame st).2.1, (collectPCs_frame st).2.2.2.2]
  exact h

private theorem formation_row_tree (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : FormationTreeCorr st) : FormationTreeCorr (admitRow p st a) := by
  cases hd : a.decode? with
  | none => delta admitRow; rw [hd]; exact h
  | some val =>
    delta admitRow
    rw [hd]
    change FormationTreeCorr (if a ∈ st.rowPool then st else
      { st with rowPool := st.rowPool ++ [a] })
    split <;> exact h

private theorem formation_raw_ack_tree {n : Nat} (st : State n) (a : AckWire n)
    (h : FormationTreeCorr st) : FormationTreeCorr (poolAckRaw st a) := by
  change ∀ b, b ∈ (poolAckRaw st a).base.blocks ↔ ∃ B ∈ (poolAckRaw st a).fg.TF, eraseFG B = b
  rw [(poolAckRaw_frame st a).2.2.1, (poolAckRaw_frame st a).2.2.2]
  exact h

private theorem formation_vote_blocks {n : Nat} (q : GridCO.Params)
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    (GridCO.admitVote q st o).blocks = st.blocks := by
  exact GridCO.admitVote_blocks q st o

private abbrev formationAccepted (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st1 := match N.pc with
    | none => st1
    | some C => if pcValid st1 C &&
        !st1.pcs.any (fun old => old.slot == C.slot && old.target == C.target)
      then deleteConflictingLeases st1 C else st1
  let st1 := { st1 with
    fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
  N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st2))

private theorem formation_process_tree (p : Params) (st : State p.n) (o : Wire p.n)
    (h : FormationTreeCorr st) : FormationTreeCorr (process p st o) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : FormationTreeCorr st) :
      FormationTreeCorr (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => formation_raw_ack_tree acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : FormationTreeCorr st) :
      FormationTreeCorr (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => formation_row_tree p acc a ha)
  cases hd : o.decode with
  | none => delta process; rw [hd]; exact h
  | some val =>
    cases val with
    | vote slot seat root =>
      delta process
      rw [hd]
      change FormationTreeCorr (admitHead p st slot seat root)
      delta admitHead
      change ∀ b, b ∈ (GridCO.admitVote p.toParams.engine st.base _).blocks ↔
        ∃ B ∈ st.fg.TF, eraseFG B = b
      rw [formation_vote_blocks]
      exact h
    | row seat body =>
      delta process
      rw [hd]
      change FormationTreeCorr (admitRow p st ⟨o.auth, body⟩)
      exact formation_row_tree p st _ h
    | block slot N =>
      delta process
      rw [hd]
      change FormationTreeCorr (admitBlock p st slot N)
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => change FormationTreeCorr st; exact h
        | some P =>
          change FormationTreeCorr (if blockAccepted p st slot N P then
            formationAccepted p st slot N P else st)
          split
          · rename_i hAcc
            delta formationAccepted
            apply hr
            apply formation_collect_tree
            apply ha
            have hi := formation_accepted_trees p st slot N P h hp hAcc
            cases hc : N.pc <;> dsimp only <;> split_ifs <;>
              first | (apply formation_reconcile_tree; exact hi) | exact hi
          · exact h
    | ack slot seat root =>
      delta process
      rw [hd]
      change FormationTreeCorr (admitAck p st ⟨o.auth, root⟩)
      delta admitAck
      apply formation_collect_tree
      cases he : AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n) with
      | none => delta poolAck; rw [he]; exact h
      | some val =>
        delta poolAck
        rw [he]
        rcases val with ⟨label, signer, target⟩
        change FormationTreeCorr (if st.slot p < label || !ackSlotOK st label target ||
          (⟨o.auth, root⟩ : AckWire p.n) ∈ st.ackPool then st else
          if 2 ≤ (seatAcks st label signer).length &&
            !decide (target ∈ seatAcks st label signer) then st else
          { st with ackPool := st.ackPool ++ [⟨o.auth, root⟩] })
        split_ifs <;> exact h
    | pc C =>
      delta process
      rw [hd]
      change FormationTreeCorr (admitPC st C)
      delta admitPC
      split
      · exact formation_collect_tree _ (ha _ _ h)
      · exact h

private abbrev formationGateAccepted (p : Params) {n : Nat} (st : State n)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (result : Block) : State n :=
  let v := actView st
  let q := p.toParams.engine
  let st1 : State n := { st with base := { st.base with
    goldfishRecord := GridCO.advance v.goldfishRecord result
    genuine := @GridCO.recordGenuine GridCO.slowLeasePolicy n .root v s (some result) } }
  if st1.base.obligations.any (fun row => st1.base.now < row.2.2 &&
      !Block.compatible row.1 result) then st1 else
    let st2 := { st1 with base := { st1.base with
      stableRecord := GridCO.advance st1.base.stableRecord result } }
    let prefixes := v.blocks.filter (fun b => b != .genesis && Block.preceq b result &&
      leaseWriteOK cs rank b)
    prefixes.foldl (fun acc b => (slowLevels p (actView acc) s b).foldl
      (fun acc g => writeLease acc b g (GridCO.gateTime q s + GridCO.lifetime q) rank) acc) st2

private theorem formation_gate_tree (p : Params) {n : Nat} (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (h : FormationTreeCorr st) :
    FormationTreeCorr (gateFrom p a cs rank st s) := by
  cases hg : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none =>
    rw [gateFrom_def]
    dsimp only
    rw [hg]
    change FormationTreeCorr st
    exact h
  | some result =>
    rw [gateFrom_def]
    dsimp only
    rw [hg]
    change FormationTreeCorr (formationGateAccepted p st cs rank s result)
    delta formationGateAccepted
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn (motive := FormationTreeCorr)
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn (motive := FormationTreeCorr)
        · exact ha
        · intro acc' ha' g _
          change ∀ C, C ∈ (writeLease acc' b g
            (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine)
            rank).base.blocks ↔ ∃ B ∈ (writeLease acc' b g
              (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine) rank).fg.TF,
                eraseFG B = C
          rw [(writeLease_frame acc' b g _ rank).2.2.2.2.1,
            (writeLease_frame acc' b g _ rank).2.2.2.2.2]
          exact ha'

private theorem formation_clock_tree (p : Params) (st : State p.n) (t : Time)
    (h : FormationTreeCorr st) : FormationTreeCorr (clock p st t) := by
  have hc : FormationTreeCorr (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply formation_normalize_tree
    split
    · exact hc
    · exact formation_gate_tree p _ _ _ _ _ hc
  · exact hc

/-- Every reachable store has the same base and FG block domain. -/
theorem pcsa_formation_tree_correspondence (p : Params) (st : State p.n)
    (h : Reachable p st) : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b := by
  change FormationTreeCorr st
  induction h with
  | init =>
    change ∀ b, b ∈ [Block.genesis] ↔ ∃ B ∈ ({FGBlock.genesis} : Finset _), eraseFG B = b
    simp only [List.mem_singleton, Finset.mem_singleton]
    intro b
    constructor
    · intro hb; subst b; exact ⟨_, rfl, rfl⟩
    · rintro ⟨B, rfl, he⟩; exact he.symm
  | tick t _ ih => exact formation_clock_tree p _ t ih
  | deliver o _ ih => exact formation_process_tree p _ o ih

/-- In stage 1 the full frame filter retains every stored FG block. -/
theorem pcsa_formation_fullTree_of_frame (p : Params) (st : State p.n)
    (h : Run.FrameVacuous p st) : fullTree p st = st.fg.TF := by
  apply Finset.ext
  intro B
  rw [fullTree_def]
  change B ∈ KitFG.filteredFromView (FGSA.heightView p) (controls p st) st.fg.TF ↔ B ∈ st.fg.TF
  rw [KitFG.mem_filteredFromView]
  constructor
  · exact fun hb => hb.1
  · intro hb
    have hF : (controls p st).F = FGBlock.genesis := h.1
    rw [hF, h.2.1, h.2.2]
    exact ⟨hb, KitFG.genesis_preceq B, KitFG.genesis_preceq B,
      B, hb, KitFG.preceq_refl B, Nat.zero_le _⟩

/-- A held PC target is frame-active in a reachable stage-1 store. -/
theorem pcsa_formation_frame_active_of_target (p : Params) (st : State p.n) (C : PC p.n)
    (hReach : Reachable p st) (hFrame : Run.FrameVacuous p st)
    (hTarget : C.target ∈ st.base.blocks) : frameActive p st C = true := by
  rw [frameActive_def, pcsa_formation_fullTree_of_frame p st hFrame]
  exact decide_eq_true ((pcsa_formation_tree_correspondence p st hReach C.target).mp hTarget)

end AvailableChain.PCSA
end
