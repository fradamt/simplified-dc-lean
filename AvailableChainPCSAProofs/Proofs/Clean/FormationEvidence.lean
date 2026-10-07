module
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! Body scope for Formation walks. Clean uses this local proof of body scope
without a dependency on the PC proof lane. -/

namespace AvailableChain.PCSA

private def FormationBodyScope {n : Nat} (B : Block → Prop) (st : State n) : Prop :=
  ∀ b ∈ st.base.blocks, B b

private theorem formation_grid_vote_scope {n : Nat} (q : GridCO.Params)
    (B : Block → Prop) (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : ∀ b ∈ v.blocks, B b) : ∀ b ∈ (GridCO.admitVote q v o).blocks, B b := by
  rw [GridCO.admitVote_blocks]
  exact h

private theorem formation_grid_proposal_scope {n : Nat} (q : GridCO.Params)
    (B : Block → Prop) (v : GridCO.State n .root) (o : GridCO.Wire n .root)
    (b : Block) (raw : List (GridCO.HeadWire n .root))
    (h : ∀ a ∈ v.blocks, B a) (hb : B b) :
    ∀ a ∈ (GridCO.admitProposal q v o b raw).blocks, B a := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> delta GridCO.admitProposal <;> dsimp only <;> split
  all_goals first
  | exact h
  | apply List.foldlRecOn (motive := fun acc : GridCO.State n .root => ∀ a ∈ acc.blocks, B a)
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h a ha
      · exact List.mem_singleton.mp ha ▸ hb
    · intro acc ha row _
      exact formation_grid_vote_scope q B acc _ ha

private theorem formation_normalize_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : FormationBodyScope B st) : FormationBodyScope B (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem formation_reconcile_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : FormationBodyScope B st) : FormationBodyScope B (reconcile st) := by
  apply formation_normalize_scope
  exact h

private theorem formation_collect_scope {n : Nat} (B : Block → Prop) (st : State n)
    (h : FormationBodyScope B st) : FormationBodyScope B (collectPCs st) := by
  change ∀ b ∈ (collectPCs st).base.blocks, B b
  rw [(collectPCs_frame st).2.1]
  exact h

private theorem formation_row_scope (p : Params) (B : Block → Prop) (st : State p.n)
    (a : RowWire p.n) (h : FormationBodyScope B st) :
    FormationBodyScope B (admitRow p st a) := by
  cases hd : a.decode? with
  | none => delta admitRow; rw [hd]; exact h
  | some val =>
    delta admitRow
    rw [hd]
    change FormationBodyScope B (if a ∈ st.rowPool then st else
      { st with rowPool := st.rowPool ++ [a] })
    split <;> exact h

private theorem formation_raw_ack_scope {n : Nat} (B : Block → Prop) (st : State n)
    (a : AckWire n) (h : FormationBodyScope B st) : FormationBodyScope B (poolAckRaw st a) := by
  change ∀ b ∈ (poolAckRaw st a).base.blocks, B b
  rw [(poolAckRaw_frame st a).2.2.1]
  exact h

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

private theorem formation_process_scope (p : Params) (B : Block → Prop) (st : State p.n)
    (o : Wire p.n) (h : FormationBodyScope B st)
    (ho : ∀ s N, o.decode = some (.block s N) →
      ∀ P, blockAccepted p st s N P = true → B N.erase) :
    FormationBodyScope B (process p st o) := by
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : FormationBodyScope B st) :
      FormationBodyScope B (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc ha a _ => formation_raw_ack_scope B acc a ha)
  have hr (st : State p.n) (as : List (RowWire p.n)) (h : FormationBodyScope B st) :
      FormationBodyScope B (as.foldl (admitRow p) st) :=
    List.foldlRecOn as (admitRow p) h (fun acc ha a _ => formation_row_scope p B acc a ha)
  cases hd : o.decode with
  | none => delta process; rw [hd]; exact h
  | some val =>
    cases val with
    | vote slot seat root =>
      delta process
      rw [hd]
      change FormationBodyScope B (admitHead p st slot seat root)
      exact formation_grid_vote_scope p.toParams.engine B st.base _ h
    | row seat body =>
      delta process
      rw [hd]
      change FormationBodyScope B (admitRow p st ⟨o.auth, body⟩)
      exact formation_row_scope p B st _ h
    | block slot N =>
      delta process
      rw [hd]
      change FormationBodyScope B (admitBlock p st slot N)
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => change FormationBodyScope B st; exact h
        | some P =>
          change FormationBodyScope B (if blockAccepted p st slot N P then
            formationAccepted p st slot N P else st)
          split
          · rename_i hAcc
            have hb := ho slot N hd P hAcc
            delta formationAccepted
            apply hr
            apply formation_collect_scope
            apply ha
            cases hc : N.pc <;> dsimp only <;> split_ifs <;>
              first
              | apply formation_reconcile_scope
                exact formation_grid_proposal_scope p.toParams.engine B st.base _ _ _ h hb
              | exact formation_grid_proposal_scope p.toParams.engine B st.base _ _ _ h hb
          · exact h
    | ack slot seat root =>
      delta process
      rw [hd]
      change FormationBodyScope B (admitAck p st ⟨o.auth, root⟩)
      delta admitAck
      apply formation_collect_scope
      cases he : AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n) with
      | none => delta poolAck; rw [he]; exact h
      | some val =>
        delta poolAck
        rw [he]
        rcases val with ⟨label, signer, target⟩
        change FormationBodyScope B (if st.slot p < label || !ackSlotOK st label target ||
          (⟨o.auth, root⟩ : AckWire p.n) ∈ st.ackPool then st else
          if 2 ≤ (seatAcks st label signer).length &&
            !decide (target ∈ seatAcks st label signer) then st else
          { st with ackPool := st.ackPool ++ [⟨o.auth, root⟩] })
        split_ifs <;> exact h
    | pc C =>
      delta process
      rw [hd]
      change FormationBodyScope B (admitPC st C)
      delta admitPC
      split
      · exact formation_collect_scope B _ (ha _ _ h)
      · exact h

/-- Accepted body predicates persist through every handler. -/
theorem pcsa_formation_process_body_scope (p : Params) (B : Block → Prop)
    (st : State p.n) (o : Wire p.n) (h : ∀ b ∈ st.base.blocks, B b)
    (ho : ∀ s N, o.decode = some (.block s N) →
      ∀ P, blockAccepted p st s N P = true → B N.erase) :
    ∀ b ∈ (process p st o).base.blocks, B b :=
  formation_process_scope p B st o h ho

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

private theorem formation_gate_scope (p : Params) {n : Nat} (B : Block → Prop)
    (st : State n) (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot)
    (h : FormationBodyScope B st) : FormationBodyScope B (gateFrom p a cs rank st s) := by
  cases hg : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none =>
    rw [gateFrom_def]
    dsimp only
    rw [hg]
    change FormationBodyScope B st
    exact h
  | some result =>
    rw [gateFrom_def]
    dsimp only
    rw [hg]
    change FormationBodyScope B (formationGateAccepted p st cs rank s result)
    delta formationGateAccepted
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn (motive := FormationBodyScope B)
      · exact h
      · intro acc ha b _
        apply List.foldlRecOn (motive := FormationBodyScope B)
        · exact ha
        · intro acc' ha' g _
          change ∀ C ∈ (writeLease acc' b g
            (GridCO.gateTime p.toParams.engine s + GridCO.lifetime p.toParams.engine)
            rank).base.blocks, B C
          rw [(writeLease_frame acc' b g _ rank).2.2.2.2.1]
          exact ha'

/-- Clock steps keep every stored body within its original scope. -/
theorem pcsa_formation_clock_body_scope (p : Params) (B : Block → Prop)
    (st : State p.n) (t : Time) (h : ∀ b ∈ st.base.blocks, B b) :
    ∀ b ∈ (clock p st t).base.blocks, B b := by
  have hc : FormationBodyScope B (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply formation_normalize_scope
    split
    · exact hc
    · exact formation_gate_scope p B _ _ _ _ _ hc
  · exact hc

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

private theorem formation_named_refl (N : NamedProposal p.n) : NamedProposal.Preceq N N := by
  cases N with
  | genesis => rfl
  | node P s root body raw support rows pc =>
    change (decide (NamedProposal.node P s root body raw support rows pc =
      NamedProposal.node P s root body raw support rows pc) ||
      NamedProposal.preceq (.node P s root body raw support rows pc) P) = true
    exact Bool.or_eq_true_iff.mpr (Or.inl (decide_eq_true rfl))

private theorem formation_decode_proposal (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : o.payload = .proposal N := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta toWire toAuth Wire.decode at h <;> cases h
  | seat l i =>
    cases l with
    | prop k =>
      cases payload <;> delta toWire toAuth Wire.decode at h
      all_goals cases h <;> rfl
    | base l =>
      cases l <;> cases payload <;> delta toWire toAuth Wire.decode Label.ackSlot? at h <;> cases h

/-- Every stored body in an honest run state is in the named collision scope. -/
theorem pcsa_formation_body_scope (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (x : V) (hx : x ∈ rho.honest) :
    ∀ b ∈ (V2.D.Run.stateBefore E rho j x).st.base.blocks, RootBlockInRun p c E rho b := by
  have hg : RootBlockInRun p c E rho .genesis := by
    refine ⟨.genesis, ⟨.genesis, Or.inr ⟨x, hx, 0, ?_⟩, formation_named_refl _⟩, rfl⟩
    change (NamedProposal.genesis : NamedProposal p.n) ∈ [NamedProposal.genesis]
    exact List.mem_singleton_self _
  have hz : FormationBodyScope (RootBlockInRun p c E rho) (initial p.n) := by
    change ∀ b ∈ [Block.genesis], RootBlockInRun p c E rho b
    intro b hb
    exact List.mem_singleton.mp hb ▸ hg
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => FormationBodyScope (RootBlockInRun p c E rho) nd.st)
    (Nat.zero_le j) x ?_ hz
  intro k e _ _ he hn h
  cases e with
  | restart y t =>
    change y = x at hn
    subst y
    change FormationBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    exact hz
  | tick y t =>
    change y = x at hn
    subst y
    change FormationBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hf : FormationBodyScope (RootBlockInRun p c E rho)
        (clock p (V2.D.Run.stateBefore E rho k x).st t) :=
      pcsa_formation_clock_body_scope p _ _ t h
    exact ht.symm ▸ hf
  | deliver y o t =>
    change y = x at hn
    subst y
    change FormationBodyScope _ (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st
    rw [Function.update_self]
    apply formation_process_scope p _ _ (toWire p o) h
    intro s N hd _ _
    exact ⟨N, ⟨N, Or.inl ⟨x, o, t, List.mem_of_getElem? he,
      formation_decode_proposal o s N hd⟩, formation_named_refl N⟩, rfl⟩

/-- The collision premise identifies equal roots of scoped blocks. -/
theorem pcsa_formation_scoped_root_eq (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : NamedRootCollisionFree p c E rho)
    (A B : Block) (hA : RootBlockInRun p c E rho A) (hB : RootBlockInRun p c E rho B)
    (he : A.root = B.root) : A = B := by
  obtain ⟨N, hN, rfl⟩ := hA
  obtain ⟨M, hM, rfl⟩ := hB
  have hr : N.root = M.root := by
    have er (P : NamedProposal p.n) : P.erase.root = P.root := by cases P <;> rfl
    simpa only [er] using he
  have hn := h.root_injective N M hN hM N M
    (Or.inl (formation_named_refl N)) (Or.inr (formation_named_refl M)) hr
  exact congrArg NamedProposal.erase hn

end AvailableChain.PCSA.Run
end
