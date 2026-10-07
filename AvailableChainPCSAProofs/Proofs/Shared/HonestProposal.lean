module
public import AvailableChainPCSAProofs.Proofs.Shared.BodyRelay
public import AvailableChainPCSAProofs.Proofs.Shared.Proposal
public import AvailableChainPCSAProofs.Proofs.Shared.Roots
public import AvailableChainPCSAProofs.Proofs.Shared.PCViews
public import AvailableChainPCSAProofs.Proofs.Shared.StageRun

public section

/-! Receipt of an honest proposal (pcsa34-r4.3b §5.3, §5.6.1), shared by the
lanes. The rows of an honest proposal pass R6 against every FG lift of its
parent, so no receiver excludes it in stage 1. Under a `DeliveryWithinOn`
premise each honest receiver admits it and holds its exact signed wire; its
carried PC is valid there. The proposal-pool helpers are private until the
Foundations proposal lemmas land on main. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem honest_norm_proposals (st : State n) :
    (normalizeS st).proposals = st.proposals := by
  delta normalizeS
  split <;> rfl

private theorem honest_reconcile_proposals (st : State n) :
    (reconcile st).proposals = st.proposals := by
  delta reconcile
  rw [honest_norm_proposals]

private theorem honest_collect_proposals (st : State n) :
    (collectPCs st).proposals = st.proposals := by
  apply collectPCs_preserves State.proposals
  intro st C
  rw [installPC_def]
  split <;> rfl

private theorem honest_raw_proposals (st : State n) (a : AckWire n) :
    (poolAckRaw st a).proposals = st.proposals := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem honest_row_proposals (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).proposals = st.proposals := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl

private theorem honest_rows_proposals (p : Params) (st : State p.n)
    (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).proposals = st.proposals := by
  apply List.foldlRecOn (motive := fun acc : State p.n => acc.proposals = st.proposals)
  · rfl
  · intro acc hh a _
    exact (honest_row_proposals p acc a).trans hh

private theorem honest_raws_proposals (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).proposals = st.proposals := by
  apply List.foldlRecOn (motive := fun acc : State n => acc.proposals = st.proposals)
  · rfl
  · intro acc hh a _
    exact (honest_raw_proposals acc a).trans hh

private theorem honest_gate_proposals (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).proposals = st.proposals := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => rfl
  | some X =>
    dsimp only
    split
    · rfl
    · apply List.foldlRecOn
        (motive := fun acc : State n => acc.proposals = st.proposals)
      · rfl
      · intro acc ha b _
        apply List.foldlRecOn
          (motive := fun acc : State n => acc.proposals = st.proposals)
        · exact ha
        · intro acc' ha' g _
          exact ha'

private theorem honest_clock_proposals (p : Params) (st : State p.n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  have hp : (clockPre p st t).proposals = st.proposals := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> rfl
  delta clock
  dsimp only
  split
  · rw [gateStep_def, honest_norm_proposals]
    split
    · exact hp
    · rw [honest_gate_proposals]
      exact hp
  · exact hp

private theorem honest_admitBlock_proposals (p : Params) (st : State p.n) (s : Slot)
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
  rw [honest_rows_proposals, honest_collect_proposals, honest_raws_proposals]
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
  · exact honest_reconcile_proposals st3

private theorem honest_process_proposals_mono (p : Params) (st : State p.n) (o : Wire p.n) :
    st.proposals ⊆ (process p st o).proposals := by
  delta process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r => exact List.Subset.refl _
    | row i body => rw [honest_row_proposals]
    | ack s i r =>
      change st.proposals ⊆ (collectPCs (poolAck p st _)).proposals
      rw [honest_collect_proposals]
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
      · rw [honest_collect_proposals, honest_raws_proposals]
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
          · rw [honest_admitBlock_proposals p st s N P hn hp ha]
            exact fun _ hm => List.mem_append_left _ hm
          · delta admitBlock
            rw [hn, hp]
            change st.proposals ⊆ (if blockAccepted p st s N P then _ else st).proposals
            rw [ite_eq_right ha]
      · have hf : namedParentHeld st N = false := Bool.eq_false_iff.mpr hn
        delta admitBlock
        rw [hf]
        exact List.Subset.refl _

/-- R6 from the construction: the rows of a proposal built at the current slot
are valid for every FG lift of its parent. -/
theorem pcsa_propose_rows_valid (p : Params) (st : State p.n) (s app : Nat)
    (N : NamedProposal p.n)
    (h : (propose p st s).map (Run.withApp p app) = some (.proposal N))
    (hs : st.slot p = s) (Q : SimplexFG.FGBlock (Fin p.n))
    (hQ : eraseFG Q = N.erase.parent) :
    rowsValidForParent p Q N.slot N.rows = true := by
  have hpar := (pcsa_propose_parent p st s app N h).2.1
  obtain ⟨M, hM, hN⟩ := Option.map_eq_some_iff.mp h
  delta propose at hM
  split at hM
  · cases hM
  · obtain ⟨P, _, hMsg⟩ := Option.map_eq_some_iff.mp hM
    subst M
    change Msg.proposal (namedProposal p P s app _ _ _ _) = Msg.proposal N at hN
    have he := Msg.proposal.inj hN
    subst N
    rw [hpar] at hQ
    change rowsValidForParent p Q s (proposalRows p st
      (getHead p st (proposerPC p st) (proposerVotes st s) (proposerSupport st s))) = true
    delta proposalRows proposalRowsCore
    dsimp only
    split
    · rfl
    · rename_i P0 hP0
      have hl := FGSA.pickPair_some_spec st.fg.TF _ hP0
      have hQP : Q = P0 := by
        apply FGSA.eraseFG_injective
        rw [← pcsa_eraseFG_eq, ← pcsa_eraseFG_eq]
        exact hQ.trans (of_decide_eq_true hl.2).symm
      subst Q
      delta rowsValidForParent
      rw [hs]
      apply List.all_eq_true.mpr
      intro a ha
      exact (Bool.and_eq_true_iff.mp (List.mem_filter.mp ha).2).1

/-- An accepted proposal carries a well-formed PC. -/
theorem pcsa_accepted_pc_wellFormed (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (h : blockAccepted p st s N P = true) : (N.pc.map PC.wellFormed).getD true = true := by
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- In the genesis frame, a proposal whose rows pass R6 against every FG lift
of its parent is never excluded. -/
theorem pcsa_rows_valid_not_excluded (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (hf : st.fg.F = .genesis)
    (hv : ∀ Q : SimplexFG.FGBlock (Fin p.n), eraseFG Q = N.erase.parent →
      rowsValidForParent p Q N.slot N.rows = true) :
    Run.excludesS p st (Run.ofWire p ⟨.proposer s, .proposal N⟩) = false := by
  have hb : blockExcluded st N.erase = false := by
    change (!Block.compatible N.erase (eraseFG st.fg.F)) = false
    rw [hf]
    change (!Block.compatible N.erase .genesis) = false
    have hg : Block.compatible N.erase .genesis = true :=
      Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))
    rw [hg]
    rfl
  change (blockExcluded st N.erase || Run.invalidForParent p st N) = false
  rw [hb, Bool.false_or]
  delta Run.invalidForParent
  split
  · rfl
  · cases hq : parentFG st N.erase with
    | none => rfl
    | some Q =>
      have hl := FGSA.pickPair_some_spec st.fg.TF _ hq
      dsimp only
      rw [hv Q (of_decide_eq_true hl.2)]
      rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- An honest emitted proposal is the proposal built at its tick state. -/
theorem pcsa_emitted_propose (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (x : V) (t : Time) (k : Nat)
    (hk : rho.events[k]? = some (.tick x t))
    (ho : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho k) :
    t = SA.proposalTime p.toParams s ∧ ∃ app,
      (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
        (withApp p app) = some (.proposal N) := by
  rw [(V2.D.Run.step_tick_eq E rho hk).2] at ho
  obtain ⟨_, _, d, hl, ht, ha⟩ :=
    (V2.D.Engine.mem_tick_seat_iff E rho _ x t (.prop s) ⟨0, Nat.one_pos⟩
      (.proposal N)).mp ho
  obtain rfl := (pcsa_signLabel_prop d s).mp hl
  cases m <;>
    change (propose p (clock p (V2.D.Run.stateBefore E rho k x).st t) s).map
      (withApp p (c.app (rho.input x t))) = some (.proposal N) at ha
  all_goals exact ⟨ht.symm, _, ha⟩

omit [DecidableEq V] in
/-- The clock at `t_s` reads slot `s`. -/
theorem pcsa_clock_slot_proposal (st : State p.n) (s : Slot) :
    (clock p st (SA.proposalTime p.toParams s)).slot p = s := by
  change ((clock p st (SA.proposalTime p.toParams s)).base.now / (4 * p.Δ)).toNat = s
  rw [pcsa_clock_now]
  change ((4 * p.Δ * (s : Int)) / (4 * p.Δ)).toNat = s
  have hd := p.deltaPos
  rw [Int.mul_ediv_cancel_left _ (by positivity)]
  exact Int.toNat_natCast s

/-- R6 for an honest proposal: its rows are valid for every FG lift of its
parent. -/
theorem pcsa_honest_proposal_rows_valid (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n)
    (hN : HonestNamedProposal p c E rho s N) (Q : SimplexFG.FGBlock (Fin p.n))
    (hQ : eraseFG Q = N.erase.parent) :
    rowsValidForParent p Q N.slot N.rows = true := by
  obtain ⟨k, hk, hem⟩ := hN.2
  obtain ⟨ht, app, hprop⟩ := pcsa_emitted_propose E rho s N _ _ k hk hem
  rw [ht] at hprop
  exact pcsa_propose_rows_valid p _ s app N hprop (pcsa_clock_slot_proposal _ s) Q hQ


/-- Without restarts, the local proposal pool only grows. -/
private theorem honest_proposals_stateBefore_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho)
    (a k : Nat) (x : V) (hak : a ≤ k) :
    (V2.D.Run.stateBefore E rho a x).st.proposals ⊆
      (V2.D.Run.stateBefore E rho k x).st.proposals := by
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
    rw [ht, honest_clock_proposals]
    exact ih
  | deliver y o t =>
    change y = x at hy
    subst y
    change _ ⊆ (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st.proposals
    rw [Function.update_self]
    exact List.Subset.trans ih (honest_process_proposals_mono p _ (toWire p o))

/-- The post-clock read at `r` is the clock of the state before the tick at `r`. -/
private theorem honest_postClock_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (y : V) (r : Time) (nd : Node p)
    (hnd : pcsa_postClock E rho y r = some nd) :
    ∃ k, rho.events[k]? = some (.tick y r) ∧
      nd.st = clock p (V2.D.Run.stateBefore E rho k y).st r := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hnd
  obtain ⟨nd0, hnd0, rfl⟩ := Option.map_eq_some_iff.mp hnd
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hnd0
  exact ⟨k, V2.D.Run.tickIdx?_spec hk, rfl⟩

/-- [pcsa34-r4.3b §5.3 (F5), §5.6.1] Receipt of an honest proposal: under a
`DeliveryWithinOn` premise whose deadline after `t_s + 1` is at most `r`, every
honest node holds the exact signed wire of the slot-`s` honest proposal at its
post-clock read at `r`, and the carried PC is valid there. -/
theorem pcsa_honest_proposal_receipt (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {Q : Obj p → Prop} {dl : Time → Time} {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho Q dl cut)
    (hQ : ∀ (o : Obj p) s N, (toWire p o).decode = some (.block s N) → Q o)
    (hmono : Monotone dl) (hlt : ∀ t, t < dl t)
    (s : Slot) (N : NamedProposal p.n) (hN : HonestNamedProposal p c E rho s N)
    (r : Time) (hr : dl (SA.proposalTime p.toParams s + 1) ≤ r) (hc : r ≤ cut)
    (y : V) (hy : y ∈ rho.honest) (nd : Node p)
    (hnd : pcsa_postClock E rho y r = some nd) :
    (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧
      ∀ D, N.pc = some D → pcValid nd.st D = true := by
  have hS := h.valid.toScheduleWellFormed
  obtain ⟨k, hk, hem⟩ := hN.2
  obtain ⟨ht, app, hprop⟩ := pcsa_emitted_propose E rho s N _ _ k hk hem
  rw [ht] at hk hprop
  have hpar := pcsa_propose_parent p _ s app N hprop
  have hR6 := pcsa_honest_proposal_rows_valid E rho s N hN
  let o : Obj p := ofWire p ⟨.proposer s, .proposal N⟩
  have hd : (toWire p o).decode = some (.block s N) := rfl
  have hts : SA.proposalTime p.toParams s < SA.proposalTime p.toParams s + 1 :=
    lt_add_one _
  have hdl0 : dl (SA.proposalTime p.toParams s) ≤ r := (hmono hts.le).trans hr
  have hNX : (pcsaWith m p c).excludes
      (V2.D.Run.stateBeforeTime E rho (dl (SA.proposalTime p.toParams s)) y) o = false := by
    have hf := (hF y hy (V2.D.Run.idxBefore rho (dl (SA.proposalTime p.toParams s)))).1
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hf
    exact pcsa_rows_valid_not_excluded p _ s N hf hR6
  have hemit : V2.D.Run.emits E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s) o
      (SA.proposalTime p.toParams s) := by
    rw [← ht]
    exact hN.2
  obtain ⟨t', htt, htd, j, parent, hj, hh⟩ := hD.broadcast _ hN.1 o (hQ o s N hd) _ hemit
    y hy (hdl0.trans hc) hNX
  have hpobj := pcsa_body_handles_direct _ parent s N hh
  have hjo : rho.events[j]? = some (.deliver y o t') := by rwa [hpobj] at hj
  have hDep := h.valid.deps j y o t' hjo
  have hFresh := h.valid.fresh j y o t' hjo
  have hWF := h.valid.wire j y o t' hjo
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) = ((4 * s : Nat) : Int) * p.Δ
    push_cast
    ring
  have hts0 : 0 ≤ SA.proposalTime p.toParams s := by
    have := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int)
    positivity
  have hnow := V2.D.Engine.delivery_now_ge_public (pcsaClock p c) E rho hS h.noRestart
    hjo hpub hts0 htt
  rw [pcsa_clock_read p c (m := m) (V2.D.Run.stateBefore E rho j y)] at hnow
  have hSlot : N.erase.slot ≤ (V2.D.Run.stateBefore E rho j y).st.slot p := by
    rw [hpar.1]
    change s ≤ ((V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ)).toNat
    have hd' := p.deltaPos
    have hle : 4 * p.Δ * (s : Int) ≤ (V2.D.Run.stateBefore E rho j y).st.base.now := hnow
    have hi : (s : Int) ≤ (V2.D.Run.stateBefore E rho j y).st.base.now / (4 * p.Δ) :=
      (Int.le_ediv_iff_mul_le (by positivity)).mpr (by nlinarith [hle])
    exact_mod_cast (le_trans hi (Int.self_le_toNat _))
  have hDep' := hDep
  change (namedParentHeld (V2.D.Run.stateBefore E rho j y).st N &&
    (parentFG (V2.D.Run.stateBefore E rho j y).st N.erase).isSome) = true at hDep'
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp hDep').2
  have hGeom : eraseFG P = N.erase.parent :=
    of_decide_eq_true (FGSA.pickPair_some_spec _ _ hP).2
  have hf := (hF y hy j).1
  obtain ⟨hNamed, Q', hQ', hAcc⟩ :=
    pcsa_body_accepted p _ s N P hf hGeom (hR6 P hGeom) hWF hDep hFresh hSlot
  have hw : (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈
      (V2.D.Run.stateBefore E rho (j + 1) y).st.proposals := by
    rw [V2.D.Run.stateBefore_succ E rho hjo]
    change _ ∈ (Function.update (V2.D.Run.stateBefore E rho j) y _ y).st.proposals
    rw [Function.update_self]
    change _ ∈ (process p (V2.D.Run.stateBefore E rho j y).st (toWire p o)).proposals
    delta process
    rw [hd]
    dsimp only
    rw [honest_admitBlock_proposals p _ s N Q' hNamed hQ' hAcc]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨k', hk', hst⟩ := honest_postClock_tick E rho y r nd hnd
  have hrk : V2.D.Run.idxBefore rho r ≤ k' := by
    apply Nat.le_of_not_lt
    intro hlt'
    have := (Gen.V2.Duty.index_lt_idxBefore_iff hS hk' r).mp hlt'
    exact lt_irrefl _ this
  have hjk : j + 1 ≤ k' := by
    have := (Gen.V2.Duty.index_lt_idxBefore_iff hS hjo r).mpr (lt_of_lt_of_le htd hdl0)
    omega
  refine ⟨?_, ?_⟩
  · rw [hst, honest_clock_proposals]
    exact honest_proposals_stateBefore_mono E rho h.noRestart _ _ y hjk hw
  · intro D hND
    have hwf : D.wellFormed = true := by
      have hpc := pcsa_accepted_pc_wellFormed p _ s N Q' hAcc
      rw [hND] at hpc
      exact hpc
    have hDx : D ∈ (V2.D.Run.stateBefore E rho k
        (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)).st.pcs := by
      have hv := hpar.2.2
      rw [hND] at hv
      have hm := bestPC_mem _ D hv.symm
      have hm' := (List.mem_filter.mp hm).1
      rwa [pcsa_clock_pcs] at hm'
    have hO := pcsa_outageStore_stateBefore E rho k _ hN.1
    have hT0 := hO.pcBlocks D hDx
    have hkT : k + 1 ≤ V2.D.Run.idxBefore rho (SA.proposalTime p.toParams s + 1) :=
      Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hS hk _).mpr hts)
    have hT1 := pcsa_body_stateBefore_mono E rho h.noRestart _ (Nat.le_of_succ_le hkT) hT0
    rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hT1
    have hT2 := pcsa_stored_body_within_on E rho h hF hD hQ hmono hlt _ y hN.1 hy
      (SA.proposalTime p.toParams s + 1) (hr.trans hc) D.target hT1
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hT2
    have hidx : V2.D.Run.idxBefore rho (dl (SA.proposalTime p.toParams s + 1)) ≤
        V2.D.Run.idxBefore rho r := by
      rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def,
        ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      apply List.countP_mono_left
      intro e _ he
      exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true he) hr)
    have hT3 := pcsa_body_stateBefore_mono E rho h.noRestart y (hidx.trans hrk) hT2
    have hT4 := pcsa_body_clock_keep p _ r (pcsa_reachable_stateBefore E rho k' y) hT3
    have hFy := (hF y hy k').1
    change (D.wellFormed && decide (D.target ∈ nd.st.base.blocks) &&
      Block.compatible D.target (eraseFG nd.st.fg.F)) = true
    rw [hst, pcsa_body_clock_fg, hFy, hwf, decide_eq_true hT4]
    exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq _))


private theorem honest_decoded_wire (o : Wire p.n) (s : Slot) (N : NamedProposal p.n)
    (h : o.decode = some (.block s N)) : o = ⟨.proposer s, .proposal N⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth with
  | none => cases payload <;> delta Wire.decode at h <;> cases h
  | proposer k =>
    cases payload <;> delta Wire.decode at h <;> cases h
    rfl
  | seat l i =>
    cases l <;> cases payload <;> delta Wire.decode Label.ackSlot? at h <;> cases h

/-- An object that decodes to a proposal is not an FG row. -/
theorem pcsa_block_isNonRow (o : Obj p) (s : Slot) (N : NamedProposal p.n)
    (h : (toWire p o).decode = some (.block s N)) : IsNonRow o := by
  have ho : o = ofWire p ⟨.proposer s, .proposal N⟩ :=
    ((toWireEquiv p).left_inv o).symm.trans
      (congrArg (ofWire p) (honest_decoded_wire (toWire p o) s N h))
  rw [ho]
  trivial

/-- [pcsa34-r4.3b §5.3 (F5), §5.6.1] Honest-proposal receipt at the early read
under the delivery premise of Formation and RECOVERY (deadline
`max t z_{s-1} + Δ`): every honest node holds the exact signed wire of the
slot-`s` honest proposal at `e_s`, and its carried PC is valid there. -/
theorem pcsa_honest_proposal_early (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) (s : Slot) (hs : 0 < s) (N : NamedProposal p.n)
    (hN : HonestNamedProposal p c E rho s N) {cut : Time}
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
      (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) cut)
    (hc : SA.earlyTime p.toParams s ≤ cut) :
    ∀ y ∈ rho.honest, ∀ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd →
      (⟨.proposer s, .proposal N⟩ : Wire p.n) ∈ nd.st.proposals ∧
        ∀ D, N.pc = some D → pcValid nd.st D = true := by
  intro y hy nd hnd
  have hd := p.deltaPos
  have hΔ := E.Δ_pos
  refine pcsa_honest_proposal_receipt E rho h hF hD
    (fun o s N hdec => pcsa_block_isNonRow o s N hdec) ?_ ?_ s N hN _ ?_ hc y hy nd hnd
  · intro a b hab
    dsimp only
    exact Int.add_le_add_right (max_le_max hab (le_refl _)) E.Δ
  · intro t
    exact lt_of_le_of_lt (le_max_left t _) (lt_add_of_pos_right _ hΔ)
  · rw [h.delta]
    have h1Δ : (1 : Int) ≤ p.Δ := by simpa using Int.add_one_le_iff.mpr hd
    have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by
      have h1 : 1 ≤ s := hs
      push_cast [Nat.cast_sub h1]
      ring
    change max (4 * p.Δ * (s : Int) + 1) (4 * p.Δ * ((s - 1 : Nat) : Int) + 3 * p.Δ) + p.Δ ≤
      4 * p.Δ * (s : Int) + 2 * p.Δ
    rw [hcast]
    rcases max_cases (4 * p.Δ * (s : Int) + 1) (4 * p.Δ * ((s : Int) - 1) + 3 * p.Δ) with
      ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> nlinarith

end AvailableChain.PCSA.Run
end
