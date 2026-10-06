module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSource
public import AvailableChainPCSAProofs.Proofs.Foundations.StampRun

public section

/-! Local clock and receipt-time bounds for Formation. -/

namespace AvailableChain.PCSA

private theorem formation_normalize_time {n : Nat} (st : State n) :
    (normalizeS st).base.now = st.base.now := by
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_time {n : Nat} (st : State n) :
    (reconcile st).base.now = st.base.now := by
  rw [show (reconcile st).base.now = st.base.now from by
    delta reconcile
    rw [formation_normalize_time]]

private theorem formation_row_time (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.now = st.base.now := by
  cases hd : a.decode? with
  | none => delta admitRow; rw [hd]
  | some val =>
    delta admitRow
    rw [hd]
    change (if a ∈ st.rowPool then st else
      { st with rowPool := st.rowPool ++ [a] }).base.now = _
    split <;> rfl

private theorem formation_raw_ack_time {n : Nat} (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.now = st.base.now := by
  rw [(poolAckRaw_frame st a).2.2.1]

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

/-- A delivery leaves the local clock time unchanged. -/
theorem pcsa_formation_process_now (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.now = st.base.now := by
  have ha (st : State p.n) (as : List (AckWire p.n)) :
      (as.foldl poolAckRaw st).base.now = st.base.now := by
    induction as generalizing st with
    | nil => rfl
    | cons a as ih => rw [List.foldl_cons, ih, formation_raw_ack_time]
  have hr (st : State p.n) (as : List (RowWire p.n)) :
      (as.foldl (admitRow p) st).base.now = st.base.now := by
    induction as generalizing st with
    | nil => rfl
    | cons a as ih => rw [List.foldl_cons, ih, formation_row_time]
  cases hd : o.decode with
  | none => delta process; rw [hd]
  | some val =>
    cases val with
    | vote slot seat root =>
      delta process
      rw [hd]
      change (admitHead p st slot seat root).base.now = _
      exact FGSA.Run.Internal.grid_admitVote_now st.base _
    | row seat body =>
      delta process
      rw [hd]
      change (admitRow p st ⟨o.auth, body⟩).base.now = _
      exact formation_row_time p st _
    | block slot N =>
      have hg := FGSA.Run.Internal.grid_admitProposal_now (q := p.toParams.engine) st.base
        (baseProposal slot N.erase N.raw N.support) N.erase (N.raw.map baseHead)
      delta process
      rw [hd]
      change (admitBlock p st slot N).base.now = _
      delta admitBlock
      split
      · rfl
      · cases hp : parentFG st N.erase with
        | none => rfl
        | some P =>
          change (if blockAccepted p st slot N P then
            formationAccepted p st slot N P else st).base.now = _
          split
          · delta formationAccepted
            rw [hr, (collectPCs_frame _).1, ha]
            cases hc : N.pc <;> dsimp only <;> split_ifs <;>
              first
              | (rw [formation_reconcile_time]; simpa only [deleteConflictingLeases_def] using hg)
              | simpa only [deleteConflictingLeases_def] using hg
          · rfl
    | ack slot seat root =>
      delta process
      rw [hd]
      change (admitAck p st ⟨o.auth, root⟩).base.now = _
      delta admitAck
      rw [(collectPCs_frame _).1]
      cases he : AckWire.decode? (⟨o.auth, root⟩ : AckWire p.n) with
      | none => delta poolAck; rw [he]
      | some val =>
        delta poolAck
        rw [he]
        rcases val with ⟨label, signer, target⟩
        change (if st.slot p < label || !ackSlotOK st label target ||
          (⟨o.auth, root⟩ : AckWire p.n) ∈ st.ackPool then st else
          if 2 ≤ (seatAcks st label signer).length &&
            !decide (target ∈ seatAcks st label signer) then st else
          { st with ackPool := st.ackPool ++ [⟨o.auth, root⟩] }).base.now = _
        split_ifs <;> rfl
    | pc C =>
      delta process
      rw [hd]
      change (admitPC st C).base.now = _
      delta admitPC
      split
      · rw [(collectPCs_frame _).1, ha]
      · rfl

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every local clock before an indexed event is at most that event's time. -/
theorem pcsa_formation_now_before_event (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (j : Nat) (e : V2.Event V (Obj p)) (he : rho.events[j]? = some e) (x : V) :
    (V2.D.Run.stateBefore E rho j x).st.base.now ≤ e.time := by
  have hzero : 0 ≤ e.time := (h.in_horizon e (List.mem_of_getElem? he)).1
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => nd.st.base.now ≤ e.time) (Nat.zero_le j) x ?_ hzero
  intro k f _ hkj hf hn hc
  cases f with
  | restart y t =>
    change y = x at hn
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    exact hzero
  | tick y t =>
    change y = x at hn
    subst y
    have ht : t ≤ e.time := by
      have hk := (List.getElem?_eq_some_iff.mp hf).1
      have hj := (List.getElem?_eq_some_iff.mp he).1
      have hh := (List.pairwise_iff_getElem.mp h.sorted) k j hk hj hkj
      rw [(List.getElem?_eq_some_iff.mp hf).2, (List.getElem?_eq_some_iff.mp he).2] at hh
      exact V2.D.Engine.time_le_of_key_le _ _ hh
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    have hs := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hh : (clock p (V2.D.Run.stateBefore E rho k x).st t).base.now ≤ e.time := by
      rw [pcsa_formation_clock_now]
      exact ht
    exact hs.symm ▸ hh
  | deliver y o t =>
    change y = x at hn
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    change (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.now ≤ e.time
    rw [pcsa_formation_process_now]
    exact hc

/-- Sorted ticks and deliveries make the local clock monotone without restart. -/
theorem pcsa_formation_now_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (hNR : V2.D.NoRestart rho) (i j : Nat) (hij : i ≤ j) (x : V) :
    (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (V2.D.Run.stateBefore E rho j x).st.base.now := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i x).st.base.now ≤ nd.st.base.now)
    hij x ?_ (le_refl _)
  intro k e _ _ he hn hc
  cases e with
  | restart y t => exact (hNR k y t he).elim
  | tick y t =>
    change y = x at hn
    subst y
    have ht := hc.trans (pcsa_formation_now_before_event E rho h k (.tick x t) he x)
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now
    rw [Function.update_self]
    have hs := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hh : (V2.D.Run.stateBefore E rho i x).st.base.now ≤
        (clock p (V2.D.Run.stateBefore E rho k x).st t).base.now := by
      rw [pcsa_formation_clock_now]
      exact ht
    exact hs.symm ▸ hh
  | deliver y o t =>
    change y = x at hn
    subst y
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now
    rw [Function.update_self]
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.now
    rw [pcsa_formation_process_now]
    exact hc

/-- The local clock immediately after a tick records its exact time. -/
theorem pcsa_formation_now_after_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (x : V) (t : Time)
    (hj : rho.events[j]? = some (.tick x t)) :
    (V2.D.Run.stateBefore E rho (j + 1) x).st.base.now = t := by
  have hs := congrArg (fun nd : Node p => nd.st.base.now) (V2.D.Run.step_tick_eq E rho hj).1
  exact hs.trans (congrArg (fun st : State p.n => st.base.now)
    (pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t) |>.trans
      (pcsa_formation_clock_now p _ t))

end AvailableChain.PCSA.Run
end
