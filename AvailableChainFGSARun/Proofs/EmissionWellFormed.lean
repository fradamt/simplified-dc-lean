module
public import AvailableChainFGSARun.Statements.Emission
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSARun.Proofs.Schedule
public import AvailableChainFGSA.Proofs.Head
public import AvailableChainKitFG.ClientSafety

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The application codec recovers the input of each emitted proposal. -/
theorem decode_honest (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) :
    HonestProposalDecodes p c E rho := by
  intro i v s hi _ _ _ b raw sup rows hm
  rw [(V2.Run.step_tick_eq E rho hi).2] at hm
  have ha := (fgsa_emits_proposal E rho _ v _ s _).mp hm
  obtain ⟨H, raw', sup', rows', he, -, happ⟩ := rowsOk_withApp _ _ _ ha.2.2.2
  cases he
  exact (congrArg c.unapp happ).trans (c.unapp_app _)

private theorem emission_rows_clock (st : State p.n) (t : Time)
    (h : EmissionRowsValid st) : EmissionRowsValid (FGSA.clock p st t) := by
  constructor
  · rw [clock_rowPool]; exact h.1
  · rw [clock_proposals]; exact h.2

private theorem emission_rows_admit (st : State p.n) (a : RowWire p.n)
    (h : EmissionRowsValid st) (ha : a.valid = true) :
    EmissionRowsValid (admitRow p st a) := by
  rcases admitRow_eq p st a with he | he
  · rw [he]; exact h
  · rw [he]
    refine ⟨?_, h.2⟩
    intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.1 a' hm
    · exact List.mem_singleton.mp hm ▸ ha

private theorem emission_rows_fold (rows : List (RowWire p.n)) (st : State p.n)
    (h : EmissionRowsValid st) (hr : ∀ a ∈ rows, a.valid = true) :
    EmissionRowsValid (rows.foldl (admitRow p) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (emission_rows_admit st a h (hr a (List.mem_cons_self ..)))
      (fun a ha => hr a (List.mem_cons_of_mem _ ha))

private theorem emission_rows_process (st : State p.n) (o : Obj p)
    (h : EmissionRowsValid st) (hw : (fgsa p c).wellFormed o = true) :
    EmissionRowsValid (FGSA.process p st (toWire p o)) := by
  change FGSA.wellFormed p (toWire p o) = true at hw
  change EmissionRowsValid (match (toWire p o).decode with
    | some (.vote s i b) => admitHead p st s i b
    | some (.row _ _ body) => admitRow p st ⟨(toWire p o).auth, body⟩
    | some (.block s b raw sup rows) => admitBlock p st s b raw sup rows
    | none => st)
  cases hd : (toWire p o).decode with
  | none => exact h
  | some m =>
    cases m with
    | vote s i b => exact h
    | row r i body =>
      have he := decode_eq_row.mp hd
      rw [he] at hw ⊢
      exact emission_rows_admit _ _ h hw
    | block s b raw sup rows =>
      have he := decode_eq_block.mp hd
      have hr : ∀ a ∈ rows, a.valid = true := by
        change (match (toWire p o).decode with
          | some (.vote _ _ _) => true
          | some (.row _ _ body) => body.valid
          | some (.block s b raw sup rows) =>
            b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
              raw.all (fun v => match v.decode? with
                | some (r, _, _) => r + 1 == b.slot | none => false) &&
              sup.all (fun v => decide (v ∈ raw)) &&
              rows.all (fun a => a.valid && match a.decode? with
                | some (r, _, _) => decide (r ≤ p.round b.slot) | none => false) && rowsOk b rows
          | none => false) = true at hw
        rw [hd] at hw
        intro a ha
        exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).2 a ha)).1
      change EmissionRowsValid (match parentFG st b with
        | none => st
        | some P => if blockAccepted p st s b P rows then
          rows.foldl (admitRow p)
            (if (on_block p.E p.cfg st.fg (fgBlock P b rows)).F = st.fg.F then
              { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := on_block p.E p.cfg st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] }
            else reconcile { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := on_block p.E p.cfg st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] })
          else st)
      cases hp : parentFG st b with
      | none => exact h
      | some P =>
        dsimp only
        split
        · apply emission_rows_fold _ _ _ hr
          have hs : EmissionRowsValid
              { st with
                base := (GridCO.admitProposal p.toParams.engine st.base
                  (baseProposal s b raw sup) b (raw.map baseHead)),
                fg := on_block p.E p.cfg st.fg (fgBlock P b rows),
                proposals := st.proposals ++ [⟨.proposer s, .proposal b raw sup rows⟩] } := by
            refine ⟨h.1, ?_⟩
            intro w hw s' b' raw' sup' rows' hd'
            rcases List.mem_append.mp hw with hm | hm
            · exact h.2 w hm s' b' raw' sup' rows' hd'
            · have hew := List.mem_singleton.mp hm
              subst w
              change some (Input.block s b raw sup rows) =
                some (Input.block s' b' raw' sup' rows') at hd'
              cases hd'
              exact hr
          split
          · exact hs
          · constructor
            · rw [(reconcile_frame _).2.2.1]; exact hs.1
            · rw [(reconcile_frame _).2.1]; exact hs.2
        · exact h

/-- Delivery wire checks keep all pool and stored-proposal rows valid.
Restarts empty both lists. No schedule or restart premise is needed. -/
theorem fgsa_emissionRowsValid (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hd : V2.DeliveryWellFormed E rho) (i : Nat) (v : V) :
    EmissionRowsValid (V2.Run.stateBefore E rho i v).st := by
  have hinit : ∀ v, EmissionRowsValid (V2.Run.stateBefore E rho 0 v).st := by
    intro v
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  apply Gen.V2.interval_induction_all E rho (fun _ nd => EmissionRowsValid nd.st)
    hinit (j := i) ?_ i (Nat.zero_le i) le_rfl v
  intro v k e _ _ he hv h
  cases e with
  | restart u t =>
    change u = v at hv; subst u
    simp only [V2.World.step, Function.update_self]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | tick u t =>
    change u = v at hv; subst u
    simp only [V2.World.step, Function.update_self]
    exact (tick_st (c := c) E rho (V2.Run.stateBefore E rho k v) v t).symm ▸
      emission_rows_clock _ _ h
  | deliver u o t =>
    change u = v at hv; subst u
    simp only [V2.World.step, Function.update_self]
    exact emission_rows_process _ o h (hd.wire k v o t he)

private theorem emission_attest_valid (st : State p.n) (Λ : Record) (j : Fin p.n) :
    (attest p st Λ j).1.valid = true := by
  change (match (createRow p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1.height_pair with
    | .empty => true | .vote h _ _ => decide (1 ≤ h)) = true
  cases hh : (createRow p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1.height_pair with
  | empty => rfl
  | vote h T t =>
    have hf := KitFG.height_pair_vote_fields hh
    obtain ⟨C, _, hc⟩ := Option.map_eq_some_iff.mp hf
    have he := congrArg Prod.fst hc
    change (derive p.E p.cfg C).h = h at he
    exact decide_eq_true (he ▸ KitFG.one_le_h p.E p.cfg C)

private theorem emission_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) :
    ∀ a ∈ proposalRows p st H, a.valid = true ∧
      ∃ r j body, a.decode? = some (r, j, body) ∧ r ≤ p.round (st.slot p) := by
  let r := p.round (st.slot p)
  let inI := fun r' => decide (r ≤ r' + p.wF) && decide (r' ≤ r)
  let good := fun a : RowWire p.n => a.valid = true ∧
    ∃ r' j body, a.decode? = some (r', j, body) ∧ r' ≤ r
  have window (a : RowWire p.n) (ha : (a.round?.map inI).getD false = true)
      (hb : a.valid = true) : good a := by
    change ((a.decode?.map (·.1)).map inI).getD false = true at ha
    cases hd : a.decode? with
    | none => rw [hd] at ha; cases ha
    | some x =>
      obtain ⟨r', j, body⟩ := x
      rw [hd] at ha
      exact ⟨hb, r', j, body, hd, of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2⟩
  have blocks : ∀ a ∈ blockWireRows p st inI, good a := by
    intro a ha
    obtain ⟨xs, hx, ha⟩ := List.mem_flatten.mp ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp hx
    change (match w.decode with
      | some (.block _ b _ _ rows) => if inI (p.round b.slot) then
          some (rows.filter (fun a => (a.round?.map inI).getD false)) else none
      | _ => none) = some xs at he
    cases hd : w.decode with
    | none => rw [hd] at he; cases he
    | some m =>
      cases m with
      | vote s j b => rw [hd] at he; cases he
      | row r j body => rw [hd] at he; cases he
      | block s b raw sup rows =>
        rw [hd] at he
        dsimp only at he
        split at he
        · cases he
          obtain ⟨hm, hi⟩ := List.mem_filter.mp ha
          exact window a hi (hv.2 w hw s b raw sup rows hd a hm)
        · cases he
  let A := st.rowPool.filter (fun a => (a.round?.map inI).getD false &&
    !decide (a ∈ chainWireRows st H))
  have hA : ∀ a ∈ A, good a := by
    intro a ha
    obtain ⟨hm, ht⟩ := List.mem_filter.mp ha
    exact window a (Bool.and_eq_true_iff.mp ht).1 (hv.1 a hm)
  change ∀ a ∈ (List.filter (fun a => !decide (a ∈ chainWireRows st H) && !decide (a ∈ A))
    (blockWireRows p st inI)).foldl (fun acc a =>
      if decide (a ∈ acc) || 2 ≤ (acc.filter (fun x =>
        x.decode?.map (fun y => (y.1, y.2.1)) == a.decode?.map (fun y => (y.1, y.2.1)))).length
      then acc else acc ++ [a]) A, good a
  apply List.foldlRecOn (motive := fun xs => ∀ a ∈ xs, good a) _ _ hA
  intro acc hacc a ha
  split
  · exact hacc
  · intro a' hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hacc a' hm
    · have he := List.mem_singleton.mp hm
      subst a'
      exact blocks a (List.mem_filter.mp ha).1

private theorem emission_proposal_votes (st : State p.n) (s : Slot) :
    (∀ a ∈ (proposerVotes st s).filterMap liftHead?,
      ∃ j b, a.decode? = some (s - 1, j, b)) ∧
    (∀ a ∈ (proposerSupport st s).filterMap liftHead?,
      a ∈ (proposerVotes st s).filterMap liftHead?) := by
  constructor
  · intro a ha
    obtain ⟨w, hw, hl⟩ := List.mem_filterMap.mp ha
    have ht : GridCO.headLabel? w = some (s - 1) :=
      beq_iff_eq.mp (List.mem_filter.mp hw).2
    change (GridCO.headLabel? w >>= fun r => GridCO.headSeat? w >>= fun j =>
      GridCO.headTarget? w >>= fun b => some ⟨.seat (.head r) j, b⟩) = some a at hl
    rw [ht] at hl
    obtain ⟨r, hr, hl⟩ := Option.bind_eq_some_iff.mp hl
    have her := Option.some.inj hr
    subst r
    obtain ⟨j, _, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨b, _, he⟩ := Option.bind_eq_some_iff.mp hl
    cases he
    exact ⟨j, b, rfl⟩
  · intro a ha
    obtain ⟨w, hw, he⟩ := List.mem_filterMap.mp ha
    exact List.mem_filterMap.mpr ⟨w, (List.mem_filter.mp hw).1, he⟩

/-- The parent chosen at a proposal tick is stored and has a smaller slot. -/
theorem fgsa_propose_parent_lt (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hs : V2.ScheduleWellFormed E rho) {i : Nat} {v : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick v (SA.proposalTime p.toParams s))) (hs0 : 0 < s) :
    let st := FGSA.clock p (V2.Run.stateBefore E rho i v).st (SA.proposalTime p.toParams s)
    (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s := by
  exact (fgsa_stored_block_slots E rho hs hi hs0).2.1 _
    (getHead_stored p _ (storeBundle_postClock E rho i v _).cstore _ _)

private theorem emission_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hs : st.slot p = s) (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  have he : m = .proposal (.node H s (packBody a rows))
      ((proposerVotes st s).filterMap liftHead?)
      ((proposerSupport st s).filterMap liftHead?) rows := by
    change (if s = 0 then none else some (.proposal (.node H s (packBody 0 rows))
      ((proposerVotes st s).filterMap liftHead?)
      ((proposerSupport st s).filterMap liftHead?) rows)).map
        (withApp a) = some m at hm
    rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
    exact (Option.some.inj hm).symm
  have hcontent := rowsOk_withApp st s a hm
  rw [he]
  change (true && (s == s) && decide (H.slot < s) &&
    ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) &&
    rows.all (fun a => a.valid && match a.decode? with
      | some (r, _, _) => decide (r ≤ p.round s) | none => false) &&
    rowsOk (.node H s (packBody a rows)) rows) = true
  obtain ⟨hraw, hsup⟩ := emission_proposal_votes st s
  have hr : rows.all (fun a => a.valid && match a.decode? with
      | some (r, _, _) => decide (r ≤ p.round s) | none => false) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨hv, r, j, body, hd, hb⟩ := emission_proposal_rows st H hv a ha
    rw [hs] at hb
    rw [hv, hd]
    exact Bool.and_eq_true_iff.mpr ⟨rfl, decide_eq_true hb⟩
  have hvotes : ((proposerVotes st s).filterMap liftHead?).all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) = true := by
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨j, b, hd⟩ := hraw v hv
    rw [hd]
    exact beq_iff_eq.mpr (Nat.sub_add_cancel hs0)
  have hsupport : ((proposerSupport st s).filterMap liftHead?).all
      (fun v => decide (v ∈ (proposerVotes st s).filterMap liftHead?)) = true :=
    List.all_eq_true.mpr (fun v hv => decide_eq_true (hsup v hv))
  have hc : rowsOk (.node H s (packBody a rows)) rows = true := by
    obtain ⟨H', raw', sup', rows', he', hc, -⟩ := hcontent
    rw [he] at he'
    have eqs := Msg.proposal.inj he'
    have hb := Block.node.inj eqs.1
    rw [← hb.1, ← eqs.2.2.2] at hc
    exact hc
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

/-- Every honest awake emission passes the wire check. -/
theorem honest_emit_wellFormed (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hd : V2.DeliveryWellFormed E rho) (hs : V2.ScheduleWellFormed E rho) :
    HonestEmissionWellFormed p c E rho := by
  intro i v t hi _ hawake o ho
  rw [(V2.Run.step_tick_eq E rho hi).2] at ho
  obtain ⟨auth, m⟩ := o
  cases auth with
  | none =>
    have hu : ∀ m, (⟨.none, m⟩ : Obj p) ∉
        (V2.tick E rho (V2.Run.stateBefore E rho i v) v t).2 := by
      intro m hm
      change (⟨.none, m⟩ : Obj p) ∈ (if E.awake v t then
        (duties p t).flatMap (fun l => (rho.ownSeats l v).filterMap (fun j =>
          ((fgsa p c).act ((fgsa p c).clock (V2.Run.stateBefore E rho i v) t) l
            (rho.input v t)).map (fun m => ⟨.seat l j, m⟩))) ++ [] else []) at hm
      rw [ite_eq_left hawake, List.append_nil] at hm
      obtain ⟨l, _, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨j, _, hm⟩ := List.mem_filterMap.mp hm
      obtain ⟨m', _, he⟩ := Option.map_eq_some_iff.mp hm
      cases he
    exact (hu m ho).elim
  | seat l j =>
    have ha := (mem_tick_seat_iff E rho _ v t l j m).mp ho
    cases l with
    | base l =>
      cases l with
      | head s =>
        have he : .head (headVote p (FGSA.clock p (V2.Run.stateBefore E rho i v).st t) s) = m :=
          Option.some.inj ha.2.2.2
        subst m
        rfl
      | fg r =>
        have he : .row (attest p (FGSA.clock p (V2.Run.stateBefore E rho i v).st t)
            (V2.Run.stateBefore E rho i v).record ⟨0, p.nPos⟩).1 = m := Option.some.inj ha.2.2.2
        subst m
        exact emission_attest_valid _ _ _
    | prop s =>
      have ht : SA.proposalTime p.toParams s = t := ha.2.1
      subst t
      have hm : (propose p (FGSA.clock p (V2.Run.stateBefore E rho i v).st
          (SA.proposalTime p.toParams s)) s).map
          (withApp (c.app (rho.input v (SA.proposalTime p.toParams s)))) = some m := ha.2.2.2
      have hs0 : 0 < s := by
        by_contra hn
        have he : s = 0 := Nat.eq_zero_of_not_pos hn
        subst s
        change none = some m at hm
        cases hm
      exact emission_proposal_wf _ s _ (fgsa_proposal_slot (c := c) _ s)
        (emission_rows_clock _ _ (fgsa_emissionRowsValid E rho hd i v))
        (fgsa_propose_parent_lt E rho hs hi hs0) hm

end AvailableChain.FGSA.Run
end
