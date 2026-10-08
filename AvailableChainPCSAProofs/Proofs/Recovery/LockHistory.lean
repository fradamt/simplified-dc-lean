module
public import AvailableChainPCSAClaims.Statements.Regimes
public import AvailableChainPCSAProofs.Proofs.Recovery.LockRank
public import AvailableChainPCSAProofs.Proofs.Shared.Clock

public section

/-! Exact lock rows and rank stamps between local gate changes. -/
namespace AvailableChain.PCSA

private def RecoveryRowHistory {n : Nat} (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State n) : Prop :=
  ∀ row ∈ st.base.obligations, Q row (leaseRank st row.1)

private theorem recovery_history_normalize_lockHistory {n : Nat}
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State n)
    (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem recovery_history_reconcile_lockHistory {n : Nat}
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State n)
    (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (reconcile st) := by
  apply recovery_history_normalize_lockHistory
  intro row hr
  exact h row (List.mem_filter.mp hr).1

private theorem recovery_history_install_lockHistory {n : Nat}
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State n)
    (pc : PC n) (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (installPC st pc) := by
  rw [installPC_def]
  split
  · exact h
  · intro row hr
    exact h row (deleteConflictingLeases_subset _ _ hr)

private theorem recovery_history_row_lockHistory (p : Params)
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State p.n)
    (a : RowWire p.n) (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (admitRow p st a) := by
  delta admitRow
  cases hd : a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem recovery_history_rawAck_lockHistory {n : Nat}
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State n)
    (a : AckWire n) (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (poolAckRaw st a) := by
  delta poolAckRaw
  cases hd : a.decode? <;> dsimp only
  · exact h
  · split <;> exact h

private theorem recovery_history_process_lockHistory (p : Params)
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State p.n)
    (o : Wire p.n) (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (process p st o) := by
  have hc := collectPCs_invariant (n := p.n) (RecoveryRowHistory Q)
    (fun st pc h _ => recovery_history_install_lockHistory Q st pc h)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : RecoveryRowHistory Q st) :
      RecoveryRowHistory Q (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h
      (fun acc hh a _ => recovery_history_rawAck_lockHistory Q acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      intro row hr
      apply h row
      change row ∈ (GridCO.admitVote _ _ _).obligations at hr
      simpa only [GridCO.admitVote_obligations] using hr
    | row i body => exact recovery_history_row_lockHistory p Q st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : RecoveryRowHistory Q { st with base := (GridCO.admitProposal
                    p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                    N.erase (N.raw.map baseHead)) } := by
                intro row hr
                exact h row (by simpa only [GridCO.admitProposal_obligations] using hr)
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply recovery_history_reconcile_lockHistory; exact hb)
                | (apply recovery_history_reconcile_lockHistory; intro row hr;
                    exact hb row (deleteConflictingLeases_subset _ _ hr))
                | exact hb
                | (intro row hr; exact hb row (deleteConflictingLeases_subset _ _ hr))
            · intro acc hh a _
              exact recovery_history_row_lockHistory p Q acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) <;> dsimp only
      · exact h
      · rename_i v
        rcases v with ⟨_, _, _⟩
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h


private theorem recovery_history_clockPre_lockHistory (p : Params)
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State p.n) (t : Time)
    (h : RecoveryRowHistory Q st) : RecoveryRowHistory Q (clockPre p st t) := by
  delta clockPre
  dsimp only
  split <;> split <;> split
  all_goals
    intro row hr
    apply h row
    first
      | exact (List.mem_filter.mp hr).1
      | exact (List.mem_filter.mp (List.mem_filter.mp hr).1).1

private theorem recovery_history_clock_lockHistory (p : Params)
    (Q : (Block × Nat × Time) → Option PCRank → Prop)
    (st : State p.n) (t : Time)
    (h : RecoveryRowHistory Q st) (ht : ∀ s, t ≠ SA.gateTime p.toParams s) :
    RecoveryRowHistory Q (clock p st t) := by
  delta clock
  dsimp only
  split
  · rename_i hg
    exact (ht _ (eq_of_beq (Bool.and_eq_true_iff.mp hg).2)).elim
  · exact recovery_history_clockPre_lockHistory p Q st t h

/-- A receipt can only remove exact lock rows and preserves their rank stamps. -/
theorem recovery_process_lock_history (p : Params) (st : State p.n) (o : Wire p.n)
    (row : Block × Nat × Time)
    (hr : row ∈ (process p st o).base.obligations) :
    row ∈ st.base.obligations ∧
      leaseRank (process p st o) row.1 = leaseRank st row.1 := by
  exact recovery_history_process_lockHistory p
    (fun row rank => row ∈ st.base.obligations ∧ rank = leaseRank st row.1)
    st o (fun row hr => ⟨hr, rfl⟩) row hr

/-- A clock outside a gate can only remove exact rows and preserves their ranks. -/
theorem recovery_clock_lock_history (p : Params) (st : State p.n) (t : Time)
    (ht : ∀ s, t ≠ SA.gateTime p.toParams s) (row : Block × Nat × Time)
    (hr : row ∈ (clock p st t).base.obligations) :
    row ∈ st.base.obligations ∧ leaseRank (clock p st t) row.1 = leaseRank st row.1 := by
  exact recovery_history_clock_lockHistory p
    (fun row rank => row ∈ st.base.obligations ∧ rank = leaseRank st row.1)
    st t (fun row hr => ⟨hr, rfl⟩) ht row hr

private theorem recovery_history_history_rank_other {n : Nat} (st : State n) (b B : Block) (g : Nat)
    (d : Time) (rank : Option PCRank) (hne : B ≠ b) :
    leaseRank (writeLease st b g d rank) B = leaseRank st B := by
  simp only [leaseRank_def, writeLease_def, List.find?_append, List.find?_filter]
  have he : (fun row : Block × Option PCRank =>
      decide ((row.1 != b) = true ∧ (row.1 == B) = true)) =
      (fun row => row.1 == B) := by
    funext row
    by_cases h : row.1 = B
    · simp [h, hne]
    · simp [h]
  rw [he]
  simp [Ne.symm hne]


private theorem recovery_history_write_lockHistory {n : Nat}
    (Q : (Block × Nat × Time) → Option PCRank → Prop) (st : State n)
    (B : Block) (g : Nat) (d : Time) (rank : Option PCRank)
    (h : RecoveryRowHistory Q st) (hb : ∀ row, row.1 = B → Q row rank) :
    RecoveryRowHistory Q (writeLease st B g d rank) := by
  intro row hr
  by_cases he : row.1 = B
  · rw [he, writeLease_rank]
    exact hb row he
  · rw [recovery_history_history_rank_other st B row.1 g d rank he]
    apply h row
    change row ∈ (GridCO.writeObligation st.base B g d).obligations at hr
    delta GridCO.writeObligation at hr
    rcases List.mem_append.mp hr with hr | hr
    · exact (List.mem_filter.mp hr).1
    · exact (he (congrArg Prod.fst (List.mem_singleton.mp hr))).elim

private theorem recovery_history_slow_of_genuine_eq (p : Params) {n : Nat}
    (v w : GridCO.State n .root)
    (h : v.genuine = w.genuine) (s : Slot) (B : Block) :
    SA.Root.slowEligible p.toParams v s B = SA.Root.slowEligible p.toParams w s B := by
  exact congrArg (fun rows => SA.Root.slowEligible p.toParams
    { v with genuine := rows } s B) h

private theorem recovery_history_gate_genuine (p : Params) {n : Nat} (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) :
    (gateFrom p a cs rank st s).base.genuine =
      @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s
        (SA.Root.confirmationFrom p.toParams a (actView st) s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · rfl
  · dsimp only
    split
    · rfl
    · apply List.foldlRecOn (motive := fun acc : State n => acc.base.genuine =
        @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s
          (some _))
      · rfl
      · intro acc hh B _
        apply List.foldlRecOn (motive := fun acc' : State n => acc'.base.genuine =
          @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s
            (some _))
        · exact hh
        · intro acc' hh' g _
          exact hh'

/-- A changed row or rank at a gate comes from its checked slow-write branch.
The preceding saved window is retained in the actual gate output. -/
theorem recovery_gate_change_window (p : Params) {n : Nat} (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (row : Block × Nat × Time)
    (hr : row ∈ (gateFrom p a cs rank st s).base.obligations)
    (hchange : ¬ (row ∈ st.base.obligations ∧
      leaseRank (gateFrom p a cs rank st s) row.1 = leaseRank st row.1)) :
    ∃ C, SA.Root.confirmationFrom p.toParams a (actView st) s = some C ∧
      Block.Preceq row.1 C ∧ leaseWriteOK cs rank row.1 = true ∧
      SA.Root.slowEligible p.toParams (actView (gateFrom p a cs rank st s)) s row.1 = true ∧
      leaseRank (gateFrom p a cs rank st s) row.1 = rank := by
  let out := gateFrom p a cs rank st s
  let Q := fun row : Block × Nat × Time => fun stamp : Option PCRank =>
    (row ∈ st.base.obligations ∧ stamp = leaseRank st row.1) ∨
      ∃ C, SA.Root.confirmationFrom p.toParams a (actView st) s = some C ∧
        Block.Preceq row.1 C ∧ leaseWriteOK cs rank row.1 = true ∧
        SA.Root.slowEligible p.toParams (actView out) s row.1 = true ∧ stamp = rank
  have hi : RecoveryRowHistory Q st := fun row hr => Or.inl ⟨hr, rfl⟩
  have hg : RecoveryRowHistory Q out := by
    unfold out
    rw [gateFrom_def]
    dsimp only
    cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
    · exact hi
    · rename_i C
      have hgen : out.base.genuine =
          @GridCO.recordGenuine GridCO.slowLeasePolicy n .root (actView st) s (some C) := by
        rw [recovery_history_gate_genuine, hc]
      dsimp only
      split
      · exact hi
      · generalize hfold : List.foldl _ _ _ = result
        have hf : RecoveryRowHistory Q result ∧ result.base.genuine = out.base.genuine := by
          rw [← hfold]
          apply List.foldlRecOn (motive := fun acc : State n =>
            RecoveryRowHistory Q acc ∧ acc.base.genuine = out.base.genuine)
          · exact ⟨hi, hgen.symm⟩
          · intro acc hh B hB
            have ht := (List.mem_filter.mp hB).2
            have hp : Block.Preceq B C := (Bool.and_eq_true_iff.mp
              (Bool.and_eq_true_iff.mp ht).1).2
            have hw := (Bool.and_eq_true_iff.mp ht).2
            delta slowLevels
            split
            · rename_i hs
              have he : SA.Root.slowEligible p.toParams (actView out) s B = true := by
                rw [← recovery_history_slow_of_genuine_eq p (actView acc) (actView out) hh.2 s B]
                exact hs
              simp only [List.foldl_cons, List.foldl_nil]
              refine ⟨recovery_history_write_lockHistory Q acc B _ _ rank hh.1 ?_, hh.2⟩
              intro row hr
              exact Or.inr ⟨C, hc, hr ▸ hp, hr ▸ hw, hr ▸ he, rfl⟩
            · exact hh
        exact hf.1
  exact (hg row hr).resolve_left hchange

private theorem recovery_history_normalize_history_fields {n : Nat} (st : State n) :
    (normalizeS st).base.obligations = st.base.obligations ∧
    (normalizeS st).leaseRanks = st.leaseRanks ∧
    (normalizeS st).base.genuine = st.base.genuine := by
  delta normalizeS
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- A changed exact lock row at a clock has a fresh gate, its current result,
its preceding saved window, and the rank of that gate's successful write. -/
theorem recovery_clock_change_window (p : Params) (st : State p.n) (t : Time)
    (row : Block × Nat × Time) (hr : row ∈ (clock p st t).base.obligations)
    (hchange : ¬ (row ∈ st.base.obligations ∧
      leaseRank (clock p st t) row.1 = leaseRank st row.1)) :
    ∃ s, t = SA.gateTime p.toParams s ∧
      GridCO.savedGenuine (clockPre p st t).base s = none ∧
      ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st t).fg.F)
          (actView (clockPre p st t)) s = some C ∧
        Block.Preceq row.1 C ∧
        leaseWriteOK (clockPre p st t).pcs (gateRank p (clockPre p st t) s) row.1 = true ∧
        SA.Root.slowEligible p.toParams (actView (clock p st t)) s row.1 = true ∧
        leaseRank (clock p st t) row.1 = gateRank p (clockPre p st t) s := by
  have hpre (hr : row ∈ (clockPre p st t).base.obligations) :
      row ∈ st.base.obligations ∧
        leaseRank (clockPre p st t) row.1 = leaseRank st row.1 :=
    recovery_history_clockPre_lockHistory p
      (fun row rank => row ∈ st.base.obligations ∧ rank = leaseRank st row.1)
      st t (fun row hr => ⟨hr, rfl⟩) row hr
  unfold clock at hr hchange ⊢
  dsimp only at hr hchange ⊢
  split at hr
  · rename_i ht
    simp only [ht, ite_true] at hchange ⊢
    let s := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
    have htime : t = SA.gateTime p.toParams s := eq_of_beq (Bool.and_eq_true_iff.mp ht).2
    refine ⟨s, htime, ?_⟩
    rw [gateStep_def] at hr hchange ⊢
    dsimp only at hr hchange ⊢
    have hn (v : State p.n) : leaseRank (normalizeS v) row.1 = leaseRank v row.1 := by
      simp only [leaseRank_def, (recovery_history_normalize_history_fields v).2.1]
    rw [(recovery_history_normalize_history_fields _).1] at hr
    simp only [hn] at hchange ⊢
    split at hr
    · rename_i hold
      simp only [hold, ite_true] at hchange
      exact (hchange (hpre hr)).elim
    · rename_i hfresh
      simp only [hfresh, Bool.false_eq_true, ite_false] at hchange ⊢
      have hnone : GridCO.savedGenuine (clockPre p st t).base s = none := by
        cases he : GridCO.savedGenuine (clockPre p st t).base s with
        | none => rfl
        | some value =>
          have hv : (GridCO.savedGenuine (clockPre p st t).base s).isSome = true := by
            rw [he]
            rfl
          exact (hfresh hv).elim
      refine ⟨hnone, ?_⟩
      have hc := recovery_gate_change_window p (clockPre p st t)
        (eraseFG (clockPre p st t).fg.F) (clockPre p st t).pcs
        (gateRank p (clockPre p st t) s) s row hr (by
          rintro ⟨hr, he⟩
          have hp := hpre hr
          exact hchange ⟨hp.1, he.trans hp.2⟩)
      obtain ⟨C, hc, hp, hw, hs, hk⟩ := hc
      refine ⟨C, hc, hp, hw, ?_, hk⟩
      rw [recovery_history_slow_of_genuine_eq p (actView (normalizeS _)) (actView _)
        (recovery_history_normalize_history_fields _).2.2]
      exact hs
  · rename_i ht
    simp only [ht, Bool.false_eq_true, ite_false] at hchange
    exact (hchange (hpre hr)).elim

private def RecoveryDeadlineBound {n : Nat} (st : State n) (limit : Time) : Prop :=
  ∀ row ∈ st.base.obligations, row.2.2 ≤ limit

private theorem recovery_history_write_bound {n : Nat} (st : State n) (B : Block) (g : Nat)
    (d limit : Time) (rank : Option PCRank) (h : RecoveryDeadlineBound st limit) (hd : d ≤ limit) :
    RecoveryDeadlineBound (writeLease st B g d rank) limit := by
  have hlookup : (GridCO.deadlineOf st.base B g).getD d ≤ limit := by
    delta GridCO.deadlineOf
    cases he : st.base.obligations.find? (fun row => row.1 == B && row.2.1 == g) with
    | none => exact hd
    | some row => exact h row (List.mem_of_find?_eq_some he)
  intro row hr
  change row ∈ (GridCO.writeObligation st.base B g d).obligations at hr
  delta GridCO.writeObligation at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h row (List.mem_filter.mp hr).1
  · cases List.mem_singleton.mp hr
    exact max_le hlookup hd

private theorem recovery_history_gate_bound (p : Params) (st : State p.n) (a : Block)
    (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot) (limit : Time)
    (h : RecoveryDeadlineBound st limit) (hd : SA.gateTime p.toParams s + Run.pcsaL p ≤ limit) :
    RecoveryDeadlineBound (gateFrom p a cs rank st s) limit := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s
  · exact h
  · dsimp only
    split
    · exact h
    · apply List.foldlRecOn (motive := fun acc : State p.n => RecoveryDeadlineBound acc limit)
      · exact h
      · intro acc hh B _
        apply List.foldlRecOn (motive := fun acc : State p.n => RecoveryDeadlineBound acc limit)
        · exact hh
        · intro acc' hh' g _
          exact recovery_history_write_bound acc' B g _ limit rank hh' hd

private theorem recovery_history_clock_bound (p : Params) (st : State p.n) (t limit : Time)
    (h :
    RecoveryDeadlineBound st limit) (ht : t + Run.pcsaL p ≤ limit) :
    RecoveryDeadlineBound (clock p st t) limit := by
  have hp : RecoveryDeadlineBound (clockPre p st t) limit :=
    recovery_history_clockPre_lockHistory p (fun row _ => row.2.2 ≤ limit) st t h
  unfold clock
  dsimp only
  split
  · rename_i hg
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def]
    dsimp only
    change RecoveryRowHistory (fun row _ => row.2.2 ≤ limit) (normalizeS _)
    apply recovery_history_normalize_lockHistory
    split
    · exact hp
    · exact recovery_history_gate_bound p _ _ _ _ _ limit hp (he ▸ ht)
  · exact hp

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Sorted event times bound each stored deadline by the local time plus L. -/
theorem recovery_lock_deadline_bound (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) :
    ∀ row ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations,
      row.2.2 ≤ (V2.D.Run.stateBefore E rho i x).st.base.now + pcsaL p := by
  apply V2.D.Engine.stateBefore_invariant (pcsaClock p c) (by
    intro d
    rw [pcsa_clock_read p c (m := m) ((pcsaWith m p c).restore d)]
    exact le_rfl)
    E rho hs (fun nd : Node p => RecoveryDeadlineBound nd.st (nd.st.base.now + pcsaL p))
  · intro row hr
    exact (List.not_mem_nil hr).elim
  · intro nd t ht hh
    rw [pcsa_clock_read p c (m := m) nd] at ht
    change RecoveryDeadlineBound (clock p nd.st t) ((clock p nd.st t).base.now + pcsaL p)
    rw [pcsa_clock_now]
    apply recovery_history_clock_bound p nd.st t _
    · intro row hr
      exact (hh row hr).trans (Int.add_le_add_right ht _)
    · exact le_rfl
  · intro nd o hh row hr
    change row.2.2 ≤ (process p nd.st (toWire p o)).base.now + pcsaL p
    rw [pcsa_process_now]
    exact hh row (recovery_process_lock_history p nd.st (toWire p o) row hr).1
  · intro nd o hh
    exact hh
  · intro nd _ row hr
    exact (List.not_mem_nil hr).elim

end AvailableChain.PCSA.Run


namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The final uninterrupted interval of an exact row and rank starts at a gate.
This statement retains all intermediate event states, including receipts. -/
theorem recovery_lock_last_change (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (x : V)
    (row : Block × Nat × Time)
    (hr : row ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      (∀ q, j < q → q ≤ i →
        row ∈ (V2.D.Run.stateBefore E rho q x).st.base.obligations ∧
        leaseRank (V2.D.Run.stateBefore E rho q x).st row.1 =
          leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) ∧
      ¬ (row ∈ (V2.D.Run.stateBefore E rho j x).st.base.obligations ∧
        leaseRank (V2.D.Run.stateBefore E rho j x).st row.1 =
          leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) := by
  classical
  let P := fun q => row ∈ (V2.D.Run.stateBefore E rho q x).st.base.obligations ∧
    leaseRank (V2.D.Run.stateBefore E rho q x).st row.1 =
      leaseRank (V2.D.Run.stateBefore E rho i x).st row.1
  have hex : ∃ a, a ≤ i ∧ ∀ q, a ≤ q → q ≤ i → P q :=
    ⟨i, le_rfl, by
      intro q hq hi
      have he : q = i := by omega
      subst q
      exact ⟨hr, rfl⟩⟩
  let a := Nat.find hex
  have ha := Nat.find_spec hex
  change a ≤ i ∧ ∀ q, a ≤ q → q ≤ i → P q at ha
  have hpos : 0 < a := by
    by_contra hn
    have he : a = 0 := by omega
    have hz := (ha.2 0 (by omega) (by omega)).1
    exact List.not_mem_nil hz
  have hnot : ¬ P (a - 1) := by
    intro hp
    have hh : a - 1 ≤ i ∧ ∀ q, a - 1 ≤ q → q ≤ i → P q := by
      refine ⟨by omega, ?_⟩
      intro q hq hi
      by_cases he : q = a - 1
      · simpa only [he] using hp
      · exact ha.2 q (by omega) hi
    exact Nat.find_min hex (show a - 1 < a by omega) hh
  have haf : P a := ha.2 a le_rfl ha.1
  have hs : a - 1 + 1 = a := by omega
  have hgate : ∃ s, rho.events[a - 1]? = some (.tick x (SA.gateTime p.toParams s)) := by
    cases he : rho.events[a - 1]? with
    | none =>
      exfalso
      apply hnot
      have hn : P (a - 1 + 1) := hs ▸ haf
      simpa only [P, V2.D.Run.stateBefore, List.take_add_one, he,
        Option.toList_none, List.append_nil] using hn
    | some e =>
      have hn : P (a - 1 + 1) := hs ▸ haf
      dsimp only [P] at hn
      rw [V2.D.Run.stateBefore_succ E rho he] at hn
      by_cases hx : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hx
          subst y
          change row ∈ (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
            ).st.base.obligations ∧
            leaseRank (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
              ).st row.1 = _ at hn
          rw [Function.update_self] at hn
          exact (List.not_mem_nil hn.1).elim
        | deliver y o t =>
          change y = x at hx
          subst y
          change row ∈ (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
            ).st.base.obligations ∧
            leaseRank (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
              ).st row.1 = _ at hn
          rw [Function.update_self] at hn
          change row ∈ (process p (V2.D.Run.stateBefore E rho (a - 1) x).st
            (toWire p o)).base.obligations ∧
            leaseRank (process p (V2.D.Run.stateBefore E rho (a - 1) x).st
              (toWire p o)) row.1 = _ at hn
          have hp := recovery_process_lock_history p _ (toWire p o) row hn.1
          exact (hnot ⟨hp.1, hp.2.symm.trans hn.2⟩).elim
        | tick y t =>
          change y = x at hx
          subst y
          by_cases hg : ∃ s, t = SA.gateTime p.toParams s
          · obtain ⟨s, rfl⟩ := hg
            exact ⟨s, rfl⟩
          · change row ∈ (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
              ).st.base.obligations ∧
              leaseRank (Function.update (V2.D.Run.stateBefore E rho (a - 1)) x _ x
                ).st row.1 = _ at hn
            rw [Function.update_self] at hn
            change row ∈ (V2.D.tick E rho (V2.D.Run.stateBefore E rho (a - 1) x)
                x t).1.st.base.obligations ∧
              leaseRank (V2.D.tick E rho (V2.D.Run.stateBefore E rho (a - 1) x)
                x t).1.st row.1 = _ at hn
            have hclock := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho (a - 1) x) x t
            rw [hclock] at hn
            have hp := recovery_clock_lock_history p _ t (by simpa using hg) row hn.1
            exact (hnot ⟨hp.1, hp.2.symm.trans hn.2⟩).elim
      · rw [V2.D.World.step_apply_of_node_ne E rho _ hx] at hn
        exact (hnot hn).elim
  obtain ⟨s, he⟩ := hgate
  exact ⟨a - 1, by omega, s, he, fun q hq hi => ha.2 q (by omega) hi, hnot⟩

/-- A stored row has a fresh write gate with the checked rank, saved window,
and an uninterrupted interval to the selected event read. The gate time bounds
its final deadline. All fields are derived from the run. -/
theorem recovery_lock_write_witness (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (i : Nat) (x : V) (row : Block × Nat × Time)
    (hr : row ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      (∀ q, j < q → q ≤ i →
        row ∈ (V2.D.Run.stateBefore E rho q x).st.base.obligations ∧
        leaseRank (V2.D.Run.stateBefore E rho q x).st row.1 =
          leaseRank (V2.D.Run.stateBefore E rho i x).st row.1) ∧
      row.2.2 ≤ SA.gateTime p.toParams s + pcsaL p ∧
      let pre := clockPre p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s)
      GridCO.savedGenuine pre.base s = none ∧
      ∃ C, SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) s = some C ∧
        Block.Preceq row.1 C ∧ leaseWriteOK pre.pcs (gateRank p pre s) row.1 = true ∧
        SA.Root.slowEligible p.toParams
          (actView (V2.D.Run.stateBefore E rho (j + 1) x).st) s row.1 = true ∧
        leaseRank (V2.D.Run.stateBefore E rho i x).st row.1 = gateRank p pre s := by
  obtain ⟨j, hj, s, he, hsurv, hnot⟩ := recovery_lock_last_change E rho i x row hr
  have hstep : (V2.D.Run.stateBefore E rho (j + 1) x).st =
      clock p (V2.D.Run.stateBefore E rho j x).st (SA.gateTime p.toParams s) := by
    rw [V2.D.Run.stateBefore_succ E rho he]
    change (Function.update (V2.D.Run.stateBefore E rho j) x _ x).st = _
    rw [Function.update_self]
    exact pcsa_tick_st E rho _ x _
  have hafter := hsurv (j + 1) (by omega) (by omega)
  have hbound := recovery_lock_deadline_bound E rho hs (j + 1) x row hafter.1
  rw [hstep, pcsa_clock_now] at hbound
  rw [hstep] at hafter
  have hc := recovery_clock_change_window p (V2.D.Run.stateBefore E rho j x).st
    (SA.gateTime p.toParams s) row hafter.1 (by
      rintro ⟨hr, hk⟩
      exact hnot ⟨hr, hk.symm.trans hafter.2⟩)
  obtain ⟨s', ht, hfresh, C, hc, hp, hw, hwindow, hrank⟩ := hc
  have heq : s = s' := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = 4 * p.Δ * (s' : Int) + 6 * p.Δ at ht
    have heq : (s : Int) = (s' : Int) := by nlinarith
    exact_mod_cast heq
  subst s'
  refine ⟨j, hj, s, he, hsurv, hbound, hfresh, C, hc, hp, hw, ?_, ?_⟩
  · rwa [hstep]
  · exact hafter.2.symm.trans hrank

end AvailableChain.PCSA.Run
end
