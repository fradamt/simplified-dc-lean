module
public import AvailableChainPCSAProofs.Proofs.Recovery.LockOrigin
public import AvailableChainPCSAProofs.Proofs.Recovery.LockBound
public import AvailableChainFGSA.Proofs.Head.Pool

public section

/-! Slow-window bounds and strict slot order in PC-SA runs. -/
namespace AvailableChain.PCSA

/-- Parent slots increase on each non-genesis edge. -/
def RecoverySlotOrdered : Block → Prop
  | .genesis => True
  | .node parent slot _ _ => parent.slot < slot ∧ RecoverySlotOrdered parent

private theorem recovery_slot_le_of_prefix (B C : Block) (ho : RecoverySlotOrdered C)
    (hp : Block.Preceq B C) : B.slot ≤ C.slot := by
  induction C with
  | genesis =>
    have he : B = .genesis := of_decide_eq_true hp
    subst B
    exact le_rfl
  | node parent s r b ih =>
    change (decide (B = .node parent s r b) || Block.preceq B parent) = true at hp
    rcases Bool.or_eq_true_iff.mp hp with he | hp
    · have he' := of_decide_eq_true he
      subst B
      exact le_rfl
    · exact (ih ho.2 hp).trans (Nat.le_of_lt ho.1)

private theorem recovery_prefix_eq_of_slot_ge (B C : Block) (ho : RecoverySlotOrdered C)
    (hp : Block.Preceq B C) (hs : C.slot ≤ B.slot) : B = C := by
  cases C with
  | genesis => exact of_decide_eq_true hp
  | node parent s r b =>
    change (decide (B = .node parent s r b) || Block.preceq B parent) = true at hp
    rcases Bool.or_eq_true_iff.mp hp with he | hp
    · exact of_decide_eq_true he
    · have hb := recovery_slot_le_of_prefix B parent ho.2 hp
      have ht := ho.1
      change s ≤ B.slot at hs
      exact (Nat.not_lt_of_ge hs (lt_of_le_of_lt hb ht)).elim

private def TreeOrdered {n : Nat} (st : State n) : Prop :=
  ∀ B ∈ st.base.blocks, RecoverySlotOrdered B

private theorem grid_proposal_ordered (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (B : Block)
    (raw : List (GridCO.HeadWire n .root))
    (h : ∀ C ∈ st.blocks, RecoverySlotOrdered C) :
    ∀ C ∈ (GridCO.admitProposal p st o B raw).blocks, RecoverySlotOrdered C := by
  delta GridCO.admitProposal
  dsimp only
  cases o.auth <;> dsimp only <;> split
  all_goals first | exact h | skip
  all_goals
    rename_i ha
    apply List.foldlRecOn (motive := fun v : GridCO.State n .root =>
      ∀ C ∈ v.blocks, RecoverySlotOrdered C)
    · intro C hc
      rcases List.mem_append.mp hc with hc | hc
      · exact h C hc
      · cases List.mem_singleton.mp hc
        have htests := ha
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          not_or, Bool.not_eq_false, decide_eq_false_iff_not] at htests
        have hp : GridCO.blockKnown st B.parent = true := by tauto
        have hs : B.parent.slot < B.slot := by tauto
        have ho := h B.parent (of_decide_eq_true hp)
        cases B with
        | genesis => trivial
        | node P s r b => exact ⟨hs, ho⟩
    · intro acc hh a _ C hc
      exact hh C (by simpa only [GridCO.admitVote_blocks] using hc)

private theorem normalize_ordered {n : Nat} (st : State n) (h : TreeOrdered st) :
    TreeOrdered (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem reconcile_ordered {n : Nat} (st : State n) (h : TreeOrdered st) :
    TreeOrdered (reconcile st) := normalize_ordered _ h

private theorem row_ordered (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : TreeOrdered st) : TreeOrdered (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem raw_ordered {n : Nat} (st : State n) (a : AckWire n)
    (h : TreeOrdered st) : TreeOrdered (poolAckRaw st a) := by
  intro B hb
  exact h B (by simpa only [(poolAckRaw_frame st a).2.2.1] using hb)

private theorem process_ordered (p : Params) (st : State p.n) (o : Wire p.n)
    (h : TreeOrdered st) : TreeOrdered (process p st o) := by
  have hc (st : State p.n) (h : TreeOrdered st) : TreeOrdered (collectPCs st) := by
    intro B hb
    exact h B (by simpa only [(collectPCs_frame st).2.1] using hb)
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : TreeOrdered st) :
      TreeOrdered (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => raw_ordered acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      intro B hb
      change B ∈ (GridCO.admitVote _ _ _).blocks at hb
      exact h B (by simpa only [GridCO.admitVote_blocks] using hb)
    | row i body => exact row_ordered p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb := grid_proposal_ordered p.toParams.engine st.base
                (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_ordered; exact hb)
                | exact hb
            · intro acc hh a _
              exact row_ordered p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

private theorem gate_ordered (p : Params) {n : Nat} (st : State n)
    (a : Block) (cs : List (PC n)) (rank : Option PCRank) (s : Slot)
    (h : TreeOrdered st) : TreeOrdered (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact h
  | some B =>
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc hh b _
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact hh'

private theorem clock_ordered (p : Params) (st : State p.n) (t : Time)
    (h : TreeOrdered st) : TreeOrdered (clock p st t) := by
  have hc : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply normalize_ordered
    split
    · exact hc
    · exact gate_ordered p _ _ _ _ _ hc
  · exact hc

/-- Every block in a reachable PC-SA tree has strictly increasing parent slots. -/
theorem recovery_reachable_slot_order (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ B ∈ st.base.blocks, RecoverySlotOrdered B := by
  induction h with
  | init => intro B hb; have he : B = .genesis := List.mem_singleton.mp hb; subst B; trivial
  | tick t _ ih => exact clock_ordered p _ t ih
  | deliver o _ ih => exact process_ordered p _ o ih

/-- A proper ancestor of a stored block has a strictly smaller slot. -/
theorem recovery_stored_strict_slots (p : Params) (st : State p.n) (h : Reachable p st)
    (P B : Block) (hb : B ∈ st.base.blocks) (hp : Block.Preceq P B) (hne : P ≠ B) :
    P.slot < B.slot := by
  by_contra hn
  exact hne (recovery_prefix_eq_of_slot_ge P B (recovery_reachable_slot_order p st h B hb)
    hp (Nat.le_of_not_gt hn))

private def LocksOrdered {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.obligations, RecoverySlotOrdered row.1

private theorem write_ordered {n : Nat} (st : State n) (B : Block) (g : Nat)
    (d : Time) (rank : Option PCRank) (h : LocksOrdered st) (hb : RecoverySlotOrdered B) :
    LocksOrdered (writeLease st B g d rank) := by
  intro row hr
  change row ∈ (GridCO.writeObligation st.base B g d).obligations at hr
  delta GridCO.writeObligation at hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h row (List.mem_filter.mp hr).1
  · cases List.mem_singleton.mp hr
    exact hb

private theorem gate_locks_ordered (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : TreeOrdered st) (h : LocksOrdered st) :
    LocksOrdered (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact h
  | some B =>
    dsimp only
    split
    · exact h
    · apply List.foldlRecOn
      · exact h
      · intro acc hh b hb
        have hm : b ∈ st.base.blocks := (List.mem_filter.mp (List.mem_filter.mp hb).1).1
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact write_ordered acc' b g _ rank hh' (ht b hm)

private theorem clock_locks_ordered (p : Params) (st : State p.n) (t : Time)
    (ht : TreeOrdered st) (h : LocksOrdered st) : LocksOrdered (clock p st t) := by
  have hc : LocksOrdered (clockPre p st t) := by
    intro row hr
    obtain ⟨old, hold, he⟩ := List.mem_map.mp
      (clockPre_lock_targets_subset p st t (List.mem_map.mpr ⟨row, hr, rfl⟩))
    exact he ▸ h old hold
  have hct : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    have hn (st : State p.n) (h : LocksOrdered st) : LocksOrdered (normalizeS st) := by
      delta normalizeS
      split <;> exact h
    apply hn
    split
    · exact hc
    · exact gate_locks_ordered p _ _ _ _ _ hct hc
  · exact hc

/-- Every stored lock target has increasing slots along its ancestry. -/
theorem recovery_reachable_lock_order (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.obligations, RecoverySlotOrdered row.1 := by
  induction h with
  | init => intro row hr; exact (List.not_mem_nil hr).elim
  | tick t hh ih => exact clock_locks_ordered p _ t (recovery_reachable_slot_order p _ hh) ih
  | deliver o _ ih =>
    intro row hr
    obtain ⟨old, hold, he⟩ := List.mem_map.mp
      (process_lock_targets_subset p _ o (List.mem_map.mpr ⟨row, hr, rfl⟩))
    exact he ▸ ih old hold

/-- Proper descendants among live locks have strictly greater slots. -/
theorem recovery_live_strict_slots (p : Params) (st : State p.n) (h : Reachable p st)
    (P B : Block) (hb : LiveLease st B) (hp : Block.Preceq P B) (hne : P ≠ B) :
    P.slot < B.slot := by
  obtain ⟨row, hr, he, _⟩ := hb
  have ho : RecoverySlotOrdered B := he ▸ recovery_reachable_lock_order p st h row hr
  by_contra hn
  exact hne (recovery_prefix_eq_of_slot_ge P B ho hp (Nat.le_of_not_gt hn))


/-- Every prefix of a genuine result has slot at most the result label. -/
theorem recovery_result_prefix_slot (p : Params) (v : GridCO.State p.n .root)
    (a C B : Block) (s : Slot) (ho : ∀ D ∈ v.blocks, RecoverySlotOrdered D)
    (hc : SA.Root.confirmationFrom p.toParams a v s = some C)
    (hb : Block.Preceq B C) : B.slot ≤ s := by
  change GridCO.confirmationFrom p.toParams.engine a v s = some C at hc
  delta GridCO.confirmationFrom at hc
  dsimp only at hc
  split at hc
  · rename_i hpos
    have he := Option.some.inj hc
    rw [he] at hpos
    have hscore : 0 < GridCO.goldfishScoreOn (GridCO.resolutionTree v) v.blocks
        (GridCO.cleanSupport p.toParams.engine v s)
        (GridCO.cleanSupport p.toParams.engine v s) C := by
      omega
    delta GridCO.goldfishScoreOn at hscore
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp hscore)
    have ht := (List.mem_filter.mp hi).2
    rw [FGSA.fgsa_cleanSupport_no_equivocation, Bool.false_or] at ht
    obtain ⟨o, ho', ht⟩ := List.any_eq_true.mp ht
    have hclean := (List.mem_filter.mp ho').1
    have hlabel : GridCO.headLabel? o = some s := by
      simpa using (List.mem_filter.mp
        (List.mem_filter.mp (List.mem_filter.mp hclean).1).1).2
    cases hr : GridCO.headTarget? o with
    | none => simp only [hr, Bool.false_eq_true] at ht
    | some r =>
      rw [hr] at ht
      dsimp only at ht
      cases hresolve : GridCO.resolveTarget .root (GridCO.resolutionTree v) r with
      | none => simp only [hresolve, Bool.false_eq_true] at ht
      | some D =>
        rw [hresolve] at ht
        dsimp only at ht
        simp only [hlabel, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at ht
        exact (recovery_slot_le_of_prefix B D (ho D ht.1.1)
          (Gen.Pure.block_preceq_trans hb ht.2)).trans ht.1.2
  · cases hc


private def ResultsBound {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
    ∀ B, Block.Preceq B C → B.slot ≤ row.1

private theorem grid_vote_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    (GridCO.admitVote p st o).genuine = st.genuine := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> delta GridCO.admitVote <;> dsimp only
  all_goals first | rfl | (split <;> rfl)

private theorem grid_proposal_genuine (p : GridCO.Params) {n : Nat}
    (st : GridCO.State n .root) (o : GridCO.Wire n .root) (B : Block)
    (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal p st o B raw).genuine = st.genuine := by
  delta GridCO.admitProposal
  dsimp only
  cases o.auth <;> dsimp only <;> split
  all_goals first | rfl | skip
  all_goals
    apply List.foldlRecOn (motive := fun v : GridCO.State n .root => v.genuine = st.genuine)
    · rfl
    · intro acc hh a _
      rw [grid_vote_genuine]
      exact hh

private theorem collect_genuine {n : Nat} (st : State n) :
    (collectPCs st).base.genuine = st.base.genuine := by
  apply collectPCs_preserves (fun st : State n => st.base.genuine)
  intro st pc
  rw [installPC_def]
  split <;> rfl

private theorem normalize_results {n : Nat} (st : State n) (h : ResultsBound st) :
    ResultsBound (normalizeS st) := by
  delta normalizeS
  split <;> exact h

private theorem reconcile_results {n : Nat} (st : State n) (h : ResultsBound st) :
    ResultsBound (reconcile st) := by
  apply normalize_results
  intro row hr C hc B hb
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hr
  cases he
  exact h old hold C (Option.filter_eq_some_iff.mp hc).1 B hb

private theorem row_results (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : ResultsBound st) : ResultsBound (admitRow p st a) := by
  delta admitRow
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem raw_results {n : Nat} (st : State n) (a : AckWire n)
    (h : ResultsBound st) : ResultsBound (poolAckRaw st a) := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact h
  | some v => dsimp only; split <;> exact h

private theorem process_results (p : Params) (st : State p.n) (o : Wire p.n)
    (h : ResultsBound st) : ResultsBound (process p st o) := by
  have hc (st : State p.n) (h : ResultsBound st) : ResultsBound (collectPCs st) := by
    delta ResultsBound at h ⊢
    simpa only [collect_genuine] using h
  have ha (st : State p.n) (as : List (AckWire p.n)) (h : ResultsBound st) :
      ResultsBound (as.foldl poolAckRaw st) :=
    List.foldlRecOn as poolAckRaw h (fun acc hh a _ => raw_results acc a hh)
  delta process
  cases hd : o.decode with
  | none => exact h
  | some msg => cases msg with
    | vote s i r =>
      delta ResultsBound at h ⊢
      delta admitHead
      simpa only [grid_vote_genuine] using h
    | row i body => exact row_results p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hp : parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · apply List.foldlRecOn
            · apply hc
              apply ha
              have hb : ResultsBound { st with base := (GridCO.admitProposal
                  p.toParams.engine st.base (baseProposal s N.erase N.raw N.support)
                    N.erase (N.raw.map baseHead)) } := by
                delta ResultsBound at h ⊢
                simpa only [grid_proposal_genuine] using h
              cases N.pc <;> dsimp only <;> split_ifs <;> first
                | (apply reconcile_results; exact hb)
                | exact hb
            · intro acc hh a _
              exact row_results p acc a hh
          · exact h
    | ack s i r =>
      dsimp only
      delta admitAck
      apply hc
      delta poolAck
      cases hd : AckWire.decode? (⟨o.auth, r⟩ : AckWire p.n) with
      | none => exact h
      | some v =>
        rcases v with ⟨_, _, _⟩
        dsimp only
        split
        · exact h
        · split <;> exact h
    | pc pc =>
      dsimp only
      delta admitPC
      split
      · exact hc _ (ha _ _ h)
      · exact h

private theorem record_results (p : Params) (st : State p.n) (s : Slot)
    (oc : Option Block) (h : ResultsBound st)
    (hn : ∀ C, oc = some C → ∀ B, Block.Preceq B C → B.slot ≤ s) :
    ∀ row ∈ @GridCO.recordGenuine GridCO.slowLeasePolicy p.n .root (actView st) s oc,
      ∀ C, row.2 = some C → ∀ B, Block.Preceq B C → B.slot ≤ row.1 := by
  delta GridCO.recordGenuine
  split
  · intro row hr C hc B hb
    rcases List.mem_append.mp hr with hr | hr
    · exact h row hr C hc B hb
    · cases List.mem_singleton.mp hr
      exact hn C hc B hb
  · exact h

private theorem gate_results (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : TreeOrdered st) (h : ResultsBound st) :
    ResultsBound (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none => exact record_results p st s none h (by intro C he; cases he)
  | some C =>
    have hi := record_results p st s (some C) h (by
      intro D hd B hb
      cases Option.some.inj hd
      exact recovery_result_prefix_slot p (actView st) a C B s
        (fun D hd => ht D (List.mem_filter.mp hd).1) hc hb)
    dsimp only
    split
    · exact hi
    · apply List.foldlRecOn
      · exact hi
      · intro acc hh b _
        apply List.foldlRecOn
        · exact hh
        · intro acc' hh' g _
          exact hh'

private theorem clock_results (p : Params) (st : State p.n) (t : Time)
    (ht : TreeOrdered st) (h : ResultsBound st) : ResultsBound (clock p st t) := by
  have hc : ResultsBound (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact h
  have hct : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    dsimp only
    apply normalize_results
    split
    · exact hc
    · exact gate_results p _ _ _ _ _ hct hc
  · exact hc

/-- Every prefix of a saved result is bounded by its label. -/
theorem recovery_saved_result_slot (p : Params) (st : State p.n) (h : Reachable p st) :
    ∀ row ∈ st.base.genuine, ∀ C, row.2 = some C →
      ∀ B, Block.Preceq B C → B.slot ≤ row.1 := by
  induction h with
  | init => intro row hr; exact (List.not_mem_nil hr).elim
  | tick t hh ih => exact clock_results p _ t (recovery_reachable_slot_order p _ hh) ih
  | deliver o _ ih => exact process_results p _ o ih

private theorem slow_result_bound (p : Params) (st : State p.n) (s : Slot) (B : Block)
    (h : ResultsBound st) (he : SA.Root.slowEligible p.toParams (actView st) s B = true) :
    p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  try delta Slot Time at *
  have hk := p.kLarge
  change (decide (p.k ≤ s + 1) && (List.range (p.k - 1)).all (fun d =>
    match GridCO.savedGenuine (actView st) (s - (d + 1)) with
    | some (some C) => Block.preceq B C
    | _ => false)) = true at he
  obtain ⟨hs, hall⟩ := Bool.and_eq_true_iff.mp he
  refine ⟨of_decide_eq_true hs, ?_⟩
  have ho := List.all_eq_true.mp hall (p.k - 2) (List.mem_range.mpr (by omega))
  rw [show p.k - 2 + 1 = p.k - 1 by omega] at ho
  cases hc : GridCO.savedGenuine (actView st) (s - (p.k - 1)) with
  | none => simp only [hc, Bool.false_eq_true] at ho
  | some oc => cases oc with
    | none => simp only [hc, Bool.false_eq_true] at ho
    | some C =>
      rw [hc] at ho
      change (st.base.genuine.find? (fun row => row.1 == s - (p.k - 1))).map Prod.snd =
        some (some C) at hc
      obtain ⟨row, hf, hr⟩ := Option.map_eq_some_iff.mp hc
      have hl : row.1 = s - (p.k - 1) := by simpa using List.find?_some hf
      simpa only [hl] using h row (List.mem_of_find?_eq_some hf) C hr B ho

private theorem gate_window_origin (p : Params) (st : State p.n)
    (a : Block) (cs : List (PC p.n)) (rank : Option PCRank) (s : Slot)
    (ht : TreeOrdered st) (hr : ResultsBound st) (B : Block)
    (hb : B ∈ (gateFrom p a cs rank st s).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨
      p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  let Q := fun B => B ∈ st.base.obligations.map Prod.fst ∨
    p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1)
  have hi : ∀ row ∈ st.base.obligations, Q row.1 :=
    fun row hm => Or.inl (List.mem_map.mpr ⟨row, hm, rfl⟩)
  have hw (acc : State p.n) (b : Block) (g : Nat) (d : Time)
      (h : ResultsBound acc ∧ ∀ row ∈ acc.base.obligations, Q row.1) (hq : Q b) :
      ResultsBound (writeLease acc b g d rank) ∧
        ∀ row ∈ (writeLease acc b g d rank).base.obligations, Q row.1 := by
    refine ⟨h.1, ?_⟩
    intro row hm
    change row ∈ (GridCO.writeObligation acc.base b g d).obligations at hm
    delta GridCO.writeObligation at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h.2 row (List.mem_filter.mp hm).1
    · cases List.mem_singleton.mp hm
      exact hq
  have hg : ResultsBound (gateFrom p a cs rank st s) ∧
      ∀ row ∈ (gateFrom p a cs rank st s).base.obligations, Q row.1 := by
    rw [gateFrom_def]
    dsimp only
    cases hc : SA.Root.confirmationFrom p.toParams a (actView st) s with
    | none => exact ⟨record_results p st s none hr (by intro C he; cases he), hi⟩
    | some C =>
      have hn := record_results p st s (some C) hr (by
        intro D hd B hb
        cases Option.some.inj hd
        exact recovery_result_prefix_slot p (actView st) a C B s
          (fun D hd => ht D (List.mem_filter.mp hd).1) hc hb)
      dsimp only
      split
      · exact ⟨hn, hi⟩
      · apply List.foldlRecOn (motive := fun acc : State p.n => ResultsBound acc ∧
          ∀ row ∈ acc.base.obligations, Q row.1)
        · exact ⟨hn, hi⟩
        · intro acc ha b _
          delta slowLevels
          split
          · rename_i he
            simpa only [List.foldl_cons, List.foldl_nil] using
              hw acc b _ _ ha (Or.inr (slow_result_bound p acc s b ha.1 he))
          · exact ha
  obtain ⟨row, hm, rfl⟩ := List.mem_map.mp hb
  exact hg.2 row hm

private theorem clock_window_origin (p : Params) (st : State p.n) (t : Time)
    (h : Reachable p st) (B : Block)
    (hb : B ∈ (clock p st t).base.obligations.map Prod.fst) :
    B ∈ st.base.obligations.map Prod.fst ∨ ∃ s,
      t = SA.gateTime p.toParams s ∧ p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  have ht := recovery_reachable_slot_order p st h
  have hr := recovery_saved_result_slot p st h
  have hct : TreeOrdered (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact ht
  have hcr : ResultsBound (clockPre p st t) := by
    delta clockPre
    dsimp only
    split <;> split <;> split <;> exact hr
  delta clock at hb
  dsimp only at hb
  split at hb
  · rename_i hg
    have he : t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat :=
      eq_of_beq (Bool.and_eq_true_iff.mp hg).2
    rw [gateStep_def] at hb
    have hn (st : State p.n) : (normalizeS st).base.obligations = st.base.obligations := by
      delta normalizeS
      split <;> rfl
    dsimp only at hb
    rw [hn] at hb
    split at hb
    · exact Or.inl (clockPre_lock_targets_subset p st t hb)
    · rcases gate_window_origin p _ _ _ _ _ hct hcr B hb with hb | hb
      · exact Or.inl (clockPre_lock_targets_subset p st t hb)
      · exact Or.inr ⟨_, he, hb⟩
  · exact Or.inl (clockPre_lock_targets_subset p st t hb)

end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- A stored lock target has an actual gate with the full oldest-label bound. -/
theorem recovery_lock_window_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (i : Nat) (x : V) (B : Block)
    (hm : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
    ∃ j < i, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
      p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  induction i with
  | zero => exact (List.not_mem_nil hm).elim
  | succ i ih =>
    have old (h : B ∈ (V2.D.Run.stateBefore E rho i x).st.base.obligations.map Prod.fst) :
        ∃ j < i + 1, ∃ s, rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) ∧
          p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
      obtain ⟨j, hj, hs⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hs⟩
    cases hi : rho.events[i]? with
    | none =>
      apply old
      simpa only [V2.D.Run.stateBefore, List.take_add_one, hi, Option.toList_none,
        List.append_nil] using hm
    | some e =>
      rw [V2.D.Run.stateBefore_succ E rho hi] at hm
      by_cases hn : e.node = x
      · cases e with
        | restart y t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          exact (List.not_mem_nil hm).elim
        | deliver y o t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          exact old (process_lock_targets_subset p _ (toWire p o) hm)
        | tick y t =>
          change y = x at hn
          subst y
          change B ∈ (Function.update (V2.D.Run.stateBefore E rho i) x _ x).st.base.obligations.map
            Prod.fst at hm
          rw [Function.update_self] at hm
          have ht := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho i x) x t
          rw [ht] at hm
          rcases clock_window_origin p _ t (pcsa_reachable_stateBefore E rho i x) B hm with
            hm | ⟨s, hs, hb⟩
          · exact old hm
          · exact ⟨i, Nat.lt_succ_self i, s, hs ▸ hi, hb⟩
      · rw [V2.D.World.step_apply_of_node_ne E rho _ hn] at hm
        exact old hm

/-- The full lock-origin input at both recovery reads follows from the run. -/
theorem recovery_live_lock_window_origin (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (x : V) (t : Time) (nd : Node p) (hn : pcsa_postClock E rho x t = some nd)
    (B : Block) (hb : LiveLease nd.st B) :
    ∃ s, SA.gateTime p.toParams s ≤ t ∧ p.k ≤ s + 1 ∧ B.slot ≤ s - (p.k - 1) := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hn0
  have hit := V2.D.Run.tickIdx?_spec hi
  obtain ⟨row, hr, he, _⟩ := hb
  have hm : B ∈ (clock p (V2.D.Run.stateBefore E rho i x).st t).base.obligations.map
      Prod.fst := List.mem_map.mpr ⟨row, hr, he⟩
  rcases clock_window_origin p _ t (pcsa_reachable_stateBefore E rho i x) B hm with
    hold | ⟨s, ht, hv⟩
  · obtain ⟨j, hj, s, hjs, hv⟩ := recovery_lock_window_origin E rho i x B hold
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hjs
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hit
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact ⟨s, V2.D.Engine.time_le_of_key_le _ _ hk, hv⟩
  · exact ⟨s, ht.ge, hv⟩

/-- A post-clock reader has a reachable store. -/
theorem recovery_postClock_reachable (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (x : V) (t : Time) (nd : Node p)
    (hn : pcsa_postClock E rho x t = some nd) : Reachable p nd.st := by
  rw [pcsa_postClock_def, pcsa_preTick_def] at hn
  obtain ⟨nd0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp hn0
  exact Reachable.tick t (pcsa_reachable_stateBefore E rho i x)

/-- The two-read lock bound now needs only anchor compatibility. -/
theorem recovery_lock_bound_from_run (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hs : V2.D.ScheduleWellFormed E rho)
    (cA s₁ : Slot) (P : Block) (hslot : P.slot = cA)
    (hwindow : s₁ - 1 - cA ≤ p.k - 1) (horder : cA < s₁)
    (anchorCompatible : ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd → ∀ B, LiveLease nd.st B →
      Block.Compatible B P) :
    ∀ x ∈ rho.honest, ∀ t,
      t = SA.proposalTime p.toParams s₁ ∨ t = SA.voteTime p.toParams s₁ →
      ∀ nd, pcsa_postClock E rho x t = some nd →
      ∀ B, LiveLease nd.st B → Block.Preceq B P := by
  apply recovery_lock_bound E rho cA s₁ P hwindow horder
  · intro x _ t _ nd hn B hb
    exact recovery_live_lock_window_origin E rho hs x t nd hn B hb
  · exact anchorCompatible
  · intro x _ t _ nd hn B hb hp hne
    rw [← hslot]
    exact recovery_live_strict_slots p nd.st (recovery_postClock_reachable E rho x t nd hn)
      P B hb hp hne

end AvailableChain.PCSA.Run
end
