module
public import AvailableChainFGSAInhabit.WeakContinuationWitness
public import AvailableChainGeneric.Proofs.V2.Duty.DeliveryBy

public section
namespace AvailableChain.FGSA.Run.Tests.WeakContinuationWitness

/-! W1: wire checks and execution validity for the window-model generator. -/

section Wire
variable {p : Params}

theorem w1_proposal_rows (st : State p.n) (H : Block)
    (hv : EmissionRowsValid st) : ∀ a ∈ proposalRows p st H, a.valid = true := by
  intro a ha
  rw [proposalRows_eq_proposalRowsFor] at ha
  rcases proposalRowsFor_origin p st (st.slot p) H a ha with
    hm | ⟨o, ho, s, b, hd, hm⟩
  · exact hv.1 a hm
  · exact hv.2 o ho s b hd a hm

theorem w1_proposal_votes (st : State p.n) (s : Slot) :
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

theorem w1_proposal_wf (st : State p.n) (s : Slot) (a : Nat)
    (hv : EmissionRowsValid st)
    (hp : (getHead p st (proposerVotes st s) (proposerSupport st s)).slot < s)
    {m : Msg p.n} (hm : (propose p st s).map (withApp p a) = some m) :
    FGSA.wellFormed p ⟨.proposer s, m⟩ = true := by
  have hs0 : 0 < s := Nat.zero_lt_of_lt hp
  let H := getHead p st (proposerVotes st s) (proposerSupport st s)
  let rows := proposalRows p st H
  let raw := (proposerVotes st s).filterMap liftHead?
  let sup := (proposerSupport st s).filterMap liftHead?
  unfold propose at hm
  rw [ite_eq_right (Nat.ne_of_gt hs0)] at hm
  simp only [Option.map_map] at hm
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp hm
  have heP : P.erase = H := (namedByErase?_sound st H P hP).2
  change FGSA.wellFormed p ⟨.proposer s, .proposal (namedProposal p P s a raw sup rows)⟩ = true
  simp only [FGSA.wellFormed, Wire.decode]
  rw [namedProposal_erase, heP]
  simp only [namedProposal, NamedProposal.raw, NamedProposal.support, NamedProposal.rows]
  change (true && (s == s) && decide (H.slot < s) &&
    raw.all (fun v => match v.decode? with
      | some (r, _, _) => r + 1 == s | none => false) &&
    sup.all (fun v => decide (v ∈ raw)) && rows.all RowWire.valid &&
    contentOk p (proposalBlock p H s a raw sup rows) raw sup rows) = true
  obtain ⟨hraw, hsup⟩ := w1_proposal_votes st s
  have hr : rows.all RowWire.valid = true :=
    List.all_eq_true.mpr (w1_proposal_rows st H hv)
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
  have hc := contentOk_proposalBlock p H s a raw sup rows
  rw [hvotes, hsupport, hr, hc]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, decide_eq_true_eq]
  exact hp

end Wire

/-- A list fold preserves knowledge when each delivery and its children have it. -/
theorem w1_known_fold (P : Obj params → Prop) (w : World) (es : List Event)
    (hw : ∀ v, GenKnown P (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P o ∧ ∀ o', carriesS params o o' → P o') :
    ∀ v, GenKnown P (genFold w es v).st := by
  induction es generalizing w with
  | nil => exact hw
  | cons e es ih =>
    apply ih
    · intro u
      cases e with
      | restart v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact ⟨by simp [fgsa, initial], by simp [GenStoredRows, fgsa, initial],
            by simp [fgsa, initial, GridCO.initial]⟩
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (i7_tick_st (w v) v t).symm ▸ gen_known_clock P _ t (hw v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact gen_known_process P _ o (hw v)
            (he v o t (List.mem_cons_self ..)).1
            (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hw u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

/-- I3 and I7 give row validity at every event prefix, without delivery validity. -/
theorem w1_rows_at_index (h : Time) (es : List Event)
    (ho : GenOrigin V2.D.World.init es) (hc : GenCarried es) (i : Nat) (v : Validator) :
    EmissionRowsValid (V2.D.Run.stateBefore weakEnv (runData h es) i v).st := by
  let P := fun o => ∃ t, GenPast es t o
  have hk : GenKnown P (genFold V2.D.World.init (es.take i) v).st := by
    apply w1_known_fold
    · intro u
      exact ⟨by simp [V2.D.World.init, fgsa, initial],
        by simp [GenStoredRows, V2.D.World.init, fgsa, initial],
        by simp [V2.D.World.init, fgsa, initial, GridCO.initial]⟩
    · intro u o t hm
      have hm' := List.mem_of_mem_take hm
      obtain ⟨x, hx⟩ := ho u o t hm'
      exact ⟨⟨t, x, t, le_rfl, hx⟩, fun o' hcarry => ⟨t, hc u o t hm' o' hcarry⟩⟩
  rw [runData_stateBefore]
  exact ⟨fun a ha => by
      obtain ⟨t, ht⟩ := hk.1 a ha
      exact gen_past_row_valid es t a ht,
    fun w hw s b hd a ha => by
      obtain ⟨t, ht⟩ := hk.2.1 w hw s b hd a ha
      exact gen_past_row_valid es t a ht⟩

/-- Every release passes the wire check, using the symbolic row invariant. -/
theorem w1_emit_wire (h : Time) (es : List Event)
    (hs : V2.D.ScheduleWellFormed weakEnv (runData h es))
    (horigin : GenOrigin V2.D.World.init es) (hcarried : GenCarried es)
    (v : Validator) (o : Obj params) (t : Time)
    (hem : V2.D.Run.emits weakEnv (runData h es) v o t) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨i, hi, ho⟩ := hem
  rw [(V2.D.Run.step_tick_eq weakEnv (runData h es) hi).2] at ho
  obtain ⟨l, j, m, rfl, hl, ha⟩ := gen_tick_seat
    (V2.D.Run.stateBefore weakEnv (runData h es) i v) v t o ho
  cases l with
  | headAction s =>
    have he : .head (headVote params
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st t) s).root = m :=
      Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest params (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st t)
      (V2.D.Run.stateBefore weakEnv (runData h es) i v).record ⟨0, params.nPos⟩).1.map Msg.row
        = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact gen_attest_valid _ _ _ _ hb
  | propAction s =>
    have ht : SA.proposalTime params.toParams s = t :=
      ((fgsa params unitCodec).duties_spec (.propAction s) t).1 hl
    subst t
    have hm : (propose params
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st
          (SA.proposalTime params.toParams s)) s).map (withApp params 0) = some m := ha
    have hs0 : 0 < s := by
      by_contra hn
      have he : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      change none = some m at hm
      cases hm
    have hv := w1_rows_at_index h es horigin hcarried i v
    have hv' : EmissionRowsValid
        (FGSA.clock params (V2.D.Run.stateBefore weakEnv (runData h es) i v).st
          (SA.proposalTime params.toParams s)) := by
      simpa only [EmissionRowsValid, i7_clock_rowPool, i7_clock_proposals] using hv
    exact w1_proposal_wf _ s 0 hv'
      (fgsa_propose_parent_lt weakEnv (runData h es) hs hi hs0) hm

/-- The source schedule has the same public times in the weak environment. -/
theorem w1_source_schedule : V2.D.ScheduleWellFormed weakEnv source :=
  { source_schedule with
    tick_public := source_schedule.tick_public
    tick_total := source_schedule.tick_total }

/-- Proposal wire checks now hold for every source delivery. -/
theorem w1_source_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : source.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, hu⟩ := prefix_origin 248 v o t (List.mem_of_getElem? hi)
  exact w1_emit_wire 247 _ w1_source_schedule (prefix_origin 248)
    (gen_prefix_carried 248).2 u o t (genEmits_runData 247 _ u o t hu)

/-- Proposal wire checks also hold for every continuation delivery. -/
theorem w1_continuation_wire (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : continuation.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).wellFormed o = true := by
  obtain ⟨u, hu⟩ := continuation_genOrigin v o t (List.mem_of_getElem? hi)
  exact w1_emit_wire 263 _ continuation_schedule continuation_genOrigin
    (gen_suffix_carried 16).2 u o t (genEmits_runData 263 _ u o t hu)

/-- A skipped offer has exactly the store effect of the real handler. -/
theorem w1_process_inert (st : State params.n) (o : Obj params)
    (hp : processedS params st o = true) :
    FGSA.process params st (toWire params o) = st := by
  unfold processedS at hp
  unfold FGSA.process
  cases hd : (toWire params o).decode with
  | none => rw [hd] at hp
  | some m =>
    rw [hd] at hp
    cases m with
    | vote s i b =>
      have hm := of_decide_eq_true hp
      change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∈ st.base.votes at hm
      simp [admitHead, GridCO.admitVote, hm]
    | row i body =>
      have hm := of_decide_eq_true hp
      obtain rfl := i7_decode_row o i body hd
      exact i7_admitRow_duplicate st i body hm
    | block s b =>
      have hm := of_decide_eq_true hp
      apply admitBlock_refused
      cases hP : parentFG st b.erase with
      | none => exact Or.inr (Or.inl rfl)
      | some P => exact Or.inr (Or.inr ⟨P, rfl, by simp [blockAccepted, hm]⟩)

/-- The store update does not depend on whether the offer was skipped. -/
theorem w1_deliver_st (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) :
    ((deliverOne t acc vo).1 u).st =
      if u = vo.1 then FGSA.process params (acc.1 u).st (toWire params vo.2)
      else (acc.1 u).st := by
  unfold deliverOne
  split
  · rename_i hp
    by_cases hu : u = vo.1
    · subst u
      rw [ite_eq_left rfl, w1_process_inert _ _ hp]
    · rw [ite_eq_right hu]
  · dsimp only
    by_cases hu : u = vo.1
    · subst u
      simp only [V2.D.World.step, Function.update_self]
      rfl
    · simp only [V2.D.World.step, Function.update_of_ne hu, ite_eq_right hu]

/-- Each node receives one store update for one offered object. -/
theorem w1_offer_st (t : Time) (acc : World × List Event) (o : Obj params)
    (vs : List Validator) (hn : vs.Nodup) (u : Validator) :
    (((vs.map (fun v => (v, o))).foldl (deliverOne t) acc).1 u).st =
      if u ∈ vs then FGSA.process params (acc.1 u).st (toWire params o)
      else (acc.1 u).st := by
  induction vs generalizing acc with
  | nil => simp
  | cons v vs ih =>
    rw [List.map_cons, List.foldl_cons, ih _ hn.of_cons, w1_deliver_st]
    by_cases huv : u = v
    · subst u
      simp only [List.mem_cons, true_or, ↓reduceIte, hn.notMem]
    · by_cases hu : u ∈ vs <;> simp [huv, hu]

/-- All four tick stores are clocks of their input stores. -/
theorem w1_tickBatch_st (t : Time) (w : World) (u : Validator) :
    ((tickBatch t w).1 u).st = FGSA.clock params (w u).st t := by
  fin_cases u <;>
    simp [tickBatch, nodes, List.foldl_cons] <;> apply i7_tick_st

/-- All node stores agree; own-signature records can differ. -/
def GenUniformStores (w : World) : Prop := ∀ u v, (w u).st = (w v).st

/-- One object preserves store agreement after its complete recipient list. -/
theorem w1_offer_uniform (t : Time) (acc : World × List Event) (o : Obj params)
    (hw : GenUniformStores acc.1) :
    GenUniformStores ((nodes.map (fun v => (v, o))).foldl (deliverOne t) acc).1 := by
  intro u v
  rw [w1_offer_st t acc o nodes (by decide), w1_offer_st t acc o nodes (by decide),
    ite_eq_left (nodes_complete u), ite_eq_left (nodes_complete v), hw u v]

/-- The object fold preserves store agreement without an acceptance premise. -/
theorem w1_objects_uniform (t : Time) (os : List (Obj params))
    (acc : World × List Event) (hw : GenUniformStores acc.1) :
    GenUniformStores ((os.flatMap (fun o => nodes.map (fun v => (v, o)))).foldl
      (deliverOne t) acc).1 := by
  induction os generalizing acc with
  | nil => exact hw
  | cons o os ih =>
    rw [List.flatMap_cons, List.foldl_append]
    exact ih _ (w1_offer_uniform t acc o hw)

/-- Each generated time block preserves store agreement. -/
theorem w1_batch_uniform (t : Time) (w : World) (hw : GenUniformStores w) :
    GenUniformStores (timeBatch t w).1 := by
  apply w1_objects_uniform
  intro u v
  rw [w1_tickBatch_st, w1_tickBatch_st, hw u v]

/-- Store agreement holds by symbolic induction over the prefix. -/
theorem w1_prefix_uniform (steps : Nat) : GenUniformStores (buildPrefix steps).1 := by
  induction steps with
  | zero => exact fun _ _ => rfl
  | succ steps ih => exact w1_batch_uniform _ _ ih

/-- Store agreement holds by symbolic induction over the suffix. -/
theorem w1_suffix_uniform (steps : Nat) : GenUniformStores (buildSuffix steps).1 := by
  induction steps with
  | zero => exact w1_prefix_uniform 248
  | succ steps ih => exact w1_batch_uniform _ _ ih

/-- A batch releases exactly the objects from its four independent ticks. -/
theorem w1_tickBatch_emits (t : Time) (w : World) (o : Obj params) :
    o ∈ (tickBatch t w).2 ↔
      ∃ v, o ∈ (V2.D.tick weakEnv (runData 263 []) (w v) v t).2 := by
  constructor
  · intro ho
    simp [tickBatch, nodes] at ho
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  · rintro ⟨v, hv⟩
    simp [tickBatch, nodes]
    fin_cases v
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hv))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hv))
    · exact List.mem_append_left _ (List.mem_append_right _ hv)
    · exact List.mem_append_right _ hv

/-- Every replayed generator store is reachable. -/
theorem w1_reachable (es : List Event) (u : Validator) :
    Reachable params (genFold V2.D.World.init es u).st := by
  have h := reachable_stateBefore weakEnv (runData 263 es) es.length u
  rwa [runData_stateBefore, List.take_length] at h

/-- An emitted proposal has a parent in the emitting store. -/
theorem w1_tick_deps (st : Node params) (v : Validator) (t : Time)
    (hr : Reachable params st.st) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 []) st v t).2) :
    depsS params (FGSA.clock params st.st t) o = true := by
  obtain ⟨l, j, m, rfl, _, ha⟩ := gen_tick_seat st v t o ho
  cases l with
  | headAction s =>
    have he : .head (headVote params (FGSA.clock params st.st t) s).root = m := Option.some.inj ha
    subst m
    rfl
  | fgAction r =>
    change (attest params (FGSA.clock params st.st t)
      st.record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    rfl
  | propAction s =>
    change (propose params (FGSA.clock params st.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.mp ha
      let pre := FGSA.clock params st.st t
      have hnamed := namedByErase?_sound pre _ P hP
      have hinv := (storeBundle_of_reachable params _ (Reachable.tick t hr)).cstore
      let H := getHead params pre (proposerVotes pre s) (proposerSupport pre s)
      obtain ⟨Q, hQ, he⟩ := (hinv.baseTree H).mp (getHead_stored params _ hinv _ _)
      have hlookup := (fgBlockOf_spec params pre hinv H Q).mpr ⟨hQ, he⟩
      change (decide (P ∈ pre.namedBodies) && (fgBlockOf pre P.erase).isSome) = true
      rw [hnamed.2, hlookup]
      simp only [Option.isSome_some, Bool.and_true, decide_eq_true_eq]
      exact hnamed.1

/-- Store agreement supplies proposal dependencies at every receiver after the ticks. -/
theorem w1_batch_deps_start (t : Time) (w : World) (hw : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (u : Validator) :
    depsS params ((tickBatch t w).1 u).st o = true := by
  obtain ⟨v, hv⟩ := (w1_tickBatch_emits t w o).1 ho
  rw [w1_tickBatch_st, hw u v]
  exact w1_tick_deps _ v t (hr v) o hv

/-- Dependencies persist when the FG store grows. -/
theorem w1_deps_mono {st st' : State params.n} (hT : st.fg.TF ⊆ st'.fg.TF)
    (hN : st.namedBodies ⊆ st'.namedBodies) (o : Obj params) (h : depsS params st o = true) :
    depsS params st' o = true := by
  unfold depsS at h ⊢
  cases hd : (toWire params o).decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body => rfl
    | block s b =>
      rw [hd] at h
      obtain ⟨hn, hp⟩ := Bool.and_eq_true_iff.mp h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true (hN (of_decide_eq_true hn)), ?_⟩
      obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp hp
      exact Option.isSome_iff_exists.mpr ⟨P,
        (parentFG_spec st' b.erase P).2
          ⟨hT ((parentFG_spec st b.erase P).1 hP).1,
            ((parentFG_spec st b.erase P).1 hP).2⟩⟩

/-- Any offered delivery preserves dependencies of every object. -/
theorem w1_deliver_deps (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) (o : Obj params)
    (h : depsS params (acc.1 u).st o = true) :
    depsS params ((deliverOne t acc vo).1 u).st o = true := by
  rw [w1_deliver_st]
  split
  · exact w1_deps_mono (process_cumulative params _ _).1
      (process_namedBodies_subset _ _) o h
  · exact h

/-- Dependency checks at every delivery in a list. -/
def GenDeps : World → List Event → Prop
  | _, [] => True
  | w, e :: es =>
      (match e with
        | .deliver v o _ => depsS params (w v).st o = true
        | _ => True) ∧
      GenDeps (V2.D.World.step weakEnv (runData 263 []) w e) es

theorem w1_deps_append (w : World) (es ds : List Event) :
    GenDeps w (es ++ ds) ↔ GenDeps w es ∧ GenDeps (genFold w es) ds := by
  induction es generalizing w with
  | nil => simp [GenDeps, genFold]
  | cons e es ih =>
    simp only [List.cons_append, GenDeps, ih, genFold, List.foldl_cons]
    tauto

/-- The delivery fold keeps the dependency checks in its accumulated trace. -/
theorem w1_delivery_fold_deps (t : Time) (xs : List (Validator × Obj params))
    (w : World) (acc : World × List Event) (hr : genFold w acc.2 = acc.1)
    (hd : GenDeps w acc.2)
    (hx : ∀ vo ∈ xs, depsS params (acc.1 vo.1).st vo.2 = true) :
    GenDeps w (xs.foldl (deliverOne t) acc).2 := by
  induction xs generalizing acc with
  | nil => exact hd
  | cons vo xs ih =>
    rw [List.foldl_cons]
    apply ih
    · unfold deliverOne
      split
      · exact hr
      · simp only [genFold_append, hr]
        rfl
    · unfold deliverOne
      split
      · exact hd
      · apply (w1_deps_append w acc.2 _).2
        exact ⟨hd, by simpa only [GenDeps, hr, and_true] using hx vo (List.mem_cons_self ..)⟩
    · intro vo' hm
      exact w1_deliver_deps t acc vo vo'.1 vo'.2 (hx vo' (List.mem_cons_of_mem _ hm))

theorem w1_ticks_deps (w : World) (t : Time) (vs : List Validator) :
    GenDeps w (vs.map (fun v => .tick v t)) := by
  induction vs generalizing w with
  | nil => trivial
  | cons v vs ih => exact ⟨trivial, ih _⟩

/-- I6 holds throughout a complete generated time block. -/
theorem w1_batch_deps (t : Time) (w : World) (hw : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) : GenDeps w (timeBatch t w).2 := by
  apply w1_delivery_fold_deps
  · exact tickBatch_replay t w
  · exact w1_ticks_deps w t nodes
  · intro vo hm
    obtain ⟨o, ho, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
    exact w1_batch_deps_start t w hw hr o ho v

/-- I6 for the source generator, by induction over time blocks. -/
theorem w1_prefix_deps (steps : Nat) : GenDeps V2.D.World.init (buildPrefix steps).2 := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    apply (w1_deps_append _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (prefix_replay_fresh steps).1]
    exact w1_batch_deps _ _ (w1_prefix_uniform steps) (fun v => by
      rw [(prefix_replay_fresh steps).1]
      exact w1_reachable _ v)

/-- I6 for the suffix generator, from the source's final store. -/
theorem w1_suffix_deps (steps : Nat) : GenDeps (buildPrefix 248).1 (buildSuffix steps).2 := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
    apply (w1_deps_append _ _ _).2
    refine ⟨ih, ?_⟩
    rw [← (suffix_replay_fresh steps).1]
    exact w1_batch_deps _ _ (w1_suffix_uniform steps) (fun v => by
      rw [(suffix_replay_fresh steps).1, (prefix_replay_fresh 248).1,
        ← genFold_append]
      exact w1_reachable _ v)

/-- Read a dependency check at an indexed delivery. -/
theorem w1_deps_get (w : World) (es : List Event) (hd : GenDeps w es)
    (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : es[i]? = some (.deliver v o t)) :
    depsS params (genFold w (es.take i) v).st o = true := by
  induction es generalizing w i with
  | nil => simp at he
  | cons e es ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst e
      exact hd.1
    | succ i => exact ih _ hd.2 i (by simpa using he)

attribute [irreducible] GenDeps

/-- The complete continuation has I6 at every delivery. -/
theorem w1_continuation_genDeps : GenDeps V2.D.World.init continuation.events := by
  change GenDeps V2.D.World.init ((buildPrefix 248).2 ++ (buildSuffix 16).2)
  rw [w1_deps_append, ← (prefix_replay_fresh 248).1]
  exact ⟨w1_prefix_deps 248, w1_suffix_deps 16⟩

set_option maxRecDepth 4096 in
/-- Proposal dependencies hold for the full continuation. -/
theorem w1_continuation_deps (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : continuation.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore weakEnv continuation i v) o
      = true := by
  change depsS params (genFold V2.D.World.init (continuation.events.take i) v).st o = true
  exact w1_deps_get V2.D.World.init continuation.events w1_continuation_genDeps i v o t hi

/-- Proposal dependencies hold for the source in its strong environment. -/
theorem w1_source_deps (i : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hi : source.events[i]? = some (.deliver v o t)) :
    (fgsa params unitCodec).depsPresent (V2.D.Run.stateBefore strongEnv source i v) o = true := by
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have hi' : continuation.events[i]? = some (.deliver v o t) := by
    change (source.events ++ (buildSuffix 16).2)[i]? = _
    rw [List.getElem?_append_left hil]
    exact hi
  have h := w1_continuation_deps i v o t hi'
  rw [source_replay (Nat.le_of_lt hil)] at h
  exact h

/-- All execution-validity fields hold for the source. -/
theorem w1_source_execution : V2.D.ExecutionValid strongEnv source where
  toScheduleWellFormed := source_schedule
  wire := w1_source_wire
  deps := w1_source_deps
  fresh := source_fresh
  toUnforgeableSignatures := source_signatures

/-- All execution-validity fields hold for the continuation. -/
theorem w1_continuation_execution : V2.D.ExecutionValid weakEnv continuation where
  toScheduleWellFormed := continuation_schedule
  wire := w1_continuation_wire
  deps := w1_continuation_deps
  fresh := continuation_fresh
  toUnforgeableSignatures := continuation_signatures


/-- The suffix is the next part of the same symbolic prefix generator. -/
theorem w1_suffix_eq (steps : Nat) :
    (buildSuffix steps).1 = (buildPrefix (248 + steps)).1 ∧
      (buildPrefix 248).2 ++ (buildSuffix steps).2 = (buildPrefix (248 + steps)).2 := by
  induction steps with
  | zero => exact ⟨rfl, List.append_nil _⟩
  | succ steps ih =>
    change (timeBatch (248 + steps : Nat) (buildSuffix steps).1).1 =
        (timeBatch (248 + steps : Nat) (buildPrefix (248 + steps)).1).1 ∧
      (buildPrefix 248).2 ++ ((buildSuffix steps).2 ++
        (timeBatch (248 + steps : Nat) (buildSuffix steps).1).2) =
        (buildPrefix (248 + steps)).2 ++
          (timeBatch (248 + steps : Nat) (buildPrefix (248 + steps)).1).2
    rw [ih.1, ← List.append_assoc, ih.2]
    exact ⟨rfl, rfl⟩

/-- Each finite nonempty generated prefix has the required schedule. -/
theorem w1_prefix_schedule (steps : Nat) :
    V2.D.ScheduleWellFormed weakEnv (runData steps (buildPrefix (steps + 1)).2) where
  horizon_nonneg := Int.natCast_nonneg _
  sorted := prefix_sorted _
  nodup := prefix_nodup _
  in_horizon e he := by
    obtain ⟨h0, ht⟩ := witness_prefix_times (steps + 1) e he
    change 0 ≤ e.time ∧ e.time ≤ (steps : Int)
    refine ⟨h0, ?_⟩
    have ht' : e.time < (steps : Int) + 1 := by exact_mod_cast ht
    exact Int.le_of_lt_add_one ht'
  honest_only _ _ := Finset.mem_univ _
  tick_public v t he := ⟨t.toNat, by
    have ht := (witness_prefix_times (steps + 1) (.tick v t) he).1
    change 0 ≤ t at ht
    change t = (t.toNat : Int) * 1
    rw [Int.toNat_of_nonneg ht, mul_one]⟩
  tick_total v _ t _ ht hh := by
    change t ≤ (steps : Int) at hh
    change (0 : Int) ≤ t at ht
    have hn : t.toNat < steps + 1 := by
      have hle : t.toNat ≤ steps := Int.toNat_le.mpr hh
      omega
    change V2.Event.tick v t ∈ (buildPrefix (steps + 1)).2
    simpa only [Int.toNat_of_nonneg ht] using prefix_tick (steps + 1) t.toNat hn v

/-- A single-duty signing key has one object in a trace with unique ticks. -/
def GenSingleDutyUnique (P : Obj params → Prop) : Prop :=
  ∀ l j o o', Gen.V2.Duty.SingleDuty (fgsa params unitCodec) l → P o → P o' → o.auth
    = .seat l j → o'.auth = .seat l j → o = o'

/-- Generated emissions satisfy single-duty key uniqueness by replay. -/
theorem w1_emits_unique (es : List Event) (hn : es.Nodup) :
    GenSingleDutyUnique (fun o => ∃ v t, GenEmits V2.D.World.init es v o t) := by
  rintro l j o o' hD ⟨v, t, he⟩ ⟨v', t', he'⟩ ha ha'
  have holder (x : Validator) (u : Time) (a : Obj params)
      (he : GenEmits V2.D.World.init es x a u) (ha : a.auth = .seat l j) :
      x = seatOf l j := by
    obtain ⟨pre, post, _, hm⟩ := he
    have hh := gen_tick_holder (genFold V2.D.World.init pre x) x u a hm
    rw [ha] at hh
    exact (Option.some.inj hh).symm
  have hv := holder v t o he ha
  have hv' := holder v' t' o' he' ha'
  obtain ⟨i, hi, ho⟩ := genEmits_runData 263 es v o t he
  obtain ⟨i', hi', ho'⟩ := genEmits_runData 263 es v' o' t' he'
  rw [hv] at hi
  rw [hv'] at hi'
  exact (Gen.V2.Duty.emitted_unique_of_singleDuty weakEnv (runData 263 es) hn
    l hD j (seatOf l j) i i' t t' o o' hi hi' ho ho' ha ha').2

/-- An honest current-slot HEAD is accepted, using key uniqueness in its pool. -/
theorem w1_head_accept (P : Obj params → Prop) (hu : GenSingleDutyUnique P)
    (st : State params.n) (hk : GenKnown P st) (s : Slot) (i : Fin params.n) (b : BlockId)
    (ho : P (ofHead params ⟨.seat (.head s) i, b⟩)) (hs : st.slot params = s) :
    processedS params (FGSA.process params st
      (toWire params (ofHead params ⟨.seat (.head s) i, b⟩)))
      (ofHead params ⟨.seat (.head s) i, b⟩) = true := by
  let a : HeadWire params.n := ⟨.seat (.head s) i, b⟩
  by_cases hm : baseVote a ∈ st.base.votes
  · have hp : processedS params st (ofHead params a) = true := decide_eq_true hm
    rw [w1_process_inert st _ hp]
    exact hp
  · have hempty : GridCO.seatVotes (GridCO.votesAt st.base s) i = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w hw hseat
      obtain ⟨hw, hlabel⟩ := List.mem_filter.mp hw
      have hl : GridCO.headLabel? w = some s := beq_iff_eq.mp hlabel
      have hi : GridCO.headSeat? w = some i := beq_iff_eq.mp hseat
      obtain ⟨auth, msg⟩ := w
      cases auth with
      | none => cases msg <;> cases hl
      | proposer r => cases msg <;> cases hl
      | seat r j =>
        cases msg with
        | proposal q raw sup => cases hl
        | head b' =>
          cases hl
          cases hi
          have hp : P (ofHead params ⟨.seat (.head s) i, b'⟩) :=
            hk.2.2 _ (List.mem_filterMap.mpr ⟨_, hw, rfl⟩)
          have he := hu (.base (.head s)) i _ _ (fgsa_head_singleDuty s) hp ho rfl rfl
          have hb : b' = b := Msg.head.inj (congrArg V2.Signed.payload he)
          subst b'
          exact hm hw
    have hx : GridCO.equivocates (GridCO.votesAt st.base s) i = false := by
      simp [GridCO.equivocates, hempty]
    have hs' : (st.base.now / (4 * params.toParams.engine.Δ)).toNat = s := hs
    change decide (baseVote a ∈ (admitHead params st s i b).base.votes) = true
    apply decide_eq_true
    change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∈ _
    change (⟨.seat s i, .head b⟩ : GridCO.Wire params.n .root) ∉ st.base.votes at hm
    simp [admitHead, GridCO.admitVote, hs', hm, hx, Nat.not_lt.mpr (Nat.sub_le s 1)]

/-- A decoded full row is accepted without a round or key-count condition. -/
theorem w1_row_accept (st : State params.n) (i : Fin params.n) (body : RowPayload) :
    processedS params (FGSA.process params st
      (toWire params (ofRow params ⟨.seat .fg i, body⟩)))
      (ofRow params ⟨.seat .fg i, body⟩) = true := by
  change decide ((⟨.seat .fg i, body⟩ : RowWire params.n) ∈
    (admitRow params st ⟨.seat .fg i, body⟩).rowPool) = true
  unfold admitRow
  dsimp only [RowWire.decode?]
  split <;> simp_all

/-- Processed objects stay processed when their pools and tree grow. -/
theorem w1_processed_mono {st st' : State params.n}
    (hv : st.base.votes ⊆ st'.base.votes) (hr : st.rowPool ⊆ st'.rowPool)
    (hT : st.fg.TF ⊆ st'.fg.TF) (o : Obj params) :
    processedS params st o = true → processedS params st' o = true := by
  dsimp only [processedS]
  cases (toWire params o).decode with
  | none => exact id
  | some m =>
    cases m with
    | vote s i b => simpa only [decide_eq_true_eq] using (fun h => hv h)
    | row i body => simpa only [decide_eq_true_eq] using (fun h => hr h)
    | block s b =>
      simp only [decide_eq_true_eq]
      rintro ⟨Y, hY, he⟩
      exact ⟨Y, hT hY, he⟩

/-- A handler call preserves every previously processed object. -/
theorem w1_process_processed (st : State params.n) (a o : Obj params)
    (h : processedS params st o = true) :
    processedS params (FGSA.process params st (toWire params a)) o = true := by
  have hc := process_cumulative params st (toWire params a)
  exact w1_processed_mono (process_votes_subset st (toWire params a))
    hc.2.2.2.2.2.subset hc.1 o h

/-- An offer preserves processed objects at every receiver. -/
theorem w1_deliver_processed (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) (o : Obj params)
    (h : processedS params (acc.1 u).st o = true) :
    processedS params ((deliverOne t acc vo).1 u).st o = true := by
  rw [w1_deliver_st]
  split
  · exact w1_process_processed _ _ _ h
  · exact h

theorem w1_fold_processed (t : Time) (xs : List (Validator × Obj params))
    (acc : World × List Event) (u : Validator) (o : Obj params)
    (h : processedS params (acc.1 u).st o = true) :
    processedS params ((xs.foldl (deliverOne t) acc).1 u).st o = true := by
  induction xs generalizing acc with
  | nil => exact h
  | cons vo xs ih => exact ih _ (w1_deliver_processed t acc vo u o h)

/-- Delivery does not change a receiver's clock. -/
theorem w1_deliver_now (t : Time) (acc : World × List Event)
    (vo : Validator × Obj params) (u : Validator) :
    ((deliverOne t acc vo).1 u).st.base.now = (acc.1 u).st.base.now := by
  rw [w1_deliver_st]
  split
  · exact process_base_now _ _
  · rfl

/-- Each offered object is processed if its current-time handler accepts it. -/
theorem w1_fold_complete (P : Obj params → Prop) (t : Time)
    (xs : List (Validator × Obj params)) (acc : World × List Event)
    (hk : ∀ u, GenKnown P (acc.1 u).st) (hn : ∀ u, (acc.1 u).st.base.now = t)
    (hc : ∀ vo ∈ xs, P vo.2 ∧ ∀ a, carriesS params vo.2 a → P a)
    (ha : ∀ vo ∈ xs, ∀ st, GenKnown P st → st.base.now = t →
      processedS params (FGSA.process params st (toWire params vo.2)) vo.2 = true) :
    ∀ vo ∈ xs, processedS params ((xs.foldl (deliverOne t) acc).1 vo.1).st vo.2 = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons vo xs ih =>
    have hk' : ∀ u, GenKnown P ((deliverOne t acc vo).1 u).st := by
      intro u
      rw [w1_deliver_st]
      split
      · exact gen_known_process P _ vo.2 (hk u)
          (hc vo (List.mem_cons_self ..)).1 (hc vo (List.mem_cons_self ..)).2
      · exact hk u
    have hn' : ∀ u, ((deliverOne t acc vo).1 u).st.base.now = t :=
      fun u => (w1_deliver_now t acc vo u).trans (hn u)
    intro vo' hm
    rcases List.mem_cons.mp hm with he | hm
    · subst vo'
      apply w1_fold_processed t xs (deliverOne t acc vo) vo.1 vo.2
      rw [w1_deliver_st, ite_eq_left rfl]
      exact ha vo (List.mem_cons_self ..) _ (hk vo.1) (hn vo.1)
    · exact ih _ hk' hn' (fun vo hm => hc vo (List.mem_cons_of_mem _ hm))
        (fun vo hm => ha vo (List.mem_cons_of_mem _ hm)) vo' hm

/-- A non-proposal emission is accepted by every current-time store with unique keys. -/
theorem w1_nonproposal_accept (P : Obj params → Prop) (hu : GenSingleDutyUnique P)
    (nd : Node params) (v : Validator) (t : Time) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 []) nd v t).2)
    (hP : P o) (hnot : ∀ b, o.payload ≠ .proposal b)
    (st : State params.n) (hk : GenKnown P st) (hn : st.base.now = t) :
    processedS params (FGSA.process params st (toWire params o)) o = true := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := gen_tick_seat nd v t o ho
  have ht := ((fgsa params unitCodec).duties_spec l t).1 hl
  cases l with
  | headAction s =>
    have he : .head (headVote params (FGSA.clock params nd.st t) s).root = m := Option.some.inj ha
    subst m
    apply w1_head_accept P hu st hk s j _ hP
    change params.slotOf st.base.now = s
    rw [hn, ← ht]
    exact (fgsa_vote_slot (c := unitCodec) nd s).symm.trans
      ((fgsa_postClock_slot (c := unitCodec) nd _).2) |>.symm
  | fgAction r =>
    change (attest params (FGSA.clock params nd.st t) nd.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact w1_row_accept st j body
  | propAction s =>
    change (propose params (FGSA.clock params nd.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

/-- Without a proposal, the complete batch accepts all its emitted HEADs and rows. -/
theorem w1_batch_nonproposal_complete (P : Obj params → Prop) (hu : GenSingleDutyUnique P)
    (t : Time) (w : World) (hk : ∀ v, GenKnown P (w v).st)
    (hp : ∀ o ∈ (tickBatch t w).2, P o)
    (hnot : ∀ o ∈ (tickBatch t w).2, ∀ b,
      o.payload ≠ .proposal b) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) :
    processedS params ((timeBatch t w).1 v).st o = true := by
  obtain ⟨hk', hc⟩ := gen_tick_fold_known P t nodes w [] hk (by simp)
  apply w1_fold_complete P t _ _ hk'
    (fun u => by rw [w1_tickBatch_st]; exact (clock_vn (w u).st t).2)
    (fun vo hm => ?_) (fun vo hm st hst hn => ?_) (v, o)
    (List.mem_flatMap.mpr ⟨o, ho, List.mem_map.mpr ⟨v, nodes_complete v, rfl⟩⟩)
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨hp a ha, hc a ha⟩
  · obtain ⟨a, ha, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hm
    obtain ⟨x, hx⟩ := (w1_tickBatch_emits t w a).1 ha
    exact w1_nonproposal_accept P hu (w x) x t a hx (hp a ha) (hnot a ha) st hst hn

/-- A proposal is the only object released at its time. -/
theorem w1_proposal_only (t : Time) (w : World) (v : Validator) (s : Slot)
    (j : Fin 1) (m : Msg params.n)
    (ho : (⟨.seat (.prop s) j, m⟩ : Obj params) ∈
      (V2.D.tick weakEnv (runData 263 []) (w v) v t).2)
    (o' : Obj params) (ho' : o' ∈ (tickBatch t w).2) :
    o' = ⟨.seat (.prop s) j, m⟩ := by
  have hv := gen_tick_holder (w v) v t _ ho
  have hv0 : v = 0 := (Option.some.inj hv).symm
  subst v
  have ha := (Gen.V2.Duty.mem_tick_singleDuty_iff weakEnv (runData 263 []) (w 0) 0 t
    (.prop s) (fgsa_prop_singleDuty s) (.propAction s) rfl j m).1 ho
  have ht : (4 : Int) * s = t := ha.2.1
  obtain ⟨v', hv'⟩ := (w1_tickBatch_emits t w o').1 ho'
  have holder := gen_tick_holder (w v') v' t o' hv'
  obtain ⟨l', j', m', rfl, hl', ha'⟩ := gen_tick_seat (w v') v' t o' hv'
  have ht' := ((fgsa params unitCodec).duties_spec l' t).1 hl'
  cases l' with
  | headAction r =>
    change (4 : Int) * r + 1 = t at ht'
    omega
  | fgAction r =>
    change (4 : Int) * ((r * 2 : Nat) : Int) + 6 = t at ht'
    omega
  | propAction s' =>
    change (4 : Int) * s' = t at ht'
    have he : s' = s := by
      have he : (s' : Int) = s := mul_left_cancel₀ (by decide : (4 : Int) ≠ 0)
        (ht'.trans ht.symm)
      exact_mod_cast he
    subst s'
    have hv0 : v' = 0 := (Option.some.inj holder).symm
    subst v'
    have hj : j' = j := Subsingleton.elim (α := Fin 1) _ _
    subst j'
    have hm : m' = m := Option.some.inj (ha'.symm.trans ha.2.2.2)
    subst m'
    rfl

/-- If a batch contains a proposal, its release list is a singleton. -/
theorem w1_proposal_singleton (t : Time) (w : World) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (b : NamedProposal params.n) (hp : o.payload = .proposal b) :
    (tickBatch t w).2 = [o] := by
  have hall : ∀ o' ∈ (tickBatch t w).2, o' = o := by
    obtain ⟨v, hv⟩ := (w1_tickBatch_emits t w o).1 ho
    obtain ⟨l, j, m, rfl, _, ha⟩ := gen_tick_seat (w v) v t o hv
    cases l with
    | headAction s =>
      have he : .head (headVote params (FGSA.clock params (w v).st t) s).root = m :=
        Option.some.inj ha
      subst m
      cases hp
    | fgAction r =>
      change (attest params (FGSA.clock params (w v).st t) (w v).record
          ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
      obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
      subst m
      cases hp
    | propAction s => exact fun o' ho' => w1_proposal_only t w v s j m hv o' ho'
  have hn := tickBatch_nodup t w
  generalize (tickBatch t w).2 = os at ho hall hn ⊢
  cases os with
  | nil => exact (List.not_mem_nil ho).elim
  | cons a os =>
    have he := hall a (List.mem_cons_self ..)
    subst a
    have hz : os = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro a ha
      have he := hall a (List.mem_cons_of_mem _ ha)
      exact hn.notMem (he ▸ ha)
    rw [hz]

/-- ROOT-DIGEST W3d. A fresh emitted proposal stores its exact body. -/
private theorem w1_proposal_admit (nd : Node params) (v : Validator) (t : Time) (o : Obj params)
    (hr : Reachable params nd.st)
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 []) nd v t).2)
    (hw : (fgsa params unitCodec).wellFormed o = true) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    processedS params
      (FGSA.process params (FGSA.clock params nd.st t) (toWire params o)) o = true ∧
      (processedS params nd.st o = false →
        b ∈ (FGSA.process params (FGSA.clock params nd.st t) (toWire params o)).namedBodies) := by
  obtain ⟨l, j, m, rfl, hl, ha⟩ := gen_tick_seat nd v t o ho
  cases l with
  | headAction s =>
    have he : .head (headVote params (FGSA.clock params nd.st t) s).root = m :=
      Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest params (FGSA.clock params nd.st t) nd.record
        ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ht : SA.proposalTime params.toParams s = t :=
      ((fgsa params unitCodec).duties_spec (.propAction s) t).1 hl
    change (propose params (FGSA.clock params nd.st t) s).map (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨Parent, hParent, rfl⟩ := Option.map_eq_some_iff.mp ha
      cases hp
      let st := FGSA.clock params nd.st t
      let H := getHead params st (proposerVotes st s) (proposerSupport st s)
      let rs := proposalRows params st H
      let N := namedProposal params Parent s 0
        ((proposerVotes st s).filterMap liftHead?)
        ((proposerSupport st s).filterMap liftHead?) rs
      have hnamed := namedByErase?_sound st H Parent hParent
      have hNamed : namedParentHeld st N = true := decide_eq_true hnamed.1
      have hinv := (storeBundle_of_reachable params st (Reachable.tick t hr)).cstore
      change FGSA.wellFormed params ⟨.proposer s, .proposal N⟩ = true at hw
      change processedS params (FGSA.process params st ⟨.proposer s, .proposal N⟩)
          (ofWire params ⟨.proposer s, .proposal N⟩) = true ∧
        (processedS params nd.st (ofWire params ⟨.proposer s, .proposal N⟩) = false →
          N ∈ (FGSA.process params st ⟨.proposer s, .proposal N⟩).namedBodies)
      by_cases hmem : ∃ Y ∈ st.fg.TF, Y.root = N.root
      · obtain ⟨Y, hY, he⟩ := hmem
        constructor
        · exact decide_eq_true ⟨Y, (process_cumulative params st _).1 hY, he⟩
        · intro hf
          change decide (∃ Z ∈ nd.st.fg.TF, Z.root = N.root) = false at hf
          have hY' : Y ∈ nd.st.fg.TF := by simpa only [st, clock_fg] using hY
          exact (of_decide_eq_false hf ⟨Y, hY', he⟩).elim
      · have hslot : N.erase.slot ≤ st.slot params := by
          have hs := fgsa_proposal_slot (c := unitCodec) nd s
          rw [ht] at hs
          exact le_of_eq hs.symm
        have hfresh : ∀ c ∈ st.base.blocks, c.root ≠ N.erase.root := by
          intro c hc he
          obtain ⟨Y, hY, rfl⟩ := (hinv.baseTree c).1 hc
          exact hmem ⟨Y, hY,
            (eraseFG_root Y).symm.trans (he.trans (named_erase_root N))⟩
        have hF : Block.Preceq (eraseFG st.fg.F) N.erase := by
          change (decide (eraseFG st.fg.F = N.erase) ||
            Block.preceq (eraseFG st.fg.F) Parent.erase) = true
          rw [hnamed.2]
          exact Bool.or_eq_true_iff.mpr (Or.inr
            (F_preceq_headInTree params st hinv _ _ _))
        have hvalid : ∀ Q, parentFG st N.erase = some Q →
            rowsValidForParent params Q N.erase.slot rs = true := by
          intro Q hQ
          have hs : st.slot params = s := by
            have hs := fgsa_proposal_slot (c := unitCodec) nd s
            rw [ht] at hs
            exact hs
          change fgBlockOf st Parent.erase = some Q at hQ
          rw [hnamed.2] at hQ
          change rowsValidForParent params Q s (proposalRows params st H) = true
          rw [proposalRows_eq_proposalRowsFor, ← hs]
          exact proposalRowsFor_valid params st (st.slot params) H Q hQ
        have hpar : N.erase.parent ∈ st.base.blocks := by
          change Parent.erase ∈ st.base.blocks
          rw [hnamed.2]
          exact getHead_stored params st hinv _ _
        obtain ⟨_, Q, hQ, hB⟩ := admitBlock_sufficient params st hinv s N hNamed hw
          hpar hslot hfresh hF hvalid
        have hacc : blockAccepted params st s N Q = true := by
          cases hacc : blockAccepted params st s N Q with
          | true => rfl
          | false =>
            have hproc := admitBlock_refused params st s N (Or.inr (Or.inr ⟨Q, hQ, hacc⟩))
            change fgBlock Q N.erase N.rows ∈ (admitBlock params st s N).fg.TF at hB
            rw [hproc] at hB
            exact (hmem ⟨_, hB, (fgBlock_root Q N.erase N.rows).trans
              (named_erase_root N)⟩).elim
        obtain ⟨pool, heq, _⟩ := admitBlock_accepted_eq params st s N Q hNamed hQ hacc
        refine ⟨decide_eq_true ⟨_, hB,
          (fgBlock_root Q N.erase N.rows).trans (named_erase_root N)⟩, fun _ => ?_⟩
        change N ∈ (admitBlock params st s N).namedBodies
        rw [heq]
        dsimp only
        split
        · apply (mem_namedBodies _ N).mpr
          exact Or.inr ⟨s, List.mem_append_right _ (List.mem_singleton_self _)⟩
        · apply (mem_namedBodies _ N).mpr
          right
          refine ⟨s, ?_⟩
          rw [(i7_reconcile_fields _).1]
          exact List.mem_append_right _ (List.mem_singleton_self _)

/-- The proposer accepts its own output in the common post-clock store. -/
theorem w1_proposal_accept (nd : Node params) (v : Validator) (t : Time) (o : Obj params)
    (hr : Reachable params nd.st)
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 []) nd v t).2)
    (hw : (fgsa params unitCodec).wellFormed o = true)
    (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    processedS params
      (FGSA.process params (FGSA.clock params nd.st t) (toWire params o)) o = true :=
  (w1_proposal_admit nd v t o hr ho hw b hp).1

/-- A proposal batch accepts its output at every receiver. -/
theorem w1_batch_proposal_complete (t : Time) (w : World) (hu : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) (o : Obj params)
    (ho : o ∈ (tickBatch t w).2) (hw : (fgsa params unitCodec).wellFormed o = true)
    (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) (v : Validator) :
    processedS params ((timeBatch t w).1 v).st o = true := by
  have hs := w1_proposal_singleton t w o ho b hp
  obtain ⟨u, he⟩ := (w1_tickBatch_emits t w o).1 ho
  have ha := w1_proposal_accept (w u) u t o (hr u) he hw b hp
  change processedS params ((((tickBatch t w).2.flatMap
    (fun a => nodes.map (fun u => (u, a)))).foldl (deliverOne t)
      ((tickBatch t w).1, nodes.map (fun u => .tick u t))).1 v).st o = true
  rw [hs, List.flatMap_singleton, w1_offer_st t _ o nodes (by decide),
    ite_eq_left (nodes_complete v), w1_tickBatch_st, hu v u]
  exact ha

/-- Embed a batch release in the generator trace that ends at that batch. -/
theorem w1_prefix_emits (steps : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2) :
    ∃ v, GenEmits V2.D.World.init (buildPrefix (steps + 1)).2 v o steps := by
  obtain ⟨v, hv⟩ := tickBatch_origin steps (buildPrefix steps).1 o ho
  obtain ⟨ds, he, _⟩ := timeBatch_block steps (buildPrefix steps).1
  have hb : GenEmits (buildPrefix steps).1
      (timeBatch steps (buildPrefix steps).1).2 v o steps := by
    rw [he]
    exact genEmits_append_left _ _ ds v o steps hv
  refine ⟨v, genEmits_append_right V2.D.World.init (buildPrefix steps).2 _ v o steps ?_⟩
  rwa [← (prefix_replay_fresh steps).1]

/-- The complete batch accepts every object that its ticks release. -/
theorem w1_batch_complete (P : Obj params → Prop) (hunique : GenSingleDutyUnique P)
    (t : Time) (w : World) (hu : GenUniformStores w)
    (hr : ∀ v, Reachable params (w v).st) (hk : ∀ v, GenKnown P (w v).st)
    (hP : ∀ o ∈ (tickBatch t w).2, P o)
    (hwf : ∀ o ∈ (tickBatch t w).2, (fgsa params unitCodec).wellFormed o = true)
    (v : Validator) (o : Obj params) (ho : o ∈ (tickBatch t w).2) :
    processedS params ((timeBatch t w).1 v).st o = true := by
  classical
  by_cases hp : ∃ a ∈ (tickBatch t w).2, ∃ b, a.payload = .proposal b
  · obtain ⟨a, ha, b, he⟩ := hp
    have hs := w1_proposal_singleton t w a ha b he
    have hoa : o = a := List.mem_singleton.mp (hs ▸ ho)
    subst o
    exact w1_batch_proposal_complete t w hu hr a ha (hwf a ha) b he v
  · apply w1_batch_nonproposal_complete P hunique t w hk hP _ v o ho
    intro a ha b he
    exact hp ⟨a, ha, b, he⟩

/-- I5: every node has processed each release when its time block is complete. -/
theorem w1_prefix_complete (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2) :
    processedS params ((buildPrefix (steps + 1)).1 v).st o = true := by
  let P := fun a => ∃ u t, GenEmits V2.D.World.init (buildPrefix (steps + 1)).2 u a t
  have hk : ∀ u, GenKnown P ((buildPrefix steps).1 u).st := by
    intro u
    apply gen_known_mono _ P _ ((gen_prefix_carried steps).1 u)
    rintro a ⟨x, t, _, he⟩
    exact ⟨x, t, genEmits_append_left V2.D.World.init (buildPrefix steps).2 _ x a t he⟩
  have hp : ∀ a ∈ (tickBatch steps (buildPrefix steps).1).2, P a := by
    intro a ha
    obtain ⟨u, hu⟩ := w1_prefix_emits steps a ha
    exact ⟨u, steps, hu⟩
  have hwf : ∀ a ∈ (tickBatch steps (buildPrefix steps).1).2,
      (fgsa params unitCodec).wellFormed a = true := by
    intro a ha
    obtain ⟨u, hu⟩ := w1_prefix_emits steps a ha
    exact w1_emit_wire steps _ (w1_prefix_schedule steps) (prefix_origin (steps + 1))
      (gen_prefix_carried (steps + 1)).2 u a steps (genEmits_runData steps _ u a steps hu)
  exact w1_batch_complete P (w1_emits_unique _ (prefix_nodup (steps + 1))) steps _
    (w1_prefix_uniform steps) (fun u => by
      rw [(prefix_replay_fresh steps).1]
      exact w1_reachable _ u) hk hp hwf v o ho

/-- I5 holds for every block of the continuation suffix as well. -/
theorem w1_suffix_complete (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch (248 + steps : Nat) (buildSuffix steps).1).2) :
    processedS params ((buildSuffix (steps + 1)).1 v).st o = true := by
  rw [(w1_suffix_eq steps).1] at ho
  rw [(w1_suffix_eq (steps + 1)).1]
  exact w1_prefix_complete (248 + steps) v o ho

/-- A single-duty signing label fixes its emission time. -/
theorem w1_emission_time (es : List Event) (v : Validator) (o : Obj params) (t : Time)
    (he : GenEmits V2.D.World.init es v o t) (d : RunDuty)
    (hD : Gen.V2.Duty.SingleDuty (fgsa params unitCodec) d.signLabel)
    (j : Fin (RunLabel.seats params d.signLabel))
    (ha : o.auth = .seat d.signLabel j) : RunDuty.actTime params d = t := by
  obtain ⟨pre, post, _, ho⟩ := he
  obtain ⟨auth, payload⟩ := o
  dsimp only at ha
  subst auth
  exact ((Gen.V2.Duty.mem_tick_singleDuty_iff weakEnv (runData 263 [])
    (genFold V2.D.World.init pre v) v t d.signLabel hD d rfl j payload).1 ho).2.1

/-- A release from the actual prefix state has no earlier emission.
For FG rows, the durable sent set supplies this fact. -/
theorem w1_not_past (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 []) ((buildPrefix steps).1 v) v steps).2) :
    ¬ GenPast (buildPrefix steps).2 steps o := by
  have hh := gen_tick_holder ((buildPrefix steps).1 v) v steps o ho
  obtain ⟨d, j, m, rfl, hd, ha⟩ := gen_tick_seat ((buildPrefix steps).1 v) v steps o ho
  have ht := ((fgsa params unitCodec).duties_spec d steps).1 hd
  rintro ⟨u, t, _, he⟩
  have no_single (hD : Gen.V2.Duty.SingleDuty (fgsa params unitCodec) d.signLabel) : False := by
    have heTime := w1_emission_time _ u _ t he d hD j rfl
    obtain ⟨pre, post, hes, _⟩ := he
    have hm : V2.Event.tick u t ∈ (buildPrefix steps).2 := by rw [hes]; simp
    have hlt := (witness_prefix_times steps (.tick u t) hm).2
    change t < (steps : Int) at hlt
    exact (lt_irrefl (steps : Int)) ((ht.symm.trans heTime) ▸ hlt)
  cases d with
  | headAction s => exact no_single (fgsa_head_singleDuty s)
  | propAction s => exact no_single (fgsa_prop_singleDuty s)
  | fgAction r =>
    change (attest params (FGSA.clock params ((buildPrefix steps).1 v).st steps)
      ((buildPrefix steps).1 v).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    have hu : u = v := by
      obtain ⟨pre, post, _, hem⟩ := he
      have hhu := gen_tick_holder (genFold V2.D.World.init pre u) u t _ hem
      exact Option.some.inj (hhu.symm.trans hh)
    subst u
    obtain ⟨i, hi, hem⟩ := genEmits_runData 263 (buildPrefix steps).2 v _ t he
    have hsent := fgsa_row_sent_before weakEnv (runData 263 (buildPrefix steps).2)
      v j body (List.getElem?_eq_some_iff.mp hi).1 t hi hem
    change (body.height_pair, body.finality_pair) ∈
      (genFold V2.D.World.init ((buildPrefix steps).2.take
        (buildPrefix steps).2.length) v).record.sent
      at hsent
    rw [List.take_length, ← (prefix_replay_fresh steps).1] at hsent
    exact (attest_some_fresh _ _ _ _ hb) hsent

/-- The clock preserves the processed predicate exactly. -/
theorem w1_clock_processed (st : State params.n) (t : Time) (o : Obj params) :
    processedS params (FGSA.clock params st t) o = processedS params st o := by
  unfold processedS
  rw [i7_clock_votes, i7_clock_rowPool, clock_fg]

/-- Knowledge can be tracked separately for each receiver. -/
theorem w1_known_fold_local (P : Validator → Obj params → Prop) (w : World)
    (es : List Event) (hk : ∀ v, GenKnown (P v) (w v).st)
    (he : ∀ v o t, V2.Event.deliver v o t ∈ es →
      P v o ∧ ∀ a, carriesS params o a → P v a) :
    ∀ v, GenKnown (P v) (genFold w es v).st := by
  induction es generalizing w with
  | nil => exact hk
  | cons e es ih =>
    apply ih
    · intro u
      cases e with
      | restart v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact ⟨by simp [fgsa, initial], by simp [GenStoredRows, fgsa, initial],
            by simp [fgsa, initial, GridCO.initial]⟩
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
      | tick v t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact (i7_tick_st (w v) v t).symm ▸ gen_known_clock (P v) _ t (hk v)
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
      | deliver v o t =>
        by_cases hu : u = v
        · subst u
          simp only [V2.D.World.step, Function.update_self]
          exact gen_known_process (P v) _ o (hk v)
            (he v o t (List.mem_cons_self ..)).1 (he v o t (List.mem_cons_self ..)).2
        · simpa only [V2.D.World.step, Function.update_of_ne hu] using hk u
    · intro v o t hm
      exact he v o t (List.mem_cons_of_mem _ hm)

/-- Each stored non-proposal after the batch was known before or delivered in this batch. -/
theorem w1_batch_known_receipt (steps : Nat) (v : Validator) :
    GenKnown (fun o => GenPast (buildPrefix steps).2 steps o ∨
      V2.Event.deliver v o steps ∈ (timeBatch steps (buildPrefix steps).1).2)
      ((timeBatch steps (buildPrefix steps).1).1 v).st := by
  rw [(timeBatch_replay_fresh _ _).1]
  apply w1_known_fold_local (fun u o => GenPast (buildPrefix steps).2 steps o ∨
    V2.Event.deliver u o steps ∈ (timeBatch steps (buildPrefix steps).1).2)
  · intro u
    exact gen_known_mono _ _ _ ((gen_prefix_carried steps).1 u) (fun _ h => Or.inl h)
  · intro u o t hm
    obtain ⟨rfl, ho⟩ := gen_timeBatch_delivered steps (buildPrefix steps).1 u o t hm
    refine ⟨Or.inr hm, fun a hc => Or.inl ?_⟩
    exact (gen_tick_fold_known (GenPast (buildPrefix steps).2 steps) steps nodes
      (buildPrefix steps).1 [] (gen_prefix_carried steps).1 (by simp)).2 o ho a hc

/-- Every HEAD and row release is directly delivered to each receiver at that time. -/
theorem w1_nonproposal_receipt (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2)
    (hnot : ∀ b, o.payload ≠ .proposal b) :
    V2.Event.deliver v o steps ∈ (timeBatch steps (buildPrefix steps).1).2 := by
  have hp := w1_prefix_complete steps v o ho
  have hk := w1_batch_known_receipt steps v
  obtain ⟨u, hu⟩ := (w1_tickBatch_emits steps (buildPrefix steps).1 o).1 ho
  have hn := w1_not_past steps u o hu
  obtain ⟨l, j, m, rfl, _, ha⟩ := gen_tick_seat ((buildPrefix steps).1 u) u steps o hu
  cases l with
  | headAction s =>
    have he : .head (headVote params
        (FGSA.clock params ((buildPrefix steps).1 u).st steps) s).root = m := Option.some.inj ha
    subst m
    have hm := of_decide_eq_true hp
    have hh := hk.2.2 _ (List.mem_filterMap.mpr ⟨_, hm, rfl⟩)
    exact hh.resolve_left hn
  | fgAction r =>
    change (attest params (FGSA.clock params ((buildPrefix steps).1 u).st steps)
        ((buildPrefix steps).1 u).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    exact (hk.1 _ (of_decide_eq_true hp)).resolve_left hn
  | propAction s =>
    change (propose params (FGSA.clock params ((buildPrefix steps).1 u).st steps) s).map
      (withApp params 0) = some m at ha
    unfold propose at ha
    split at ha
    · cases ha
    · simp only [Option.map_map] at ha
      obtain ⟨parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
      exact (hnot _ rfl).elim

/-- Without a local delivery or restart, replay preserves processed objects exactly. -/
theorem w1_fold_no_local (w : World) (es : List Event) (v : Validator) (o : Obj params)
    (hd : ∀ a t, V2.Event.deliver v a t ∉ es)
    (hr : ∀ t, V2.Event.restart v t ∉ es) :
    processedS params (genFold w es v).st o = processedS params (w v).st o := by
  induction es generalizing w with
  | nil => rfl
  | cons e es ih =>
    rw [show genFold w (e :: es) =
      genFold (V2.D.World.step weakEnv (runData 263 []) w e) es from rfl,
      ih _ (fun a t hm => hd a t (List.mem_cons_of_mem _ hm))
        (fun t hm => hr t (List.mem_cons_of_mem _ hm))]
    cases e with
    | restart u t =>
      have hne : v ≠ u := by intro he; subst u; exact hr t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | deliver u a t =>
      have hne : v ≠ u := by intro he; subst u; exact hd a t (List.mem_cons_self ..)
      simp only [V2.D.World.step, Function.update_of_ne hne]
    | tick u t =>
      by_cases he : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact (i7_tick_st (w v) v t).symm ▸ w1_clock_processed (w v).st t o
      · simp only [V2.D.World.step, Function.update_of_ne he]

/-- Node zero's proposal tick is the first event of its time block. -/
theorem w1_prefix_tick_zero (steps : Nat) :
    (buildPrefix (steps + 1)).2[(buildPrefix steps).2.length]? = some (.tick 0 steps) ∧
      genFold V2.D.World.init
        ((buildPrefix (steps + 1)).2.take (buildPrefix steps).2.length) =
          (buildPrefix steps).1 := by
  obtain ⟨ds, he, _⟩ := timeBatch_block steps (buildPrefix steps).1
  change ((buildPrefix steps).2 ++ (timeBatch steps (buildPrefix steps).1).2)[
    (buildPrefix steps).2.length]? = _ ∧ _
  constructor
  · rw [he]
    simp [nodes]
  · change genFold V2.D.World.init
      (((buildPrefix steps).2 ++ (timeBatch steps (buildPrefix steps).1).2).take
        (buildPrefix steps).2.length) = _
    rw [List.take_append_length]
    exact (prefix_replay_fresh steps).1.symm

/-- ROOT-DIGEST W3d. A stored non-genesis root has the fixture slot digest. -/
private theorem w1_stored_digest (st : State params.n) (hr : Reachable params st)
    (Y : SimplexFG.FGBlock (Fin params.n)) (hY : Y ∈ st.fg.TF) :
    Y = .genesis ∨ Y.root = ⟨Y.slot + 1⟩ := by
  by_cases hg : Y = .genesis
  · exact Or.inl hg
  · right
    have hs := storeBundle_of_reachable params st hr
    obtain ⟨s, N, hw, hErase, _⟩ := stored_wire_of_block params st hs.cstore hs.«meta» hY hg
    obtain ⟨s', M, he, hc, _⟩ := hs.«meta».wireTree _ hw
    have hp := Msg.proposal.inj (congrArg (fun w : Wire params.n => w.payload) he)
    cases hp
    unfold namedContentOk at hc
    rw [hErase] at hc
    have hd := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hc).2
    dsimp only [params, proposalInput] at hd
    exact (eraseFG_root Y).symm.trans
      (hd.trans (congrArg (fun r : Nat => (⟨r + 1⟩ : BlockId)) (eraseFG_slot Y)))

/-- A generated proposal is not already processed before its time block. -/
theorem w1_proposal_fresh_start (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    processedS params ((buildPrefix steps).1 v).st o = false := by
  obtain ⟨u, hu⟩ := (w1_tickBatch_emits steps (buildPrefix steps).1 o).1 ho
  have hu0 := (gen_tick_proposal_rows ((buildPrefix steps).1 u) u steps o hu b hp).1
  subst u
  obtain ⟨l, j, m, rfl, hl, ha⟩ := gen_tick_seat ((buildPrefix steps).1 0) 0 steps o hu
  cases l with
  | headAction s =>
    have he : .head (headVote params
        (FGSA.clock params ((buildPrefix steps).1 0).st steps) s).root = m := Option.some.inj ha
    subst m
    cases hp
  | fgAction r =>
    change (attest params (FGSA.clock params ((buildPrefix steps).1 0).st steps)
        ((buildPrefix steps).1 0).record ⟨0, params.nPos⟩).1.map Msg.row = some m at ha
    obtain ⟨body, hb, hm⟩ := Option.map_eq_some_iff.mp ha
    subst m
    cases hp
  | propAction s =>
    have ht : SA.proposalTime params.toParams s = steps :=
      ((fgsa params unitCodec).duties_spec (.propAction s) steps).1 hl
    have hs0 : 0 < s := by
      by_contra hn
      have hz : s = 0 := Nat.eq_zero_of_not_pos hn
      subst s
      cases ha
    have hi := (w1_prefix_tick_zero steps).1
    rw [← ht] at hi
    have hb := (fgsa_stored_block_slots weakEnv
      (runData steps (buildPrefix (steps + 1)).2) (w1_prefix_schedule steps) hi hs0).2.2.1
    change ∀ B ∈ (genFold V2.D.World.init
      ((buildPrefix (steps + 1)).2.take (buildPrefix steps).2.length) 0).st.fg.TF, B.slot < s at hb
    rw [(w1_prefix_tick_zero steps).2] at hb
    change (propose params (FGSA.clock params ((buildPrefix steps).1 0).st steps) s).map
      (withApp params 0) = some m at ha
    unfold propose at ha
    rw [ite_eq_right (Nat.ne_of_gt hs0)] at ha
    simp only [Option.map_map] at ha
    obtain ⟨Parent, _, rfl⟩ := Option.map_eq_some_iff.mp ha
    cases hp
    change decide (∃ Y ∈ ((buildPrefix steps).1 v).st.fg.TF,
      Y.root = (⟨s + 1⟩ : BlockId)) = false
    apply decide_eq_false
    rintro ⟨Y, hY, he⟩
    rw [w1_prefix_uniform steps v 0] at hY
    have hslot := hb Y hY
    have hr : Reachable params ((buildPrefix steps).1 0).st := by
      rw [(prefix_replay_fresh steps).1]
      exact w1_reachable _ 0
    rcases w1_stored_digest _ hr Y hY with hg | hd
    · subst Y
      have hz := congrArg BlockId.value he
      change 0 = s + 1 at hz
      exact Nat.noConfusion hz
    · have hs := congrArg BlockId.value (hd.symm.trans he)
      change Y.slot + 1 = s + 1 at hs
      exact (Nat.lt_irrefl s) ((Nat.add_right_cancel hs) ▸ hslot)

/-- Every proposal release is directly delivered to every receiver at that time. -/
theorem w1_proposal_receipt (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2) (b : NamedProposal params.n)
    (hp : o.payload = .proposal b) :
    V2.Event.deliver v o steps ∈ (timeBatch steps (buildPrefix steps).1).2 := by
  by_contra hn
  have hs := w1_proposal_singleton steps (buildPrefix steps).1 o ho b hp
  have hd : ∀ a t, V2.Event.deliver v a t ∉ (timeBatch steps (buildPrefix steps).1).2 := by
    intro a t hm
    obtain ⟨rfl, ha⟩ := gen_timeBatch_delivered steps (buildPrefix steps).1 v a t hm
    have he : a = o := List.mem_singleton.mp (hs ▸ ha)
    exact hn (he ▸ hm)
  have he := w1_fold_no_local (buildPrefix steps).1
    (timeBatch steps (buildPrefix steps).1).2 v o hd
    (timeBatch_no_restart steps (buildPrefix steps).1 v)
  rw [← (timeBatch_replay_fresh _ _).1, w1_proposal_fresh_start steps v o ho b hp]
    at he
  have ht := w1_prefix_complete steps v o ho
  exact Bool.noConfusion (ht.symm.trans he)

/-- Broadcast: each release has a direct same-time delivery to every node. -/
theorem w1_batch_receipt (steps : Nat) (v : Validator) (o : Obj params)
    (ho : o ∈ (tickBatch steps (buildPrefix steps).1).2) :
    V2.Event.deliver v o steps ∈ (timeBatch steps (buildPrefix steps).1).2 := by
  classical
  by_cases hp : ∃ b, o.payload = .proposal b
  · obtain ⟨b, hp⟩ := hp
    exact w1_proposal_receipt steps v o ho b hp
  · exact w1_nonproposal_receipt steps v o ho (fun b he => hp ⟨b, he⟩)

/-- A tick in a time block reads its own unchanged input node. -/
theorem w1_batch_tick_state (t : Time) (w : World) (i : Nat) (v : Validator) (u : Time)
    (he : (timeBatch t w).2[i]? = some (.tick v u)) :
    u = t ∧ genFold w ((timeBatch t w).2.take i) v = w v := by
  have hut : u = t := timeBatch_time t w (.tick v u) (List.mem_of_getElem? he)
  subst u
  obtain ⟨ds, hes, _⟩ := timeBatch_block t w
  have hv : (timeBatch t w).2[v.val]? = some (.tick v t) := by
    rw [hes]
    fin_cases v <;> simp [nodes]
  have hi : i = v.val :=
    (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp he).1 (timeBatch_nodup t w)).1
      (he.trans hv.symm)
  subst i
  refine ⟨rfl, ?_⟩
  rw [hes]
  fin_cases v <;> simp [nodes, genFold, V2.D.World.step]

/-- Locate every indexed emission in its generated time block. -/
theorem w1_locate_emission (steps : Nat) (i : Nat) (v : Validator) (t : Time)
    (o : Obj params) (hi : (buildPrefix steps).2[i]? = some (.tick v t))
    (ho : o ∈ (V2.D.tick weakEnv (runData 263 [])
      (genFold V2.D.World.init ((buildPrefix steps).2.take i) v) v t).2) :
    ∃ n < steps, t = n ∧ o ∈ (tickBatch n (buildPrefix n).1).2 := by
  induction steps generalizing i with
  | zero => simp [buildPrefix] at hi
  | succ steps ih =>
    change ((buildPrefix steps).2 ++ (timeBatch steps (buildPrefix steps).1).2)[i]? = _ at hi
    change o ∈ (V2.D.tick weakEnv (runData 263 []) (genFold V2.D.World.init
      (((buildPrefix steps).2 ++ (timeBatch steps (buildPrefix steps).1).2).take i) v) v t).2 at ho
    by_cases hil : i < (buildPrefix steps).2.length
    · rw [List.getElem?_append_left hil] at hi
      rw [List.take_append_of_le_length (Nat.le_of_lt hil)] at ho
      obtain ⟨n, hn, ht, hm⟩ := ih i hi ho
      exact ⟨n, Nat.lt_succ_of_lt hn, ht, hm⟩
    · have hil' := Nat.le_of_not_lt hil
      rw [List.getElem?_append_right hil'] at hi
      rw [List.take_append, List.take_of_length_le hil', genFold_append,
        ← (prefix_replay_fresh steps).1] at ho
      obtain ⟨rfl, hs⟩ := w1_batch_tick_state steps (buildPrefix steps).1 _ v t hi
      rw [hs] at ho
      exact ⟨steps, Nat.lt_succ_self _, rfl, (w1_tickBatch_emits _ _ o).2 ⟨v, ho⟩⟩

/-- A generated emission has a direct same-time delivery to each receiver. -/
theorem w1_prefix_broadcast (steps : Nat) (v : Validator) (o : Obj params) (t : Time)
    (he : V2.D.Run.emits weakEnv (runData steps (buildPrefix (steps + 1)).2) v o t)
    (u : Validator) :
    V2.Event.deliver u o t ∈ (buildPrefix (steps + 1)).2 := by
  obtain ⟨i, hi, ho⟩ := he
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := w1_locate_emission (steps + 1) i v t o hi ho
  rw [prefix_blocks]
  exact List.mem_flatMap.mpr ⟨n, List.mem_range.mpr hn, w1_batch_receipt n u o hm⟩

/-- Replay without restarts preserves every processed object. -/
theorem w1_fold_stable (w : World) (es : List Event) (v : Validator) (o : Obj params)
    (hr : ∀ u t, V2.Event.restart u t ∉ es)
    (hp : processedS params (w v).st o = true) :
    processedS params (genFold w es v).st o = true := by
  induction es generalizing w with
  | nil => exact hp
  | cons e es ih =>
    apply ih _ (fun u t hm => hr u t (List.mem_cons_of_mem _ hm))
    cases e with
    | restart u t => exact (hr u t (List.mem_cons_self ..)).elim
    | tick u t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        have he : processedS params (FGSA.clock params (w v).st t) o = true := by
          rw [w1_clock_processed]
          exact hp
        exact (i7_tick_st (w v) v t).symm ▸ he
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp
    | deliver u a t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact w1_process_processed _ _ _ hp
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hp

/-- Earlier generated traces are literal event prefixes. -/
theorem w1_prefix_prefix (m n : Nat) (h : m ≤ n) :
    (buildPrefix m).2.IsPrefix (buildPrefix n).2 := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact List.prefix_refl _
  | succ n ih =>
    by_cases he : m = n + 1
    · subst m; exact List.prefix_refl _
    · exact (ih (by omega)).trans ⟨(timeBatch n (buildPrefix n).1).2, rfl⟩

/-- A processed object remains processed at every later generator boundary. -/
theorem w1_prefix_stable (m n : Nat) (hmn : m ≤ n) (v : Validator) (o : Obj params)
    (hp : processedS params ((buildPrefix m).1 v).st o = true) :
    processedS params ((buildPrefix n).1 v).st o = true := by
  obtain ⟨ds, he⟩ := w1_prefix_prefix m n hmn
  rw [(prefix_replay_fresh n).1, ← he, genFold_append, ← (prefix_replay_fresh m).1]
  apply w1_fold_stable _ ds v o _ hp
  intro u t hm
  apply prefix_no_restart n u t
  rw [← he]
  exact List.mem_append_right _ hm

/-- At every boundary, all nodes have processed all prior generated emissions. -/
theorem w1_past_complete (steps : Nat) (o : Obj params) (t : Time)
    (he : GenPast (buildPrefix steps).2 t o) (v : Validator) :
    processedS params ((buildPrefix steps).1 v).st o = true := by
  obtain ⟨u, s, _, he⟩ := he
  obtain ⟨i, hi, ho⟩ := genEmits_runData 263 _ u o s he
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, _, hm⟩ := w1_locate_emission steps i u s o hi ho
  exact w1_prefix_stable (n + 1) steps hn v o (w1_prefix_complete n v o hm)

/-- An event at time at least `m` is after the boundary for times below `m`. -/
theorem w1_index_after (steps m i : Nat) (hm : m ≤ steps) (e : Event)
    (hi : (buildPrefix steps).2[i]? = some e) (ht : (m : Int) ≤ e.time) :
    (buildPrefix m).2.length ≤ i := by
  obtain ⟨ds, he⟩ := w1_prefix_prefix m steps hm
  by_contra hn
  have hl : i < (buildPrefix m).2.length := Nat.lt_of_not_ge hn
  rw [← he, List.getElem?_append_left hl] at hi
  exact (not_lt.mpr ht) (witness_prefix_times m e (List.mem_of_getElem? hi)).2

/-- Boundary completeness persists through any later event prefix. -/
theorem w1_index_stable (steps m i : Nat) (hm : m ≤ steps)
    (hi : (buildPrefix m).2.length ≤ i) (v : Validator) (o : Obj params)
    (hp : processedS params ((buildPrefix m).1 v).st o = true) :
    processedS params (genFold V2.D.World.init ((buildPrefix steps).2.take i) v).st o = true := by
  obtain ⟨ds, he⟩ := w1_prefix_prefix m steps hm
  rw [← he, List.take_append, List.take_of_length_le hi, genFold_append,
    ← (prefix_replay_fresh m).1]
  apply w1_fold_stable _ _ v o _ hp
  intro u t hmem
  apply prefix_no_restart steps u t
  rw [← he]
  exact List.mem_append_right _ (List.mem_of_mem_take hmem)

/-- A handled object is the envelope or one of its carried objects. -/
theorem w1_handles_carries (st : State params.n) (a o : Obj params)
    (hh : handlesS params st a o) : a = o ∨ carriesS params a o := by
  rcases hh with he | hh
  · exact Or.inl he
  · generalize hd : (toWire params a).decode = d at hh
    cases d with
    | none => exact hh.elim
    | some m =>
      cases m with
      | vote s i b => exact hh.elim
      | row i body => exact hh.elim
      | block s b =>
        have he := i7_decode_proposal a s b hd
        right
        simp only [carriesS, he]
        exact hh.2.elim Or.inl (fun hm => Or.inr (Or.inr hm))

/-- Every carried child of a delivery was processed by all receivers before this block. -/
theorem w1_child_processed (steps i : Nat) (v u : Validator) (a o : Obj params) (t : Time)
    (hi : (buildPrefix steps).2[i]? = some (.deliver v a t))
    (hc : carriesS params a o) :
    processedS params
      (genFold V2.D.World.init ((buildPrefix steps).2.take (i + 1)) u).st o = true := by
  have hm := List.mem_of_getElem? hi
  rw [prefix_blocks] at hm
  obtain ⟨n, hn, hm⟩ := List.mem_flatMap.mp hm
  have hn' : n < steps := List.mem_range.mp hn
  obtain ⟨rfl, ha⟩ := gen_timeBatch_delivered n (buildPrefix n).1 v a t hm
  have hp : GenPast (buildPrefix n).2 n o :=
    (gen_tick_fold_known (GenPast (buildPrefix n).2 n) n nodes (buildPrefix n).1 []
      (gen_prefix_carried n).1 (by simp)).2 a ha o hc
  apply w1_index_stable steps n (i + 1) (Nat.le_of_lt hn')
  · exact (w1_index_after steps n i (Nat.le_of_lt hn') _ hi le_rfl).trans (Nat.le_succ i)
  · exact w1_past_complete n o n hp u

/-- Relay: a receiver still missing a handled object gets a same-time direct delivery. -/
theorem w1_prefix_relay (steps i : Nat) (v u : Validator) (a o : Obj params) (t : Time)
    (hi : (buildPrefix (steps + 1)).2[i]? = some (.deliver v a t))
    (hh : a = o ∨ carriesS params a o)
    (hp : processedS params
      (genFold V2.D.World.init ((buildPrefix (steps + 1)).2.take (i + 1)) u).st o = false) :
    V2.Event.deliver u o t ∈ (buildPrefix (steps + 1)).2 := by
  rcases hh with rfl | hc
  · obtain ⟨x, hx⟩ := prefix_origin (steps + 1) v a t (List.mem_of_getElem? hi)
    exact w1_prefix_broadcast steps x a t (genEmits_runData steps _ x a t hx) u
  · have ht := w1_child_processed (steps + 1) i v u a o t hi hc
    exact Bool.noConfusion (hp.symm.trans ht)

/-- A direct delivery is a handler call in every environment. -/
theorem w1_direct_handle (E : Generic.Env Validator) (h : Time) (es : List Event)
    (v : Validator) (o : Obj params) (t : Time) (hm : V2.Event.deliver v o t ∈ es) :
    ∃ i, V2.D.Run.handlesAt E (runData h es) i v o t := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact ⟨i, o, hi, Or.inl rfl⟩

/-- Each nonempty generated prefix satisfies both partial-synchrony clauses. -/
theorem w1_prefix_sync (steps : Nat) :
    V2.D.PartialSynchrony weakEnv (runData steps (buildPrefix (steps + 1)).2) where
  broadcast_emitted v _ o t he u _ _ _ := by
    refine ⟨t, le_rfl, ?_, w1_direct_handle weakEnv _ _ u o t
      (w1_prefix_broadcast steps v o t he u)⟩
    change t < max t 0 + 1
    exact Int.lt_add_one_iff.mpr (le_max_left _ _)
  relay_accepted v _ i o t ha u _ hp _ _ := by
    obtain ⟨⟨a, hi, hh⟩, _, _⟩ := ha
    have hc := w1_handles_carries _ a o hh
    refine ⟨t, le_rfl, ?_, w1_direct_handle weakEnv _ _ u o t
      (w1_prefix_relay steps i v u a o t hi hc hp)⟩
    change t < max t 0 + 1
    exact Int.lt_add_one_iff.mpr (le_max_left _ _)

/-- The source replay agrees in the two environments at every covered event prefix. -/
theorem w1_source_state (i : Nat) (hi : i ≤ source.events.length) :
    V2.D.Run.stateBefore weakEnv source i = V2.D.Run.stateBefore strongEnv source i := by
  have ha : AgreesThrough₂ params unitCodec strongEnv source weakEnv source 1 :=
    { honest := rfl, gst := rfl, delta := rfl, seats := rfl, inputs := fun _ _ _ => rfl,
      awake := fun v t ht => awake_agreement v t ht, events := by simp,
      suffixTime := by simp }
  exact replay_of_agreement ha (fun e he => (source_in_horizon e he).2) hi

/-- Source emissions also agree in the reverse direction. -/
theorem w1_source_emits (v : Validator) (o : Obj params) (t : Time)
    (he : V2.D.Run.emits strongEnv source v o t) : V2.D.Run.emits weakEnv source v o t := by
  obtain ⟨i, hi, ho⟩ := he
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  have ht := (source_in_horizon _ (List.mem_of_getElem? hi)).2
  refine ⟨i, hi, ?_⟩
  simp only [V2.D.Run.emitsAt, hi] at ho ⊢
  rw [w1_source_state i (Nat.le_of_lt hil)]
  simpa only [V2.D.tick, awake_agreement v t ht] using ho

set_option maxRecDepth 4096 in
/-- The source satisfies the synchrony premise in its strong environment. -/
theorem w1_source_sync : V2.D.PartialSynchrony strongEnv source where
  broadcast_emitted v _ o t he u _ _ _ := by
    have hm := w1_prefix_broadcast 247 v o t (w1_source_emits v o t he) u
    refine ⟨t, le_rfl, ?_, w1_direct_handle strongEnv 247 _ u o t hm⟩
    change t < max t 0 + 1
    exact Int.lt_add_one_iff.mpr (le_max_left _ _)
  relay_accepted v _ i o t ha u _ hp _ _ := by
    obtain ⟨⟨a, hi, hh⟩, _, _⟩ := ha
    have hc := w1_handles_carries _ a o hh
    have hil := (List.getElem?_eq_some_iff.mp hi).1
    have hp' : (fgsa params unitCodec).processed
        (V2.D.Run.stateBefore weakEnv source (i + 1) u) o = false := by
      rw [w1_source_state (i + 1) hil]
      exact hp
    have hm := w1_prefix_relay 247 i v u a o t hi hc hp'
    refine ⟨t, le_rfl, ?_, w1_direct_handle strongEnv 247 _ u o t hm⟩
    change t < max t 0 + 1
    exact Int.lt_add_one_iff.mpr (le_max_left _ _)

/-- The continuation is the first 264 blocks of the unchanged weak generator. -/
theorem w1_continuation_eq : continuation = runData 263 (buildPrefix 264).2 :=
  congrArg (runData 263) (w1_suffix_eq 16).2

/-- Synchrony also holds throughout the continuation, including for sleeping nodes. -/
theorem w1_continuation_sync : V2.D.PartialSynchrony weakEnv continuation := by
  rw [w1_continuation_eq]
  exact w1_prefix_sync 263

/-- ROOT-DIGEST W3d. Replay without restarts preserves every stored body. -/
private theorem w1_fold_blocks (w : World) (es : List Event) (v : Validator)
    (hr : ∀ u t, V2.Event.restart u t ∈ es → False) (B : NamedProposal params.n)
    (hB : B ∈ (w v).st.namedBodies) : B ∈ (genFold w es v).st.namedBodies := by
  induction es generalizing w with
  | nil => exact hB
  | cons e es ih =>
    apply ih _ (fun u t hm => hr u t (List.mem_cons_of_mem _ hm))
    cases e with
    | restart u t => exact (hr u t (List.mem_cons_self ..)).elim
    | tick u t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        have he := congrArg State.namedBodies
          (i7_tick_st (w v) v t)
        change (V2.D.tick weakEnv (runData 263 []) (w v) v t).1.st.namedBodies = _ at he
        rw [he, clock_namedBodies]
        exact hB
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hB
    | deliver u o t =>
      by_cases hv : v = u
      · subst u
        simp only [V2.D.World.step, Function.update_self]
        exact process_namedBodies_subset _ _ hB
      · simpa only [V2.D.World.step, Function.update_of_ne hv] using hB

/-- ROOT-DIGEST W3d. Later generator boundaries keep each earlier body. -/
private theorem w1_prefix_blocks_mono (m n : Nat) (hmn : m ≤ n) (v : Validator)
    (B : NamedProposal params.n) (hB : B ∈ ((buildPrefix m).1 v).st.namedBodies) :
    B ∈ ((buildPrefix n).1 v).st.namedBodies := by
  obtain ⟨ds, he⟩ := w1_prefix_prefix m n hmn
  rw [(prefix_replay_fresh n).1, ← he, genFold_append, ← (prefix_replay_fresh m).1]
  apply w1_fold_blocks _ ds v _ B hB
  intro u t hm
  apply prefix_no_restart n u t
  rw [← he]
  exact List.mem_append_right _ hm

/-- ROOT-DIGEST W3d. The complete proposal batch stores the exact emitted body. -/
private theorem w1_prefix_body (n : Nat) (o : Obj params)
    (ho : o ∈ (tickBatch n (buildPrefix n).1).2) (B : NamedProposal params.n)
    (hp : o.payload = .proposal B) :
    B ∈ ((buildPrefix (n + 1)).1 0).st.namedBodies := by
  obtain ⟨u, hu⟩ := (w1_tickBatch_emits n (buildPrefix n).1 o).1 ho
  have hr : Reachable params ((buildPrefix n).1 u).st := by
    rw [(prefix_replay_fresh n).1]
    exact w1_reachable _ u
  obtain ⟨x, hx⟩ := w1_prefix_emits n o ho
  have hw := w1_emit_wire n _ (w1_prefix_schedule n) (prefix_origin (n + 1))
    (gen_prefix_carried (n + 1)).2 x o n (genEmits_runData n _ x o n hx)
  have hb := (w1_proposal_admit _ u n o hr hu hw B hp).2
    (w1_proposal_fresh_start n u o ho B hp)
  have hs := w1_proposal_singleton n (buildPrefix n).1 o ho B hp
  change B ∈ ((((tickBatch n (buildPrefix n).1).2.flatMap
    (fun a => nodes.map (fun v => (v, a)))).foldl (deliverOne n)
      ((tickBatch n (buildPrefix n).1).1, nodes.map (fun v => .tick v n))).1 0).st.namedBodies
  rw [hs, List.flatMap_singleton, w1_offer_st n _ o nodes (by decide),
    ite_eq_left (nodes_complete 0), w1_tickBatch_st, w1_prefix_uniform n 0 u]
  exact hb

/-- ROOT-DIGEST W3d. One finite final store covers both concrete runs. -/
private def w1_finalStore (steps : Nat) : State params.n := ((buildPrefix steps).1 0).st

private def w1_rootTable (steps : Nat) : List (NamedProposal params.n) :=
  (w1_finalStore steps).namedBodies

private theorem w1_tableInv (steps : Nat) : CStoreInv params (w1_finalStore steps) := by
  apply (storeBundle_of_reachable params _ _).cstore
  change Reachable params ((buildPrefix steps).1 0).st
  rw [(prefix_replay_fresh steps).1]
  exact w1_reachable _ 0

/-- ROOT-DIGEST W3d. The finite table contains every ancestor of each table body. -/
private theorem w1_tableMeta (steps : Nat) : MetaInv params (w1_finalStore steps) := by
  apply metadataInvariant
  change Reachable params ((buildPrefix steps).1 0).st
  rw [(prefix_replay_fresh steps).1]
  exact w1_reachable _ 0

private theorem w1_ancestorTable (steps : Nat) (B : NamedProposal params.n)
    (hB : B ∈ w1_rootTable steps) (A : NamedProposal params.n)
    (hA : NamedProposal.Preceq A B) : A ∈ w1_rootTable steps := by
  induction B with
  | genesis =>
    have he : A = .genesis := by
      simpa [NamedProposal.Preceq, NamedProposal.preceq] using hA
    exact he ▸ hB
  | node P slot root body raw sup rows ih =>
    rcases Bool.or_eq_true_iff.mp hA with he | hp
    · exact (of_decide_eq_true he) ▸ hB
    · exact ih (namedBodies_parent params _ (w1_tableMeta steps) hB) hp

/-- ROOT-DIGEST W3d. Each delivered proposal is a body in the final finite table. -/
private theorem w1_deliveredTable (steps : Nat) (v : Validator) (o : Obj params) (t : Time)
    (hd : V2.Event.deliver v o t ∈ (buildPrefix steps).2) (B : NamedProposal params.n)
    (hp : o.payload = .proposal B) : B ∈ w1_rootTable steps := by
  obtain ⟨u, hu⟩ := prefix_origin steps v o t hd
  obtain ⟨i, hi, ho⟩ := genEmits_runData 263 _ u o t hu
  rw [(V2.D.Run.step_tick_eq weakEnv _ hi).2] at ho
  obtain ⟨n, hn, rfl, hm⟩ := w1_locate_emission steps i u t o hi ho
  exact w1_prefix_blocks_mono (n + 1) steps hn 0 B (w1_prefix_body n o hm B hp)

/-- ROOT-DIGEST W3d. Every stored prefix body is in the final finite table. -/
private theorem w1_storedTable (steps : Nat) (h : Time) (i : Nat) (v : Validator)
    (B : NamedProposal params.n)
    (hB : B ∈ (V2.D.Run.stateBefore weakEnv (runData h (buildPrefix steps).2) i v).st.namedBodies) :
    B ∈ w1_rootTable steps := by
  rw [runData_stateBefore] at hB
  have hm := w1_fold_blocks (genFold V2.D.World.init ((buildPrefix steps).2.take i))
    ((buildPrefix steps).2.drop i) v
    (fun u t he => prefix_no_restart steps u t (List.mem_of_mem_drop he)) B hB
  rw [← genFold_append, List.take_append_drop, ← (prefix_replay_fresh steps).1] at hm
  rwa [w1_prefix_uniform steps v 0] at hm

/-- ROOT-DIGEST W3d. Local finite coverage gives the run's one root premise. -/
private theorem w1_tableRootPremise (steps : Nat) (E : Generic.Env Validator)
    (rho : V2.D.Run Validator (fgsa params unitCodec))
    (hd : ∀ v o t, V2.Event.deliver v o t ∈ rho.events → ∀ B,
      o.payload = .proposal B → B ∈ w1_rootTable steps)
    (hs : ∀ i v B, B ∈ (V2.D.Run.stateBefore E rho i v).st.namedBodies → B ∈ w1_rootTable steps) :
    NamedRootCollisionFree params unitCodec E rho where
  root_injective := by
    have scope (B : NamedProposal params.n) (hB : NamedProposalInRun params unitCodec E rho B) :
        B ∈ w1_rootTable steps := by
      obtain ⟨C, hC, hBC⟩ := hB
      apply w1_ancestorTable steps C _ B hBC
      rcases hC with ⟨v, o, t, he, hp⟩ | ⟨v, _, i, hm⟩
      · exact hd v o t he C hp
      · exact hs i v C hm
    intro B C hB hC A D hA hD he
    have ancestor (X : NamedProposal params.n)
      (hX : NamedProposal.Preceq X B ∨ NamedProposal.Preceq X C) :
        X ∈ w1_rootTable steps := hX.elim
      (w1_ancestorTable steps B (scope B hB) X) (w1_ancestorTable steps C (scope C hC) X)
    exact namedBodies_root_injective params _ (w1_tableInv steps) (w1_tableMeta steps)
      (ancestor A hA) (ancestor D hD) he

private theorem w1_continuation_deliveredTable (v : Validator) (o : Obj params) (t : Time)
    (hd : V2.Event.deliver v o t ∈ continuation.events) (B : NamedProposal params.n)
    (hp : o.payload = .proposal B) : B ∈ w1_rootTable 264 := by
  rw [w1_continuation_eq] at hd
  exact w1_deliveredTable 264 v o t hd B hp

private theorem w1_continuation_storedTable (i : Nat) (v : Validator) (B : NamedProposal params.n)
    (hB : B ∈ (V2.D.Run.stateBefore weakEnv continuation i v).st.namedBodies) :
    B ∈ w1_rootTable 264 := by
  rw [w1_continuation_eq] at hB
  exact w1_storedTable 264 263 i v B hB

private theorem w1_continuation_rootPremise :
    NamedRootCollisionFree params unitCodec weakEnv continuation :=
  w1_tableRootPremise 264 weakEnv continuation
    w1_continuation_deliveredTable w1_continuation_storedTable

/-- ROOT-DIGEST W3d. Source coverage follows from its literal continuation prefix. -/
private theorem w1_source_rootPremise :
    NamedRootCollisionFree params unitCodec strongEnv source := by
  apply w1_tableRootPremise 264 strongEnv source
  · intro v o t hd B hp
    exact w1_continuation_deliveredTable v o t (List.mem_append_left _ hd) B hp
  · intro i v B hB
    by_cases hi : i ≤ source.events.length
    · rw [← source_replay hi] at hB
      exact w1_continuation_storedTable i v B hB
    · have hl : source.events.length ≤ i := Nat.le_of_not_ge hi
      have he : V2.D.Run.stateBefore strongEnv source i =
          V2.D.Run.stateBefore strongEnv source source.events.length := by
        simp only [V2.D.Run.stateBefore, List.take_of_length_le hl, List.take_length]
      rw [he, ← source_replay le_rfl] at hB
      exact w1_continuation_storedTable source.events.length v B hB

/-- Stage 3: the full bounded strong-recovery source. -/
theorem w1_strongRecovery : StrongRecoverySearchPrefix₂ params unitCodec strongEnv source 4 1 where
  sync := by
    have h := (Gen.V2.Duty.partialSynchrony_iff_by_const strongEnv source).mp w1_source_sync
    have hd : (fgsaDelay (p := params) 1 1) = (fun _ => 1) := by
      funext o
      rw [fgsaDelay_def]
      cases o.payload <;> rfl
    exact hd.symm ▸ h
  deltaF := le_rfl
  liveness := ⟨by decide⟩
  gap := source_gap
  base := ⟨w1_source_execution, linked 247 _, cstar 247 _, no_restart.1, rfl,
    w1_source_rootPremise⟩
  fault := fault_bound.2
  awake := fun v _ t _ _ => strong_awake v t
  gapPos := gap_positive
  endpoint := endpoint

/-- Stage 3: the full clean-continuation pair after participation drops. -/
theorem w1_cleanContinuation :
    CleanContinuation₂ params unitCodec strongEnv source weakEnv continuation 1 where
  base := ⟨w1_continuation_execution, linked 263 _, cstar 263 _, no_restart.2, rfl,
    w1_continuation_rootPremise⟩
  agrees := agreement
  covered := le_of_lt covered
  sync := by
    have h := (Gen.V2.Duty.partialSynchrony_iff_by_const weakEnv continuation).mp
      w1_continuation_sync
    have hd : (fgsaDelay (p := params) 1 1) = (fun _ => 1) := by
      funext o
      rw [fgsaDelay_def]
      cases o.payload <;> rfl
    exact hd.symm ▸ h
  deltaF := le_rfl
  participation := fun t ht _ => witness_participation t ht

-- Axiom audit for every theorem added in W1.

end AvailableChain.FGSA.Run.Tests.WeakContinuationWitness
end
