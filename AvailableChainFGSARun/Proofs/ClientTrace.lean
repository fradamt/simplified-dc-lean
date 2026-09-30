module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainKitFG.ClientSafety

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open AvailableChain.V2.Engine
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem fg_seats (rho : V2.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (v : V) (r : Nat) : rho.ownSeats (.base (.fg r)) v = [e.symm v] :=
  ownSeats_bijSeat rho (ℓ := .base (.fg r)) e (he r) v

private theorem visible_head (s : Slot) (j : Fin p.n) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.base (.head s)) j, m⟩ = false := rfl

private theorem visible_prop (s : Slot) (j : Fin 1) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.prop s) j, m⟩ = false := rfl

private theorem visible_fg (r : Nat) (j : Fin p.n) (m : Msg p.n) :
    (fgsa p c).objSelfVisible ⟨.seat (.base (.fg r)) j, m⟩ = true := rfl

/-- The complete self-visible output: one FG row at an awake action tick. -/
theorem fgsa_tick_rows_of_seats (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (nd : Node p) (v : V) (t : Time) :
    ((V2.tick E rho nd v t).2.filter (fgsa p c).objSelfVisible) =
      if E.awake v t = true ∧ p.actionTime ((p.slotOf t - 1) / p.R) = t then
        [ofRow p ⟨.seat (.fg ((p.slotOf t - 1) / p.R)) (e.symm v),
          (attest p (FGSA.clock p nd.st t) nd.record ⟨0, p.nPos⟩).1⟩]
      else [] := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  have ht : (V2.tick E rho nd v t).2 =
    (if E.awake v t then
    (duties p t).flatMap (fun ℓ => (rho.ownSeats ℓ v).filterMap (fun j =>
      (act p c ⟨FGSA.clock p nd.st t, nd.record⟩ ℓ (rho.input v t)).map
        (fun m => (⟨.seat ℓ j, m⟩ : Obj p)))) ++ [] else []) := rfl
  rw [ht]
  dsimp only [duties]
  clear ht
  cases hprop : propose p (FGSA.clock p nd.st t) (p.slotOf t) <;>
  split_ifs <;>
    simp_all only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.nil_append, List.append_nil] <;>
    (try dsimp only [act, actS]) <;>
    simp_all only [Option.map_none, Option.map_some, List.filterMap_none,
      List.filter_append, fg_seats rho e he, List.filter_nil] <;>
    (try dsimp only [ofRow, ofWire, ofAuth]) <;>
    simp_all [List.filter_map, Function.comp_def, visible_head (p := p) (c := c),
      visible_prop (p := p) (c := c), visible_fg (p := p) (c := c)]

private theorem released_event (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (v : V) (k : Nat) :
    ownReleasedAt E rho v k =
      ((fgClientEvent p c E rho v k).toList.map (fun ev =>
        ofRow p ⟨.seat (.fg ev.2.2.1) (e.symm v),
          (attest p (FGSA.clock p (V2.Run.stateBefore E rho k v).st ev.2.1)
            (V2.Run.stateBefore E rho k v).record ⟨0, p.nPos⟩).1⟩)) := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  unfold ownReleasedAt fgClientEvent
  cases hk : rho.events[k]? with
  | none => rfl
  | some ev =>
    cases ev with
    | restart u t =>
      have hh : V2.Run.emitsAt E rho k = [] := by unfold V2.Run.emitsAt; rw [hk]
      simp only [hh, List.filter_nil, ite_self, Option.toList_none, List.map_nil]
    | deliver u o t =>
      have hh : V2.Run.emitsAt E rho k = [] := by unfold V2.Run.emitsAt; rw [hk]
      simp only [hh, List.filter_nil, ite_self, Option.toList_none, List.map_nil]
    | tick u t =>
      dsimp only [Option.map, V2.Event.node]
      by_cases huv : u = v
      · subst u
        have hh := (V2.Run.step_tick_eq E rho hk).2
        rw [ite_eq_left rfl, hh, fgsa_tick_rows_of_seats E rho e he]
        split_ifs <;> simp_all
      · simp only [Option.some.injEq, huv, false_and, ↓reduceIte, Option.toList_none, List.map_nil]

private theorem client_append (j : Fin p.n)
    (xs ys : List (Option (FGBlock (Fin p.n)) × HeadFields)) (Λ : Record) :
    clientRun p.E p.cfg j Λ (xs ++ ys) = clientRun p.E p.cfg j Λ xs ++
      clientRun p.E p.cfg j
        (xs.foldl (fun rec x => (createRow p.E p.cfg rec j x.1 x.2).2) Λ) ys := by
  induction xs generalizing Λ with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, clientRun, List.foldl_cons, ih]

private theorem record_succ (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (v : V) (k : Nat) :
    (V2.Run.stateBefore E rho (k + 1) v).record =
      (ownReleasedAt E rho v k).foldl (recordRow? p) (V2.Run.stateBefore E rho k v).record := by
  -- Unfold protocol projections in the dependent object and event types.
  set_option backward.isDefEq.respectTransparency false in
  rw [ownRecord_fold_run, ownReleased_succ E rho v (Nat.zero_le k), List.foldl_append,
    ← ownRecord_fold_run]

private theorem event_input (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (v : V)
    (k : Nat) (ev) (h : fgClientEvent p c E rho v k = some ev) :
    ev.2.2.2 = fgInputs p (FGSA.clock p (V2.Run.stateBefore E rho k v).st ev.2.1) := by
  unfold fgClientEvent at h
  cases hk : rho.events[k]? with
  | none => rw [hk] at h; cases h
  | some event =>
    rw [hk] at h
    cases event with
    | restart u t => cases h
    | deliver u o t => cases h
    | tick u t =>
      dsimp only at h
      split_ifs at h with hg
      · obtain ⟨rfl, _, _⟩ := hg
        cases h
        rfl

private theorem trace_and_record (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (v : V) (k : Nat) :
    (V2.Run.stateBefore E rho k v).record =
      ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)).foldl
        (fun rec x => (createRow p.E p.cfg rec (e.symm v) x.1 x.2).2) Record.initial ∧
    (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
      clientRun p.E p.cfg (e.symm v) Record.initial
        ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) := by
  -- Unfold the protocol state and object types when rewriting the two folds.
  set_option backward.isDefEq.respectTransparency false in
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hxs : (fgClientEvents p c E rho v (k + 1)).map (fun ev => ev.2.2.2) =
        (fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2) ++
          (fgClientEvent p c E rho v k).toList.map (fun ev => ev.2.2.2) := by
      unfold fgClientEvents
      rw [List.range_succ, List.filterMap_append, List.map_append]
      cases hx : fgClientEvent p c E rho v k with
      | none => rw [List.filterMap_cons_none hx]; rfl
      | some ev => rw [List.filterMap_cons_some hx]; rfl
    rw [record_succ, ownReleased_succ E rho v (Nat.zero_le k),
      List.filterMap_append, released_event E rho e he, hxs,
      List.foldl_append, client_append, ← ih.1, ih.2]
    cases hx : fgClientEvent p c E rho v k with
    | none => simp [clientRun]
    | some ev =>
      have hi := event_input E rho v k ev hx
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.foldl_cons,
        List.foldl_nil]
      rw [hi]
      exact ⟨rfl, rfl⟩

/-- For a fixed FG seat map, the decoded emitted rows are exactly the client
run on the actual awake action inputs, across restarts. -/
theorem fgsa_client_trace_of_seats (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (e : Fin p.n ≃ V) (he : ∀ r j, rho.seatOf (.base (.fg r)) j = e j)
    (v : V) (k : Nat) :
    (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
      clientRun p.E p.cfg (e.symm v) Record.initial
        ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) :=
  (trace_and_record E rho e he v k).2

omit [DecidableEq V] in
/-- Linked supplies one seat bijection for every FG round. -/
theorem fgsa_linked_seats (rho : V2.Run V (fgsa p c))
    (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    ∃ e : Fin p.n ≃ V, ∀ r j, rho.seatOf (.base (.fg r)) j = e j := by
  obtain ⟨N, e, hF⟩ := hL
  obtain ⟨hn, _⟩ := hF (.base (.fg 0)) trivial
  change p.n = N at hn
  subst N
  refine ⟨e, fun r j => ?_⟩
  obtain ⟨h, hr⟩ := hF (.base (.fg r)) trivial
  exact hr j

/-- A bijective seat map gives one owned seat for any duty label. -/
theorem fgsa_ownSeats_bijSeat (rho : V2.Run V (fgsa p c)) (ℓ : RunLabel)
    (e : Fin (RunLabel.seats p ℓ) ≃ V) (he : ∀ j, rho.seatOf ℓ j = e j) (v : V) :
    rho.ownSeats ℓ v = [e.symm v] :=
  ownSeats_bijSeat rho (ℓ := ℓ) e he v

/-- The run adapter and row decoder recover the actual seat's client row. -/
theorem fgsa_decode_attest_object (st : State p.n) (Λ : Record) (r : Nat) (j : Fin p.n) :
    decodeRowObject p (ofRow p ⟨.seat (.fg r) j, (attest p st Λ ⟨0, p.nPos⟩).1⟩) =
      some (createRow p.E p.cfg Λ j (fgInputs p st).1 (fgInputs p st).2).1 := rfl

/-- The trace under Linked uses one fixed seat and includes restarts. -/
theorem fgsa_client_trace (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    ∃ e : Fin p.n ≃ V, (∀ r j, rho.seatOf (.base (.fg r)) j = e j) ∧
      ∀ v k, (ownReleased E rho v 0 k).filterMap (decodeRowObject p) =
        clientRun p.E p.cfg (e.symm v) Record.initial
          ((fgClientEvents p c E rho v k).map (fun ev => ev.2.2.2)) := by
  obtain ⟨e, he⟩ := fgsa_linked_seats rho hL
  exact ⟨e, he, fgsa_client_trace_of_seats E rho e he⟩

private theorem emitted_mem (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (x : V) (a : RowWire p.n) (u : Row (Fin p.n)) (k n : Nat) (t : Time)
    (hk : rho.events[k]? = some (.tick x t)) (ha : ofRow p a ∈ V2.Run.emitsAt E rho k)
    (hn : k < n) (hd : RowWire.toRow? a = some u) :
    u ∈ (ownReleased E rho x 0 n).filterMap (decodeRowObject p) := by
  have hs : (fgsa p c).objSelfVisible (ofRow p a) = true := by
    obtain ⟨au, body⟩ := a
    rcases au with ⟨(_ | _), _⟩ | _ | _
    · cases hd
    · rfl
    · cases hd
    · cases hd
  have hd' : decodeRowObject p (ofRow p a) = some u := by
    have heq : decodeRowObject p (ofRow p a) = RowWire.toRow? a := by
      obtain ⟨au, body⟩ := a
      rcases au with ⟨(_ | _), _⟩ | _ | _ <;> rfl
    exact heq.trans hd
  apply List.mem_filterMap.mpr
  refine ⟨ofRow p a, ?_, hd'⟩
  apply List.mem_flatMap.mpr
  refine ⟨k, ?_, ?_⟩
  · simpa using hn
  · simp only [ownReleasedAt, hk, Option.map_some, V2.Event.node, ite_true]
    exact List.mem_filter.mpr ⟨ha, hs⟩

/-- Under Linked, every honest node's emitted rows contain no slashable pair.
No schedule, store invariant, or restart restriction is required. -/
theorem emittedRowsNoSlash (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hL : V2.Linked (fgsaFamilies p c).linked rho) :
    ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x := by
  obtain ⟨e, _, htrace⟩ := fgsa_client_trace E rho hL
  intro x _ a b ha hb u v hu hv
  obtain ⟨i, t, hi, ha⟩ := ha
  obtain ⟨j, t', hj, hb⟩ := hb
  have hm := emitted_mem E rho x a u i (max i j + 1) t hi ha (by omega) hu
  have hm' := emitted_mem E rho x b v j (max i j + 1) t' hj hb (by omega) hv
  rw [htrace] at hm hm'
  exact KitFG.clientRun_noSlash p.E p.cfg (e.symm x) _ u hm v hm'

end AvailableChain.FGSA.Run
end
