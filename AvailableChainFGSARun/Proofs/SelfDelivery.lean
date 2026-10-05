module
public import AvailableChainFGSARun.Proofs.Receipts
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainEngineV2.Laws.Duty.SelfDelivery

/-! Self-delivery of the own FG row (own-row analysis, Option 1; spec
`on_tick` ends with `attest`, and `on_attestation` is the delivery handler).

The FG action tick records the released row in Λ only; the row enters the
sender's store through a delivery event. This module shows that the
same-time self-delivery of an emitted row, appended after the last event of
the sender, is a valid continuation of a valid run (`EmitOk` for the row,
with freshness from send-once and unforgeable signatures), and that the
per-object delivery premises survive the append. The regime record
`Base₂` is handled in `AvailableChainFGSAProofs.Proofs.Shared.SelfDelivery`.
No statement, claim, manifest or fixture changes. -/

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-! ### Append laws of the duty engine (generic in the protocol) -/

section Snoc
variable {In' : Type} {P : V2.ProtocolSpecD In'} {E : Generic.Env V} {rho : V2.D.Run V P}
  {e : V2.Event V P.Object}

/-- [own-row Option 1; DC N3] The world step reads no event: an append keeps it. -/
theorem step_snoc :
    V2.D.World.step E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) =
      V2.D.World.step E rho := rfl

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] An index of the appended run is an old index or the new one. -/
theorem getElem?_snoc_cases {k : Nat} {f : V2.Event V P.Object}
    (hk : ({ rho with events := rho.events ++ [e] } : V2.D.Run V P).events[k]? = some f) :
    (k < rho.events.length ∧ rho.events[k]? = some f) ∨
      (k = rho.events.length ∧ f = e) := by
  by_cases hlt : k < rho.events.length
  · exact Or.inl ⟨hlt, by rw [← V2.D.Run.getElem?_snoc_of_lt hlt]; exact hk⟩
  · change (rho.events ++ [e])[k]? = some f at hk
    have hk' : k < (rho.events ++ [e]).length := (List.getElem?_eq_some_iff.mp hk).1
    have hkn : k = rho.events.length := by simp at hk'; omega
    subst hkn
    have hdn : (rho.events ++ [e])[rho.events.length]? = some e := by simp
    rw [hdn] at hk
    exact Or.inr ⟨rfl, (Option.some.inj hk).symm⟩

/-- [own-row Option 1; DC N3] Past the new event, the state is the final state. -/
theorem stateBefore_snoc_of_ge {k : Nat} (hk : rho.events.length + 1 ≤ k) :
    V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) k =
      V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
        (rho.events.length + 1) := by
  simp only [V2.D.Run.stateBefore]
  rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]

/-- [own-row Option 1; DC N3] The state after the new event is one step from the old final
state. -/
theorem stateBefore_snoc_last :
    V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      (rho.events.length + 1) =
      V2.D.World.step E rho (V2.D.Run.stateBefore E rho rho.events.length) e := by
  have hdn : ({ rho with events := rho.events ++ [e] } : V2.D.Run V P).events[rho.events.length]? =
      some e := by simp
  rw [V2.D.Run.stateBefore_succ E _ hdn, V2.D.Run.stateBefore_snoc_of_le le_rfl]
  rfl

/-- [own-row Option 1; DC N3] The time-indexed state after an append: one more step when the
new event is before the time. -/
theorem stateBeforeTime_snoc (T : Time) :
    V2.D.Run.stateBeforeTime E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) T =
      if e.time < T then V2.D.World.step E rho (V2.D.Run.stateBeforeTime E rho T) e
      else V2.D.Run.stateBeforeTime E rho T := by
  change ((rho.events ++ [e]).filter (fun f => decide (f.time < T))).foldl
    (V2.D.World.step E rho) V2.D.World.init = _
  rw [List.filter_append, List.foldl_append]
  by_cases h : e.time < T
  · simp [h]
    rfl
  · simp [h]
    rfl

/-- [own-row Option 1; DC N3] A delivery append adds no emission. -/
theorem emits_snoc_deliver_iff {v u : V} {o₀ o : P.Object} {t₀ t : Time} :
    V2.D.Run.emits E ({ rho with events := rho.events ++ [.deliver v o₀ t₀] } : V2.D.Run V P)
      u o t ↔ V2.D.Run.emits E rho u o t := by
  constructor
  · rintro ⟨k, hk, ho⟩
    rcases getElem?_snoc_cases hk with ⟨hlt, hk'⟩ | ⟨-, h⟩
    · exact ⟨k, hk', by rw [V2.D.Run.emitsAt_snoc_of_lt hlt] at ho; exact ho⟩
    · cases h
  · exact V2.D.Run.emits_snoc

/-- [own-row Option 1; DC N3] Old handler calls survive an append. -/
theorem handlesAt_snoc_of_lt {k : Nat} (hk : k < rho.events.length) {w : V} {o : P.Object}
    {t : Time} (h : V2.D.Run.handlesAt E rho k w o t) :
    V2.D.Run.handlesAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) k w o t := by
  obtain ⟨o', hk', hh⟩ := h
  exact ⟨o', by rw [V2.D.Run.getElem?_snoc_of_lt hk]; exact hk',
    by rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hk)]; exact hh⟩

/-- [own-row Option 1; DC N3] A handler call index of the old run is below its length. -/
theorem handlesAt_lt_length {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.handlesAt E rho k w o t) : k < rho.events.length := by
  obtain ⟨_, hk, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp hk).1

/-- [own-row Option 1; DC N3] A handler call of the appended run is an old call or a call of
the new event. -/
theorem handlesAt_snoc_cases {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.handlesAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      k w o t) :
    (k < rho.events.length ∧ V2.D.Run.handlesAt E rho k w o t) ∨
      (k = rho.events.length ∧ ∃ o', e = .deliver w o' t ∧
        P.handles (V2.D.Run.stateBefore E rho rho.events.length w) o' o) := by
  obtain ⟨o', hk, hh⟩ := h
  rcases getElem?_snoc_cases hk with ⟨hlt, hk'⟩ | ⟨rfl, he⟩
  · exact Or.inl ⟨hlt, o', hk',
      by rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)] at hh; exact hh⟩
  · exact Or.inr ⟨rfl, o', he.symm,
      by rw [V2.D.Run.stateBefore_snoc_of_le le_rfl] at hh; exact hh⟩

/-- [own-row Option 1; DC N3] An acceptance of the appended run is an old acceptance or a
call of the new event. -/
theorem acceptsAt_snoc_cases {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.acceptsAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      k w o t) :
    (k < rho.events.length ∧ V2.D.Run.acceptsAt E rho k w o t) ∨
      (k = rho.events.length ∧ ∃ o', e = .deliver w o' t ∧
        P.handles (V2.D.Run.stateBefore E rho rho.events.length w) o' o) := by
  obtain ⟨hh, hb, ha⟩ := h
  rcases handlesAt_snoc_cases hh with ⟨hlt, hh'⟩ | hnew
  · refine Or.inl ⟨hlt, hh', ?_, ?_⟩
    · rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)] at hb; exact hb
    · rw [V2.D.Run.stateBefore_snoc_of_le hlt] at ha; exact ha
  · exact Or.inr hnew

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] A delivery append keeps `NoRestart`. -/
theorem noRestart_snoc_deliver {v : V} {o : P.Object} {t : Time} (h : V2.D.NoRestart rho) :
    V2.D.NoRestart ({ rho with events := rho.events ++ [.deliver v o t] } : V2.D.Run V P) := by
  intro k u s hk
  rcases getElem?_snoc_cases hk with ⟨-, hk'⟩ | ⟨-, hk'⟩
  · exact h k u s hk'
  · cases hk'

end Snoc

/-! ### FG-SA facts about the own row -/

variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [own-row Option 1; DC N4] A store wire with a row payload keeps the proposals: the
handler is `admitRow` or the identity. -/
theorem process_row_proposals (st : State p.n) (a : Auth Label p.n) (body : RowPayload) :
    (FGSA.process p st ⟨a, .row body⟩).proposals = st.proposals := by
  unfold FGSA.process
  cases hd : Wire.decode (⟨a, .row body⟩ : Wire p.n) with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => cases decode_eq_vote.mp hd
    | block s N => cases decode_eq_block.mp hd
    | row i body' =>
      change (admitRow p st ⟨a, body'⟩).proposals = st.proposals
      rcases admitRow_eq p st ⟨a, body'⟩ with h | h <;> rw [h]

/-- [own-row Option 1; DC N4] An FG row delivery adds no named body. -/
theorem process_ofRow_namedBodies (st : State p.n) (a : RowWire p.n) :
    (FGSA.process p st (toWire p (ofRow p a))).namedBodies = st.namedBodies := by
  rw [toWire_ofRow]
  simp only [State.namedBodies, process_row_proposals]

/-- [own-row Option 1; DC NamedRootCollisionFree] The named scope of a run with an appended
row delivery is the named scope of the run. -/
theorem namedProposalInRun_snoc_row {v : V} {a : RowWire p.n} {t : Time}
    {A : NamedProposal p.n}
    (h : NamedProposalInRun p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p a) t] }) A) :
    NamedProposalInRun p c E rho A := by
  obtain ⟨B, hB, hAB⟩ := h
  refine ⟨B, ?_, hAB⟩
  rcases hB with ⟨x, o, s, hmem, hpay⟩ | ⟨x, hx, k, hk⟩
  · rcases List.mem_append.mp hmem with hmem | hmem
    · exact Or.inl ⟨x, o, s, hmem, hpay⟩
    · obtain ⟨-, rfl, -⟩ := V2.Event.deliver.inj (List.mem_singleton.mp hmem)
      change Msg.row a.payload = Msg.proposal B at hpay
      cases hpay
  · refine Or.inr ⟨x, hx, ?_⟩
    by_cases hk' : k ≤ rho.events.length
    · exact ⟨k, by rw [V2.D.Run.stateBefore_snoc_of_le hk'] at hk; exact hk⟩
    · refine ⟨rho.events.length, ?_⟩
      rw [stateBefore_snoc_of_ge (by omega), stateBefore_snoc_last] at hk
      simp only [V2.D.World.step] at hk
      by_cases hxv : x = v
      · subst hxv
        rw [Function.update_self] at hk
        change B ∈ (FGSA.process p (V2.D.Run.stateBefore E rho rho.events.length x).st
          (toWire p (ofRow p a))).namedBodies at hk
        rw [process_ofRow_namedBodies] at hk
        exact hk
      · rw [Function.update_of_ne hxv] at hk
        exact hk

/-- [own-row Option 1; DC NamedRootCollisionFree] `NamedRootCollisionFree` survives an
appended row delivery: the scope does not grow. -/
theorem namedRootCollisionFree_snoc_row {v : V} {a : RowWire p.n} {t : Time}
    (h : NamedRootCollisionFree p c E rho) :
    NamedRootCollisionFree p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p a) t] }) where
  root_injective B C hB hC :=
    h.root_injective B C (namedProposalInRun_snoc_row hB) (namedProposalInRun_snoc_row hC)

/-- [own-row Option 1; DC N4] A delivery append keeps every exclusion of the time-indexed
state (`excludesS_process`). -/
theorem excludes_stateBeforeTime_snoc {v w : V} {o₀ o : Obj p} {t₀ T : Time}
    (h : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o = true) :
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E
      ({ rho with events := rho.events ++ [.deliver v o₀ t₀] }) T w) o = true := by
  rw [stateBeforeTime_snoc]
  split
  · simp only [V2.D.World.step]
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact excludesS_process _ _ _ h
    · rw [Function.update_of_ne hw]
      exact h
  · exact h

/-- [own-row Option 1; DC N4] The contrapositive: an object not excluded after the append
was not excluded before. -/
theorem excludes_stateBeforeTime_snoc_false {v w : V} {o₀ o : Obj p} {t₀ T : Time}
    (h : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E
      ({ rho with events := rho.events ++ [.deliver v o₀ t₀] }) T w) o = false) :
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o = false := by
  cases hb : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o with
  | false => rfl
  | true => rw [excludes_stateBeforeTime_snoc (v := v) (o₀ := o₀) (t₀ := t₀) hb] at h; cases h

/-- [own-row Option 1; spec `attest`, `on_attestation`; DC N4] The own row is fresh: a row
released by the FG action tick of `v` at index `i` is not in the row pool of `v` before
that tick. A pool row has an earlier handler call (`rowPool_provenance`); under
`UnforgeableSignatures` its honest holder `v` emitted it at or before that delivery; the
fixed FG seat emits each content once (`fgsa_emitOnceUnder`), so that emission is the tick
at `i`; the schedule order then puts the delivery before the emission time. -/
theorem fgsa_emitted_row_fresh (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V}
    {t : Time} (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    (⟨.seat .fg j, body⟩ : RowWire p.n) ∉ (V2.D.Run.stateBefore E rho i v).st.rowPool := by
  intro hm
  obtain ⟨-, hseat, -⟩ := (fgsa_emitsAt_row E rho i v t hi j body).mp ho
  have hv : v ∈ rho.honest := hvalid.honest_only _ (List.mem_of_getElem? hi)
  have hilen : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨k, tk, hki, ⟨o', hk, hhand⟩, -⟩ := rowPool_provenance E rho i v _ hm
  have hhold : V2.D.Run.holder rho (ofRow p ⟨.seat .fg j, body⟩).auth = some v := by
    rw [ofRow_auth]
    exact congrArg some hseat
  have hproc : V2.D.Run.processes rho v o' tk := ⟨k, hk⟩
  have hem : ∃ t', t' ≤ tk ∧ V2.D.Run.emits E rho v (ofRow p ⟨.seat .fg j, body⟩) t' := by
    rcases (fgsaHooks p c).handles_carries _ _ _ hhand with heq | hc
    · rw [← heq]
      exact hvalid.unforgeable v o' tk hproc v hv (by rw [heq]; exact hhold)
    · exact hvalid.carried v o' tk hproc _ hc v hv hhold
  obtain ⟨t', ht', i', hi', ho'⟩ := hem
  have hii : i' = i :=
    fgsa_emitOnceUnder E rho hvalid j (by rw [hseat]; exact hv) (.row body) i' i t' t
      (by rw [hseat]; exact hi') (by rw [hseat]; exact hi) ho' ho
  subst hii
  rw [hi] at hi'
  obtain ⟨-, rfl⟩ := V2.Event.tick.inj (Option.some.inj hi')
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
  have hs := List.pairwise_iff_getElem.mp hvalid.sorted k i' hkl hilen hki
  rw [hkv, (List.getElem?_eq_some_iff.mp hi).2] at hs
  unfold V2.Event.key at hs
  rcases Prod.Lex.toLex_le_toLex.mp hs with hlt | ⟨-, hph⟩
  · change tk < t at hlt
    exact (lt_irrefl _ (lt_of_le_of_lt ht' hlt)).elim
  · change (2 : Nat) ≤ 1 at hph
    omega

/-- [own-row Option 1; DC N4] `EmitOk` for a released FG row: the wire check from
`honest_emit_wellFormed`, no dependencies (`depsS`), freshness from
`fgsa_emitted_row_fresh`, and a row carries nothing (`carriesS`). -/
theorem fgsa_emitOk_row (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.EmitOk E rho (V2.D.Run.stateBefore E rho i v) v t (ofRow p ⟨.seat .fg j, body⟩) := by
  obtain ⟨hawake, -, -⟩ := (fgsa_emitsAt_row E rho i v t hi j body).mp ho
  have hv : v ∈ rho.honest := hvalid.honest_only _ (List.mem_of_getElem? hi)
  have hd : (toWire p (ofRow p ⟨.seat .fg j, body⟩)).decode = some (.row j body) := by
    rw [toWire_ofRow]
    exact decode_eq_row.mpr rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact honest_emit_wellFormed E rho hvalid.toDeliveryWellFormed hvalid.toScheduleWellFormed
      i v t hi hv hawake _ ho
  · change depsS p (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).1.st
      (ofRow p ⟨.seat .fg j, body⟩) = true
    unfold depsS
    rw [hd]
  · change processedS p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t)
      (ofRow p ⟨.seat .fg j, body⟩) = false
    unfold processedS
    rw [hd, clock_rowPool]
    exact decide_eq_false (fgsa_emitted_row_fresh hvalid hi ho)
  · intro o' h
    exact h

/-- [own-row Option 1; DC N4] Every object released at an FG seat is a row with `EmitOk`. -/
theorem fgsa_emitOk_fg (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {m : Msg p.n}
    (ho : (⟨.seat (.base .fg) j, m⟩ : Obj p) ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.EmitOk E rho (V2.D.Run.stateBefore E rho i v) v t ⟨.seat (.base .fg) j, m⟩ := by
  have ho' := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at ho'
  obtain ⟨body, rfl⟩ := fgsa_tick_fg_row E rho _ v t j m ho'
  exact fgsa_emitOk_row hvalid hi ho

/-- [own-row Option 1; DC N3] The same-time self-delivery of a released FG row, appended
after the last event of the sender, keeps `ExecutionValid`. -/
theorem executionValid_snoc_selfDelivery (hvalid : V2.D.ExecutionValid E rho) {i : Nat}
    {v : V} {t : Time} (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.ExecutionValid E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t] }) :=
  hvalid.snoc_selfDelivery (fgsaHooks p c) hkey hi hlast ho (fgsa_emitOk_row hvalid hi ho)

/-! ### Delivery regimes survive the append -/

/-- [own-row Option 1; DC Generic/Conditions.lean:110] `PartialSynchronyBy` survives the
same-time self-delivery of a released object that carries nothing. Old obligations keep
their witnesses; the obligations of the new acceptance are the broadcast obligations of the
emission, with the same deadline. -/
theorem partialSynchronyBy_snoc_selfDelivery {delayOf : Obj p → Time}
    (h : Gen.V2.Duty.PartialSynchronyBy E rho delayOf) {i : Nat} {v : V} {t : Time} {o : Obj p}
    (hi : rho.events[i]? = some (.tick v t)) (ho : o ∈ V2.D.Run.emitsAt E rho i)
    (hnc : ∀ o', (fgsa p c).carries o o' → False) :
    Gen.V2.Duty.PartialSynchronyBy E
      ({ rho with events := rho.events ++ [.deliver v o t] }) delayOf where
  broadcast_emitted u hu o' t' he w hw hdl hx := by
    obtain ⟨t'', ht1, ht2, j, hj⟩ := h.broadcast_emitted u hu o' t' (emits_snoc_deliver_iff.mp he)
      w hw hdl (excludes_stateBeforeTime_snoc_false hx)
    exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
  relay_accepted u hu k o' t' hacc w hw hp hdl hx := by
    rcases acceptsAt_snoc_cases hacc with ⟨hlt, hacc'⟩ | ⟨rfl, o'', heq, hh⟩
    · have hp' : (fgsa p c).processed (V2.D.Run.stateBefore E rho (k + 1) w) o' = false := by
        rw [V2.D.Run.stateBefore_snoc_of_le hlt] at hp; exact hp
      obtain ⟨t'', ht1, ht2, j, hj⟩ := h.relay_accepted u hu k o' t' hacc' w hw hp' hdl
        (excludes_stateBeforeTime_snoc_false hx)
      exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
    · obtain ⟨rfl, rfl, rfl⟩ := V2.Event.deliver.inj heq
      rcases (fgsaHooks p c).handles_carries _ _ _ hh with rfl | hc
      · obtain ⟨t'', ht1, ht2, j, hj⟩ := h.broadcast_emitted v hu o t ⟨i, hi, ho⟩ w hw hdl
          (excludes_stateBeforeTime_snoc_false hx)
        exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
      · exact (hnc _ hc).elim

/-- [own-row Option 1; DC Generic/Conditions.lean:134] `HealthyPrefixDeliveryBy` survives
the same-time self-delivery of a released object that carries nothing. -/
theorem healthyPrefixDeliveryBy_snoc_selfDelivery {delayOf : Obj p → Time} {cut : Time}
    (h : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho delayOf cut) {i : Nat} {v : V} {t : Time}
    {o : Obj p} (hi : rho.events[i]? = some (.tick v t)) (ho : o ∈ V2.D.Run.emitsAt E rho i)
    (hnc : ∀ o', (fgsa p c).carries o o' → False) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E
      ({ rho with events := rho.events ++ [.deliver v o t] }) delayOf cut where
  broadcast_emitted u hu o' t' he w hw hdl hx := by
    obtain ⟨t'', ht1, ht2, j, hj⟩ := h.broadcast_emitted u hu o' t' (emits_snoc_deliver_iff.mp he)
      w hw hdl (excludes_stateBeforeTime_snoc_false hx)
    exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
  relay_accepted u hu k o' t' hacc w hw hp hdl hx := by
    rcases acceptsAt_snoc_cases hacc with ⟨hlt, hacc'⟩ | ⟨rfl, o'', heq, hh⟩
    · have hp' : (fgsa p c).processed (V2.D.Run.stateBefore E rho (k + 1) w) o' = false := by
        rw [V2.D.Run.stateBefore_snoc_of_le hlt] at hp; exact hp
      obtain ⟨t'', ht1, ht2, j, hj⟩ := h.relay_accepted u hu k o' t' hacc' w hw hp' hdl
        (excludes_stateBeforeTime_snoc_false hx)
      exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
    · obtain ⟨rfl, rfl, rfl⟩ := V2.Event.deliver.inj heq
      rcases (fgsaHooks p c).handles_carries _ _ _ hh with rfl | hc
      · obtain ⟨t'', ht1, ht2, j, hj⟩ := h.broadcast_emitted v hu o t ⟨i, hi, ho⟩ w hw hdl
          (excludes_stateBeforeTime_snoc_false hx)
        exact ⟨t'', ht1, ht2, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩
      · exact (hnc _ hc).elim

/-- [own-row Option 1; DC N4] A released FG row carries nothing. -/
theorem fgsa_row_noCarried (a : RowWire p.n) (o' : Obj p)
    (h : (fgsa p c).carries (ofRow p a) o') : False := h

end AvailableChain.FGSA.Run
end
