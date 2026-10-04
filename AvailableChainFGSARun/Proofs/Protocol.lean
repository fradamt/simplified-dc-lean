module
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSARun.Model.Families
public import AvailableChainKitFG.ClientOnceSafety
public import AvailableChainGeneric.Proofs.V2.Duty.Signatures

public section

/-! Basic facts of the FG-SA protocol on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2): the restore, clock,
process and own-record steps on the two parts of the node state; the FG action
and its record; the application value of the proposal; the adapter. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}

/-! ### The two parts of the node state -/

/-- [plan §1a restart decision] A restart restarts the store from `initial`. -/
theorem restore_st (d : RecordOnce) : ((fgsa p c).restore d).st = initial p.n := rfl

/-- [plan §1a restart decision] A restart keeps Λ. -/
theorem restore_rec (d : RecordOnce) : ((fgsa p c).restore d).record = d := rfl

/-- The clock step keeps Λ. -/
theorem clock_rec (nd : Node p) (t : Time) : ((fgsa p c).clock nd t).record = nd.record := rfl

/-- The delivery step keeps Λ. -/
theorem process_rec (nd : Node p) (o : Obj p) :
    ((fgsa p c).process nd o).record = nd.record := rfl

/-- The own-record step keeps the store. -/
theorem recordOwn_st (nd : Node p) (o : Obj p) :
    ((fgsa p c).recordOwn nd o).st = nd.st := rfl

/-- The own-record step is `recordRow?` on Λ. -/
theorem recordOwn_rec (nd : Node p) (o : Obj p) :
    ((fgsa p c).recordOwn nd o).record = recordRow? p nd.record o := rfl

/-! ### The FG action -/

/-- [spec 1304–1313; plan T7.2] The row body and the new record of `attest` do
not depend on the identity: `createRowOnce` uses the signer only in `Row.signer`,
`record_row_once` does not read it, and `RowBody.ofRow` drops it. -/
theorem attest_signer_irrel (st : State p.n) (Λ : RecordOnce) (i j : Fin p.n) :
    attest p st Λ i = attest p st Λ j := by
  have h := KitFG.createRowOnce_signer_irrel p.E p.cfg Λ i j
    (fgInputs p st).1 (fgInputs p st).2
  apply Prod.ext
  · have he := congrArg (Option.map (fun k => RowPayload.vote ⟨k.1, k.2⟩)) h.1
    dsimp only [attest, RowBody.ofRow, Row.onceKey] at he ⊢
    simp only [Option.map_map, Function.comp_def] at he
    exact he
  · exact h.2

/-- An FG duty releases zero or one row. -/
theorem act_fg (nd : Node p) (r : Nat) (x : In) :
    (fgsa p c).act nd (.fgAction r) x =
      (attest p nd.st nd.record ⟨0, p.nPos⟩).1.map Msg.row := rfl

/-- A successful client action writes its complete released content. -/
theorem attest_some_record (st : State p.n) (Λ : RecordOnce) (i : Fin p.n)
    (payload : RowPayload) (h : (attest p st Λ i).1 = some payload) :
    (attest p st Λ i).2 = record_row_once Λ (payload.toRow i) := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_, _, _, _, _, _, _, hr⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ i (fgInputs p st).1 (fgInputs p st).2 ha
  change (createRowOnce p.E p.cfg Λ i (fgInputs p st).1 (fgInputs p st).2).2 = _
  rw [hr, ← hp]
  rfl

/-- A successful client action has not sent this content before. -/
theorem attest_some_fresh (st : State p.n) (Λ : RecordOnce) (i : Fin p.n)
    (payload : RowPayload) (h : (attest p st Λ i).1 = some payload) :
    (payload.height_pair, payload.finality_pair) ∉ Λ.sent := by
  obtain ⟨a, ha, hp⟩ := Option.map_eq_some_iff.mp h
  have hf := (KitFG.createRowOnce_sent p.E p.cfg Λ i
    (fgInputs p st).1 (fgInputs p st).2).2 a ha
  rw [← hp]
  exact hf.1

/-- A suppressed client action does not write the record. -/
theorem attest_none_record (st : State p.n) (Λ : RecordOnce) (i : Fin p.n)
    (h : (attest p st Λ i).1 = none) : (attest p st Λ i).2 = Λ := by
  exact KitFG.createRowOnce_none p.E p.cfg Λ i (fgInputs p st).1 (fgInputs p st).2
    (Option.map_eq_none_iff.mp h)

/-- The engine records a successful attest result before release. -/
theorem recordOwn_attest (nd : Node p) (i : Fin p.n) (payload : RowPayload)
    (h : (attest p nd.st nd.record ⟨0, p.nPos⟩).1 = some payload) :
    ((fgsa p c).recordOwn nd ⟨.seat (.base .fg) i, .row payload⟩).record =
      (attest p nd.st nd.record ⟨0, p.nPos⟩).2 := by
  rw [attest_some_record _ _ _ _ h]
  rfl

/-- At one time, distinct due duties have distinct signing labels. -/
theorem fgsa_dutiesInjectiveAt (t : Time) : V2.D.DutiesInjectiveAt (fgsa p c) t := by
  have fg_eq (r : Nat) (hr : RunDuty.fgAction r ∈ duties p t) :
      r = (p.slotOf t - 1) / p.R := by
    simp only [duties] at hr
    split_ifs at hr <;> simp_all
  intro d d' ht ht' hs
  change RunDuty.signLabel d = RunDuty.signLabel d' at hs
  have hd := (duties_spec p d t).mpr ht
  have hd' := (duties_spec p d' t).mpr ht'
  have hfg : ∀ r q, RunDuty.fgAction r ∈ duties p t →
      RunDuty.fgAction q ∈ duties p t → r = q :=
    fun r q hr hq => (fg_eq r hr).trans (fg_eq q hq).symm
  cases d <;> cases d' <;> dsimp only [RunDuty.signLabel] at hs <;> simp_all
  all_goals first | rfl | exact congrArg RunDuty.fgAction (hfg _ _ hd hd')

/-- A HEAD label has exactly its scheduled HEAD duty. -/
theorem fgsa_head_singleDuty (s : Slot) :
    Gen.V2.Duty.SingleDuty (fgsa p c) (.base (.head s)) := by
  refine ⟨.headAction s, rfl, ?_⟩
  intro d hd
  change RunDuty.signLabel d = _ at hd
  cases d <;> dsimp only [RunDuty.signLabel] at hd <;> simp_all
  all_goals rfl

/-- A proposal label has exactly its scheduled proposal duty. -/
theorem fgsa_prop_singleDuty (s : Slot) :
    Gen.V2.Duty.SingleDuty (fgsa p c) (.prop s) := by
  refine ⟨.propAction s, rfl, ?_⟩
  intro d hd
  change RunDuty.signLabel d = _ at hd
  cases d <;> dsimp only [RunDuty.signLabel] at hd <;> simp_all
  all_goals rfl

/-! ### The proposal -/

/-- [plan T7.2] The payload of a proposal label is the store proposal with the
application value of the input. -/
theorem act_prop (nd : Node p) (s : Slot) (x : In) :
    (fgsa p c).act nd (.propAction s) x = (propose p nd.st s).map (withApp p (c.app x)) := rfl

/-- [plan T7.2] There is no proposal at slot `0`. -/
theorem act_prop_zero (nd : Node p) (x : In) : (fgsa p c).act nd (.propAction 0) x = none := rfl

/-- ROOT-DIGEST W2. A zero-app update preserves the proposal digest and payload.
Thus unitCodec preserves the local proposal output. -/
theorem withApp_zero (st : State p.n) (s : Slot) :
    (propose p st s).map (withApp p 0) = propose p st s := by
  unfold propose
  split <;> rfl

/-- [ROOT-DIGEST W2; plan T7.2; I9 D9; Opus M2] The proposal with application value `a` is a
proposal whose block is a node of slot `s` with the packed body of `a` and its
carried rows. The block passes the BODY check `rowsOk` with these rows,
and its application value is `a`. -/
theorem rowsOk_withApp (st : State p.n) (s : Slot) (a : Nat) {m : Msg p.n}
    (h : (propose p st s).map (withApp p a) = some m) :
    ∃ H raw sup rows, m = .proposal (proposalBlock p H s a raw sup rows) raw sup rows ∧
      rowsOk (proposalBlock p H s a raw sup rows) rows = true ∧
      appOf (proposalBlock p H s a raw sup rows).body = a := by
  unfold propose at h
  split at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨_, _, _, _, rfl, ?_, appOf_packBody _ _⟩
    exact contentOk_rowsOk (contentOk_proposalBlock p _ s a _ _ _)

/-! ### Label families and isolation -/

/-- [plan T7.2; 2a Task 3 Step 5] A proposal label has one seat. -/
theorem singleSeat_prop : V2.D.SingleSeat (fgsa p c) (fun ℓ => ∃ s, ℓ = .prop s) := by
  rintro _ ⟨s, rfl⟩
  rfl

/-- [plan T7.2; FRAMEWORK dated E5 note :302–306] The linked family (the FG
labels) is self-visible. -/
theorem linked_selfVisible (ℓ : RunLabel) (h : (fgsaFamilies p c).linked ℓ) :
    (fgsa p c).selfVisible ℓ = true := by
  rcases ℓ with (_ | _) | _
  · exact h.elim
  · rfl
  · exact h.elim

/-- [plan T7.2; 2a `Isolation.base_tick`] The store after a tick is the store
clock of the store before it: the released objects and the own record do not
change the store. -/
theorem tick_st {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) :
    (V2.D.tick E rho nd v t).1.st = FGSA.clock p nd.st t :=
  (fgsaIso p c).base_tick E rho nd v t

/-! ### The adapter -/

@[simp] theorem ofWire_toWire (o : Obj p) : ofWire p (toWire p o) = o :=
  (toWireEquiv p).left_inv o

@[simp] theorem toWire_ofWire (w : Wire p.n) : toWire p (ofWire p w) = w :=
  (toWireEquiv p).right_inv w

theorem toWire_injective : Function.Injective (toWire p) := (toWireEquiv p).injective

/-- A carried HEAD reaches the store as its HEAD wire. -/
@[simp] theorem toWire_ofHead (h : HeadWire p.n) :
    toWire p (ofHead p h) = ⟨h.auth, .head h.payload⟩ := toWire_ofWire _

/-- A carried row reaches the store as its row wire. -/
@[simp] theorem toWire_ofRow (a : RowWire p.n) :
    toWire p (ofRow p a) = ⟨a.auth, .row a.payload⟩ := toWire_ofWire _

/-- [A0 M8] Two carried rows give the same v2 object only if they are equal. -/
theorem ofRow_injective : Function.Injective (ofRow p) := by
  intro a a' h
  have h' := congrArg (toWire p) h
  rw [toWire_ofRow, toWire_ofRow] at h'
  obtain ⟨x, y⟩ := a
  obtain ⟨x', y'⟩ := a'
  simp only [Signed.mk.injEq, Msg.row.injEq] at h'
  obtain ⟨rfl, rfl⟩ := h'
  rfl

/-- [A0 M8] Two carried HEADs give the same v2 object only if they are equal. -/
theorem ofHead_injective : Function.Injective (ofHead p) := by
  intro h h' e
  have e' := congrArg (toWire p) e
  rw [toWire_ofHead, toWire_ofHead] at e'
  obtain ⟨x, y⟩ := h
  obtain ⟨x', y'⟩ := h'
  simp only [Signed.mk.injEq, Msg.head.injEq] at e'
  obtain ⟨rfl, rfl⟩ := e'
  rfl

/-- [A0 M8] The v2 authentication of a carried row. -/
theorem ofRow_auth (a : RowWire p.n) : (ofRow p a).auth = ofAuth p a.auth := rfl

/-! ### The decoder -/

/-- The store decoder gives a vote only for a HEAD-seat HEAD wire. -/
theorem decode_eq_vote {n : Nat} {w : Wire n} {s : Slot} {i : Fin n} {b : Block} :
    w.decode = some (.vote s i b) ↔ w = ⟨.seat (.head s) i, .head b⟩ := by
  obtain ⟨a, m⟩ := w
  constructor
  · intro h
    rcases a with ⟨(_ | _), _⟩ | _ | _ <;> cases m <;> simp_all [Wire.decode]
  · rintro ⟨⟩; rfl

/-- The store decoder gives a row only for an FG-seat row wire. -/
theorem decode_eq_row {n : Nat} {w : Wire n} {i : Fin n} {body : RowPayload} :
    w.decode = some (.row i body) ↔ w = ⟨.seat .fg i, .row body⟩ := by
  obtain ⟨a, m⟩ := w
  constructor
  · intro h
    rcases a with ⟨(_ | _), _⟩ | _ | _ <;> cases m <;> simp_all [Wire.decode]
  · rintro ⟨⟩; rfl

/-- The store decoder gives a block only for a proposer-key proposal wire. -/
theorem decode_eq_block {n : Nat} {w : Wire n} {s : Slot} {b : Block}
    {raw sup : List (HeadWire n)} {rows : List (RowWire n)} :
    w.decode = some (.block s b raw sup rows) ↔ w = ⟨.proposer s, .proposal b raw sup rows⟩ := by
  obtain ⟨a, m⟩ := w
  constructor
  · intro h
    rcases a with ⟨(_ | _), _⟩ | _ | _ <;> cases m <;> simp_all [Wire.decode]
  · rintro ⟨⟩; rfl

/-- A row wire decodes as a row exactly when its auth is an FG seat. -/
theorem rowWire_decode {n : Nat} {a : RowWire n} {i : Fin n} {body : RowPayload} :
    a.decode? = some (i, body) ↔ a = ⟨.seat .fg i, body⟩ := by
  obtain ⟨x, y⟩ := a
  constructor
  · intro h
    rcases x with ⟨(_ | _), _⟩ | _ | _ <;> simp_all [RowWire.decode?]
  · rintro ⟨⟩; rfl

/-- [A0 M8] `processed` of a carried row is pool membership. -/
theorem processedS_ofRow (st : State p.n) {a : RowWire p.n} {i : Fin p.n}
    {body : RowPayload} (h : a.decode? = some (i, body)) :
    processedS p st (ofRow p a) = decide (a ∈ st.rowPool) := by
  obtain rfl := rowWire_decode.mp h
  rfl

/-- [R5] A decoded carried row is never excluded. -/
theorem excludesS_ofRow (st : State p.n) {a : RowWire p.n} {i : Fin p.n}
    {body : RowPayload} (h : a.decode? = some (i, body)) :
    excludesS p st (ofRow p a) = false := by
  obtain rfl := rowWire_decode.mp h
  rfl

/-- [A0 M8] A carried row is handled at a delivery exactly when it is the
delivered object, or it is one of the rows of a delivered proposal that the
store accepts. -/
theorem handlesS_ofRow_iff (st : State p.n) (o : Obj p) (a : RowWire p.n) :
    handlesS p st o (ofRow p a) ↔ o = ofRow p a ∨
      ∃ s b raw sup rows P, (toWire p o).decode = some (.block s b raw sup rows) ∧
        parentFG st b = some P ∧ blockAccepted p st s b raw sup P rows = true ∧ a ∈ rows := by
  unfold handlesS
  refine or_congr Iff.rfl ?_
  constructor
  · intro h
    split at h
    · rename_i s b raw sup rows hd
      obtain ⟨⟨P, hP, hacc⟩, hmem⟩ := h
      refine ⟨s, b, raw, sup, rows, P, hd, hP, hacc, ?_⟩
      rcases hmem with hmem | hmem
      · obtain ⟨h', -, e⟩ := List.mem_map.mp hmem
        have e' := congrArg (toWire p) e
        rw [toWire_ofHead, toWire_ofRow] at e'
        simp at e'
      · obtain ⟨a', ha', e⟩ := List.mem_map.mp hmem
        rwa [ofRow_injective e] at ha'
    · exact h.elim
  · rintro ⟨s, b, raw, sup, rows, P, hd, hP, hacc, ha⟩
    rw [hd]
    exact ⟨⟨P, hP, hacc⟩, Or.inr (List.mem_map_of_mem ha)⟩

end AvailableChain.FGSA.Run

end
