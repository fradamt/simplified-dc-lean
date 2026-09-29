module
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSARun.Model.Families

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
theorem restore_st (d : Record) : ((fgsa p c).restore d).st = initial p.n := rfl

/-- [plan §1a restart decision] A restart keeps Λ. -/
theorem restore_rec (d : Record) : ((fgsa p c).restore d).record = d := rfl

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
not depend on the identity: `createRow` uses the signer only in `Row.signer`,
`record_row` does not read it, and `RowBody.ofRow` drops it. -/
theorem attest_signer_irrel (st : State p.n) (Λ : Record) (i j : Fin p.n) :
    attest p st Λ i = attest p st Λ j := rfl

/-- [plan T7.2] The payload of an FG label is the `attest` row body. -/
theorem act_fg (nd : Node p) (r : Nat) (x : In) :
    (fgsa p c).act nd (.base (.fg r)) x = some (.row (attest p nd.st nd.record ⟨0, p.nPos⟩).1) :=
  rfl

/-- [spec 681, 1391–1399; plan T7.2] Recording the emitted FG row, with any seat,
gives the record of `attest`. -/
theorem recordOwn_attest (nd : Node p) (r : Nat) (i : Fin p.n) :
    ((fgsa p c).recordOwn nd
        ⟨.seat (.base (.fg r)) i, .row (attest p nd.st nd.record ⟨0, p.nPos⟩).1⟩).record =
      (attest p nd.st nd.record ⟨0, p.nPos⟩).2 := rfl

/-! ### The proposal -/

/-- [plan T7.2] The payload of a proposal label is the store proposal with the
application value of the input. -/
theorem act_prop (nd : Node p) (s : Slot) (x : In) :
    (fgsa p c).act nd (.prop s) x = (propose p nd.st s).map (withApp (c.app x)) := rfl

/-- [plan T7.2] There is no proposal at slot `0`. -/
theorem act_prop_zero (nd : Node p) (x : In) : (fgsa p c).act nd (.prop 0) x = none := rfl

/-- [plan T7.2; I9] `withApp 0` does not change the I9 `propose` output. So with
`unitCodec` the honest proposal is the I9 proposal. -/
theorem withApp_zero (st : State p.n) (s : Slot) :
    (propose p st s).map (withApp 0) = propose p st s := by
  unfold propose
  split <;> rfl

/-- [plan T7.2; I9 D9; Opus M2] The proposal with application value `a` is a
proposal whose block is a node of slot `s` with the packed body of `a` and its
carried rows. So the block passes the content check `rowsOk` with its carried
rows, and its application value is `a`. -/
theorem rowsOk_withApp (st : State p.n) (s : Slot) (a : Nat) {m : Msg p.n}
    (h : (propose p st s).map (withApp a) = some m) :
    ∃ H raw sup rows, m = .proposal (.node H s (packBody a rows)) raw sup rows ∧
      rowsOk (.node H s (packBody a rows)) rows = true ∧
      appOf (Block.node H s (packBody a rows)).body = a := by
  unfold propose at h
  split at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨_, _, _, _, rfl, ?_, appOf_packBody _ _⟩
    simp [rowsOk, Block.body, appOf_packBody]

/-! ### Label families and isolation -/

/-- [plan T7.2; 2a Task 3 Step 5] A proposal label has one seat. -/
theorem singleSeat_prop : V2.SingleSeat (fgsa p c) (fun ℓ => ∃ s, ℓ = .prop s) := by
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
theorem tick_st {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (nd : Node p) (v : V) (t : Time) :
    (V2.tick E rho nd v t).1.st = FGSA.clock p nd.st t :=
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
theorem decode_eq_row {n : Nat} {w : Wire n} {r : Nat} {i : Fin n} {body : RowBody} :
    w.decode = some (.row r i body) ↔ w = ⟨.seat (.fg r) i, .row body⟩ := by
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
theorem rowWire_decode {n : Nat} {a : RowWire n} {r : Nat} {i : Fin n} {body : RowBody} :
    a.decode? = some (r, i, body) ↔ a = ⟨.seat (.fg r) i, body⟩ := by
  obtain ⟨x, y⟩ := a
  constructor
  · intro h
    rcases x with ⟨(_ | _), _⟩ | _ | _ <;> simp_all [RowWire.decode?]
  · rintro ⟨⟩; rfl

/-- [A0 M8] `processed` of a carried row is pool membership. -/
theorem processedS_ofRow (st : State p.n) {a : RowWire p.n} {r : Nat} {i : Fin p.n}
    {body : RowBody} (h : a.decode? = some (r, i, body)) :
    processedS p st (ofRow p a) = decide (a ∈ st.rowPool) := by
  obtain rfl := rowWire_decode.mp h
  rfl

/-- [A0 M8] `excludes` of a carried row: not in the pool, and old or capped. -/
theorem excludesS_ofRow (st : State p.n) {a : RowWire p.n} {r : Nat} {i : Fin p.n}
    {body : RowBody} (h : a.decode? = some (r, i, body)) :
    excludesS p st (ofRow p a) = rowExcl p st a r i := by
  obtain rfl := rowWire_decode.mp h
  rfl

/-- The row clause as a proposition: not in the pool, and old or capped. -/
theorem rowExcl_iff (st : State p.n) (a : RowWire p.n) (r : Nat) (i : Fin p.n) :
    rowExcl p st a r i = true ↔
      a ∉ st.rowPool ∧ (r + p.wF < p.round (st.slot p) ∨ 2 ≤ rowCount st r i) := by
  simp [rowExcl]

/-- [A0 M8] A carried row is handled at a delivery exactly when it is the
delivered object, or it is one of the rows of a delivered proposal that the
store accepts. -/
theorem handlesS_ofRow_iff (st : State p.n) (o : Obj p) (a : RowWire p.n) :
    handlesS p st o (ofRow p a) ↔ o = ofRow p a ∨
      ∃ s b raw sup rows P, (toWire p o).decode = some (.block s b raw sup rows) ∧
        parentFG st b = some P ∧ blockAccepted p st s b P rows = true ∧ a ∈ rows := by
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
