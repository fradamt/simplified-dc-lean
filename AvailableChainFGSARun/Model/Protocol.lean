module
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Ring
public import AvailableChainEngineV2.Engine.Spec
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Model.Clock
public import AvailableChainFGSA.Model.Frame

@[expose] public section

/-! The FG-SA protocol on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, §3.1 and T7.2).

The v2 protocol `fgsa p c` runs the store model `AvailableChainFGSA` without a
change. The node state is the store and the client record Λ (`Node`). The v2
payload is the store payload `Msg p.n`. A v2 object reaches the store through
the adapter `toWire`, a bijection (`toWireEquiv`), so the store's decode
discipline (J1) does not change. Every hook reads only the store: the store
functions below (`depsS`, `processedS`, `excludesS`, `handlesS`) take the
store, and `fgsa` applies them to `nd.st`. The FG action (`attest`) is the
only duty that reads Λ, and `recordOwn` is the only step that writes it.

v1 `Auth` and `Signed` (namespace `AvailableChain`) and v2 `Auth` and `Signed`
(namespace `AvailableChain.V2`) clash, so this file writes the v2 names as
`V2.…` and does not open `AvailableChain.V2`. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- [plan T7.2; 2c I1] The application codec: the run input `x : In` enters the
proposal body as the number `app x`, and `unapp` decodes it (`unapp_app`: a
left inverse of `app`). -/
structure AppCodec (In : Type) where
  app : In → Nat
  unapp : Nat → Option In
  unapp_app : ∀ x, unapp (app x) = some x

/-- [plan T7.2; I9] The codec of the unit input: application value `0`, so the
honest proposal is the I9 `propose` output (`withApp_zero`). -/
def unitCodec : AppCodec Unit where
  app _ := 0
  unapp _ := some ()
  unapp_app _ := rfl

/-- [spec 197–220; FRAMEWORK E1; plan T7.2] The v2 duty labels: a store label
(the HEAD of a slot or the FG action of a round) or the proposal duty of a
slot. A proposal duty is a label with one seat. -/
inductive RunLabel where
  | base (ℓ : Label)
  | prop (s : Slot)
  deriving DecidableEq, Repr

namespace RunLabel

/-- [spec 154–158; FRAMEWORK E1] The committee size of a label: `n` seats for a
store label, one seat for a proposal duty. -/
def seats (p : Params) : RunLabel → Nat
  | .base _ => p.n
  | .prop _ => 1

/-- [spec 197–220] The act time: `v_s` for a HEAD, `a_r` for an FG action,
`t_s` for a proposal. -/
def actTime (p : Params) : RunLabel → Time
  | .base ℓ => Label.actTime p ℓ
  | .prop s => SA.proposalTime p.toParams s

/-- [spec 681; FRAMEWORK E5; plan T7.2] Only an FG label is self-visible: the
node records its own FG row in Λ at its tick. -/
def selfVisible : RunLabel → Bool
  | .base (.fg _) => true
  | _ => false

end RunLabel

/-- [plan §3.1; DQ4] The node state: the store (Λ-free, the E5 base) and the
client record Λ. -/
structure Node (p : Params) where
  st : State p.n
  /-- Λ. The plan calls this field `rec`; Lean reserves `Node.rec` for the
  recursor of the structure. -/
  record : Record

/-- [plan §3.1] The v2 wire objects of FG-SA. -/
abbrev Obj (p : Params) : Type := V2.Signed RunLabel (RunLabel.seats p) (Msg p.n)

/-! ### The adapter to the store wire (plan §3.1) -/

/-- [plan §3.1; FRAMEWORK :336] The store authentication of a v2
authentication: a store-label seat keeps its label and seat; the seat of a
proposal duty is the proposer key of its slot (`Fin 1` has one value); an
unsigned object stays unsigned. -/
def toAuth (p : Params) : V2.Auth RunLabel (RunLabel.seats p) → Auth Label p.n
  | .seat (.base ℓ) i => .seat ℓ i
  | .seat (.prop s) _ => .proposer s
  | .none => .none

/-- [plan §3.1] The inverse of `toAuth`. -/
def ofAuth (p : Params) : Auth Label p.n → V2.Auth RunLabel (RunLabel.seats p)
  | .seat ℓ i => .seat (.base ℓ) i
  | .proposer s => .seat (.prop s) ⟨0, Nat.one_pos⟩
  | .none => .none

/-- [plan §3.1; J1] The store wire of a v2 object: the authentication through
`toAuth`, the payload unchanged. Every store handler and the input check see
only `toWire o`. A malformed pair of authentication and payload gives a
malformed store wire, which `Wire.decode` refuses. -/
def toWire (p : Params) (o : Obj p) : Wire p.n := ⟨toAuth p o.auth, o.payload⟩

/-- [plan §3.1] The v2 object of a store wire (the inverse of `toWire`). -/
def ofWire (p : Params) (w : Wire p.n) : Obj p := ⟨ofAuth p w.auth, w.payload⟩

/-- [plan §3.1; Opus m15] The adapter is a bijection. -/
def toWireEquiv (p : Params) : Obj p ≃ Wire p.n where
  toFun := toWire p
  invFun := ofWire p
  left_inv := by
    rintro ⟨a, m⟩
    cases a with
    | seat ℓ i =>
        cases ℓ with
        | base ℓ => rfl
        | prop s =>
            have hi : i = ⟨0, Nat.one_pos⟩ := Subsingleton.elim (α := Fin 1) _ _
            subst hi
            rfl
    | none => rfl
  right_inv := by
    rintro ⟨a, m⟩
    cases a <;> rfl

/-- [plan §3.1] A carried HEAD as a v2 object (through the inverse adapter). -/
def ofHead (p : Params) (h : HeadWire p.n) : Obj p := ofWire p ⟨h.auth, .head h.payload⟩

/-- [plan §3.1] A carried row as a v2 object (through the inverse adapter). -/
def ofRow (p : Params) (a : RowWire p.n) : Obj p := ofWire p ⟨a.auth, .row a.payload⟩

/-! ### Duties -/

/-- [spec 197–220] The labels due at time `t`: the proposal of the slot whose
proposal time is `t`, the HEAD of the slot whose vote time is `t`, and the FG
action of the round whose action time is `t`. The three candidates come from
the slot of `t` (the action time of round `r` is in slot `rR + 1`), and each
one is due only if its act time is `t`. -/
def duties (p : Params) (t : Time) : List RunLabel :=
  let s := p.slotOf t
  let r := (s - 1) / p.R
  (if SA.proposalTime p.toParams s = t then [.prop s] else []) ++
    (if SA.voteTime p.toParams s = t then [.base (.head s)] else []) ++
    (if p.actionTime r = t then [.base (.fg r)] else [])

/-- The slot of a time in slot `s` at offset `k`, `0 ≤ k < 4Δ`, is `s`. -/
theorem slotOf_offset (p : Params) (s : Slot) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < 4 * p.Δ) : p.slotOf (4 * p.Δ * s + k) = s := by
  have hΔ : (4 * p.Δ : Int) ≠ 0 := by have : (0 : Int) < p.Δ := p.deltaPos; omega
  unfold Params.slotOf
  rw [add_comm, Int.add_mul_ediv_left _ _ hΔ, Int.ediv_eq_zero_of_lt hk0 hk, zero_add,
    Int.toNat_natCast]

theorem duties_spec (p : Params) (ℓ : RunLabel) (t : Time) :
    ℓ ∈ duties p t ↔ RunLabel.actTime p ℓ = t := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hR : 0 < p.R := by have := p.RLarge; omega
  simp only [duties, List.mem_append]
  constructor
  · intro h
    rcases h with (h | h) | h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
  · intro h
    cases ℓ with
    | prop s =>
        have h' : SA.proposalTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + 0 := by
          rw [← h']; simp [SA.proposalTime, GridCO.proposalTime, SA.Params.engine]
        have hs : p.slotOf t = s := by rw [ht]; exact slotOf_offset p s 0 le_rfl (by omega)
        left; left
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _
    | base ℓ =>
        cases ℓ with
        | head s =>
            have h' : SA.voteTime p.toParams s = t := h
            have ht : t = 4 * p.Δ * s + p.Δ := by
              rw [← h']; simp [SA.voteTime, GridCO.voteTime, GridCO.proposalTime,
                SA.Params.engine]
            have hs : p.slotOf t = s := by
              rw [ht]; exact slotOf_offset p s p.Δ (by omega) (by omega)
            left; right
            rw [hs, ite_eq_left h']
            exact List.mem_singleton_self _
        | fg r =>
            have h' : p.actionTime r = t := h
            have ht : t = 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ := by
              rw [← h']
              simp only [Params.actionTime, SA.gateTime, GridCO.gateTime, GridCO.proposalTime,
                SA.Params.engine]
              push_cast
              ring
            have hs : p.slotOf t = r * p.R + 1 := by
              rw [ht]; exact slotOf_offset p _ (2 * p.Δ) (by omega) (by omega)
            have hr : (p.slotOf t - 1) / p.R = r := by
              rw [hs, Nat.add_sub_cancel, Nat.mul_div_cancel _ hR]
            right
            rw [hr, ite_eq_left h']
            exact List.mem_singleton_self _

theorem duties_nodup (p : Params) (t : Time) : (duties p t).Nodup := by
  simp only [duties]
  split_ifs <;> simp

/-! ### Duty payloads -/

/-- [plan T7.2; 2c I1; I9 D5, D9] Put the application value `a` into a proposal:
the block body becomes the packed body of `a` with the carried rows, and the
rows stay. On the I9 `propose` output (`packBody 0 rows`) it replaces only the
application value (`withApp_zero`, `rowsOk_withApp`). Every other payload does
not change. -/
def withApp {n : Nat} (a : Nat) : Msg n → Msg n
  | .proposal (.node H s _) raw sup rows => .proposal (.node H s (packBody a rows)) raw sup rows
  | m => m

/-- [spec 1236–1253, 1276–1302; plan T7.2] The payload of the base duties (the
AP labels): the HEAD vote at `v_s` and the proposal at `t_s`, with the input in
the body. It reads only the store. There is no base payload for an FG label. -/
def actS (p : Params) {In : Type} (c : AppCodec In) (st : State p.n) :
    RunLabel → In → Option (Msg p.n)
  | .base (.head s), _ => some (.head (headVote p st s))
  | .base (.fg _), _ => none
  | .prop s, x => (propose p st s).map (withApp (c.app x))

/-- [spec 1304–1313, 1391–1399; plan T7.2] The payload of a duty: `actS` on the
base labels, and the `attest` row body on an FG label. `attest` reads Λ; its
identity argument does not change the body (`attest_signer_irrel`), so seat
`0` is used. `act` returns `none` for `.prop 0` (`propose`). -/
def act (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    RunLabel → In → Option (Msg p.n)
  | .base (.fg _), _ => some (.row (attest p nd.st nd.record ⟨0, p.nPos⟩).1)
  | ℓ, x => actS p c nd.st ℓ x

/-- [spec 681, 1391–1399; Opus m11] The own-record step: an FG row signed with
seat `i` records the row `⟨i, height pair, finality pair⟩` in Λ
(`record_row`, which does not read the signer); any other object leaves Λ
unchanged. -/
def recordRow? (p : Params) (Λ : Record) (o : Obj p) : Record :=
  match o with
  | ⟨.seat (.base (.fg _)) i, .row body⟩ =>
      record_row Λ (⟨i, body.height_pair, body.finality_pair⟩ : Row (Fin p.n))
  | _ => Λ

/-! ### Hooks on the store

Each hook is a function of the store and reads the object through `toWire`. A
malformed wire decodes to `none`: `process` refuses it, and it is not
processed and not excluded. -/

/-- [spec 519–522; I9 D2; plan T7.2] Dependencies: a proposal needs its stored
FG parent (`parentFG`, the root lookup); every other object has none. -/
def depsS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.block _ b _ _ _) => (parentFG st b).isSome
  | _ => true

/-- [spec 804–857; DQ9; plan T7.2] Processed: a proposal by root (a stored FG
block has the root of its block, the duplicate test of `blockAccepted`); a
HEAD if its base vote is in the vote pool; a row if it is in the row pool
(which only grows). -/
def processedS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) => decide (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ st.base.votes)
  | some (.row r i body) => decide ((⟨.seat (.fg r) i, body⟩ : RowWire p.n) ∈ st.rowPool)
  | some (.block _ b _ _ _) => decide (∃ Y ∈ st.fg.TF, Y.root = b.root)
  | none => false

/-- The rows of seat `i` and round `r` in the row pool (the identity and
round of each pool row come from its decoder). -/
def rowCount {n : Nat} (st : State n) (r : Nat) (i : Fin n) : Nat :=
  (st.rowPool.filter (fun c => c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))).length

/-- [spec 360–366, 831–857] The row clause of `excludesS` at the signed row `a`
of round `r` and seat `i`: `a` is not in the pool, and it is old
(`r + w_F < round now`) or its seat has two rows of round `r` in the pool. -/
def rowExcl (p : Params) (st : State p.n) (a : RowWire p.n) (r : Nat) (i : Fin p.n) : Bool :=
  !decide (a ∈ st.rowPool) &&
    (decide (r + p.wF < p.round (st.slot p)) || decide (2 ≤ rowCount st r i))

/-- [spec 360–366, 831–857; DQ9; I9 D2; plan T7.2] Excluded for good: a proposal
whose block is not compatible with F (`blockExcluded`); a HEAD that the Grid CO
vote pool excludes (an old label or an equivocation, not stored); a row that
is not in the pool and is old (`r + w_F < round now`) or whose seat already
has two rows of round `r` in the pool. A future row (`round now < r`) is a
temporary refusal, not an exclusion. There is no root clause. -/
def excludesS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) =>
      GridCO.excludes p.toParams.engine st.base (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n))
  | some (.row r i body) => rowExcl p st ⟨.seat (.fg r) i, body⟩ r i
  | some (.block _ b _ _ _) => blockExcluded st b
  | none => false

/-- [spec 804–829; plan T7.2] Handler calls: the delivered object itself; for a
proposal that the store accepts (`parentFG` and `blockAccepted`, the tests of
`admitBlock`), also its carried HEADs (the raw votes) and its carried rows, as
v2 objects (`ofHead`, `ofRow`). -/
def handlesS (p : Params) (st : State p.n) (o o' : Obj p) : Prop :=
  o = o' ∨ match (toWire p o).decode with
    | some (.block s b raw _ rows) =>
        (∃ P, parentFG st b = some P ∧ blockAccepted p st s b P rows = true) ∧
          (o' ∈ raw.map (ofHead p) ∨ o' ∈ rows.map (ofRow p))
    | _ => False

/-- [spec 248–255; plan T7.2] Structural containment: a proposal payload
carries its raw HEADs, its support HEADs and its rows. -/
def carriesS (p : Params) (o o' : Obj p) : Prop :=
  match o.payload with
  | .proposal _ raw sup rows =>
      o' ∈ raw.map (ofHead p) ∨ o' ∈ sup.map (ofHead p) ∨ o' ∈ rows.map (ofRow p)
  | _ => False

/-! ### The protocol -/

/-- [plan T7.2; FRAMEWORK E1, E2, E5, E6] FG-SA on engine v2, with the
application codec `c`.

* State: the store and Λ (`Node`). A restart keeps Λ (`Durable := Record`, the
  slashing-protection database; user decision, plan §1a) and restarts the
  store from `initial`, so the base after a restore does not depend on the
  kept data (E5 restore law).
* `clock` and `process` run the store functions and keep Λ; `recordOwn`
  writes only Λ (`recordRow?`).
* `act`: HEAD and proposal from the store (`actS`), FG row from `attest`.
* The hooks are the store hooks (`depsS`, `processedS`, `excludesS`,
  `handlesS`) at `nd.st`. -/
def fgsa (p : Params) {In : Type} (c : AppCodec In) : V2.ProtocolSpec In where
  State := Node p
  Label := RunLabel
  seats := RunLabel.seats p
  Payload := Msg p.n
  Durable := Record
  init := ⟨initial p.n, Record.initial⟩
  clock nd t := { nd with st := FGSA.clock p nd.st t }
  actTime := RunLabel.actTime p
  duties := duties p
  duties_spec := duties_spec p
  duties_nodup := duties_nodup p
  act := act p c
  gossip _ _ := []
  process nd o := { nd with st := FGSA.process p nd.st (toWire p o) }
  selfVisible := RunLabel.selfVisible
  recordOwn nd o := { nd with record := recordRow? p nd.record o }
  durable nd := nd.record
  restore d := ⟨initial p.n, d⟩
  wellFormed o := FGSA.wellFormed p (toWire p o)
  depsPresent nd o := depsS p nd.st o
  processed nd o := processedS p nd.st o
  excludes nd o := excludesS p nd.st o
  handles nd o o' := handlesS p nd.st o o'
  carries := carriesS p

/-- Labels of `fgsa` have decidable equality (the instance of `RunLabel`; the
projection does not unfold at instance transparency). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (fgsa p c).Label :=
  inferInstanceAs (DecidableEq RunLabel)

/-- Payloads of `fgsa` have decidable equality (the instance of `Msg`). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (fgsa p c).Payload :=
  inferInstanceAs (DecidableEq (Msg p.n))

end AvailableChain.FGSA.Run

end
