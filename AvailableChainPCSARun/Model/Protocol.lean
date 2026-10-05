module
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Ring
public import AvailableChainEngineV2.Engine.Duty.Spec
public import AvailableChainPCSA.Model.Handlers
public import AvailableChainPCSA.Model.Clock
public import AvailableChainPCSA.Model.Frame

@[expose] public section

/-! The PC-SA protocol on engine v2 (FG-SA `AvailableChainFGSARun/Model/Protocol.lean`
with the ack duty; pcsa-decisions 3n/4).

The v2 protocol `pcsa p c` runs the store model `AvailableChainPCSA` without a
change. The node state is the store and the client record Λ (`Node`). The v2
payload is the store payload `Msg p.n`. A v2 object reaches the store through
the adapter `toWire`, a bijection (`toWireEquiv`), so the store's decode
discipline (J1) does not change. Every hook reads only the store. The FG
action (`attest`) is the only duty that reads Λ, and `recordOwn` is the only
step that writes it. The ack duty (`ackAction s`) runs at `e_s` and sends
only; its payload is the store read `ackTarget?`.

v1 `Auth` and `Signed` (namespace `AvailableChain`) and v2 `Auth` and `Signed`
(namespace `AvailableChain.V2`) clash, so this file writes the v2 names as
`V2.D.…` and does not open `AvailableChain.V2`. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

/-- [PC-SA M1] [plan T7.2; 2c I1] The application codec: the run input `x : In` enters the
proposal body as the number `app x`, and `unapp` decodes it (`unapp_app`: a
left inverse of `app`). -/
structure AppCodec (In : Type) where
  app : In → Nat
  unapp : Nat → Option In
  unapp_app : ∀ x, unapp (app x) = some x

/-- [PC-SA M1] [plan T7.2; I9] The codec of the unit input: application value `0`, so the
honest proposal is the I9 `propose` output. -/
def unitCodec : AppCodec Unit where
  app _ := 0
  unapp _ := some ()
  unapp_app _ := rfl

/-- [PC-SA M1] Signing labels: a HEAD label and an ack label for each slot, one
fixed FG label, and one proposal label for each slot. Duties are separate
scheduled actions. -/
inductive RunLabel where
  | base (ℓ : Label)
  | prop (s : Slot)
  deriving DecidableEq, Repr

namespace RunLabel

/-- [PC-SA M1] [spec 154–158; FRAMEWORK E1] The committee size of a label: `n` seats for a
store label, one seat for a proposal duty. -/
def seats (p : Params) : RunLabel → Nat
  | .base _ => p.n
  | .prop _ => 1

/-- [PC-SA M1] [spec 681; FRAMEWORK E5; plan T7.2] Only an FG label is self-visible: the
node records its own FG row in Λ at its tick. -/
def selfVisible : RunLabel → Bool
  | .base .fg => true
  | _ => false

end RunLabel

/-- [PC-SA M1; pcsa-decisions 3n/4] Scheduled actions. FG actions share one
signing label. The ack action of slot `s` runs at `e_s`. -/
inductive RunDuty where
  | headAction (s : Slot)
  | fgAction (r : Nat)
  | propAction (s : Slot)
  | ackAction (s : Slot)
  deriving DecidableEq, Repr

/-- [PC-SA M1] The signing identity of an action. -/
def RunDuty.signLabel : RunDuty → RunLabel
  | .headAction s => .base (.head s)
  | .fgAction _ => .base .fg
  | .propAction s => .prop s
  | .ackAction s => .base (.ack s)

/-- [PC-SA M1] The scheduled time of an action. -/
def RunDuty.actTime (p : Params) : RunDuty → Time
  | .headAction s => SA.voteTime p.toParams s
  | .fgAction r => p.actionTime r
  | .propAction s => SA.proposalTime p.toParams s
  | .ackAction s => SA.earlyTime p.toParams s

/-- [PC-SA M1] [plan §3.1; DQ4] The node state: the store (Λ-free, the E5 base) and the
client record Λ. -/
structure Node (p : Params) where
  st : State p.n
  /-- [PC-SA M1] Λ. The plan calls this field `rec`; Lean reserves `Node.rec` for the
  recursor of the structure. -/
  record : RecordOnce

/-- [PC-SA M1] [plan §3.1] The v2 wire objects of PC-SA. -/
abbrev Obj (p : Params) : Type := V2.Signed RunLabel (RunLabel.seats p) (Msg p.n)

/-! ### The adapter to the store wire (plan §3.1) -/

/-- [PC-SA M1] [plan §3.1; FRAMEWORK :336] The store authentication of a v2
authentication: a store-label seat keeps its label and seat; the seat of a
proposal duty is the proposer key of its slot (`Fin 1` has one value); an
unsigned object stays unsigned. -/
def toAuth (p : Params) : V2.Auth RunLabel (RunLabel.seats p) → Auth Label p.n
  | .seat (.base ℓ) i => .seat ℓ i
  | .seat (.prop s) _ => .proposer s
  | .none => .none

/-- [PC-SA M1] [plan §3.1] The inverse of `toAuth`. -/
def ofAuth (p : Params) : Auth Label p.n → V2.Auth RunLabel (RunLabel.seats p)
  | .seat ℓ i => .seat (.base ℓ) i
  | .proposer s => .seat (.prop s) ⟨0, Nat.one_pos⟩
  | .none => .none

/-- [PC-SA M1] [plan §3.1; J1] The store wire of a v2 object: the authentication through
`toAuth`, the payload unchanged. Every store handler and the input check see
only `toWire o`. A malformed pair of authentication and payload gives a
malformed store wire, which `Wire.decode` refuses. -/
def toWire (p : Params) (o : Obj p) : Wire p.n := ⟨toAuth p o.auth, o.payload⟩

/-- [PC-SA M1] [plan §3.1] The v2 object of a store wire (the inverse of `toWire`). -/
def ofWire (p : Params) (w : Wire p.n) : Obj p := ⟨ofAuth p w.auth, w.payload⟩

/-- [PC-SA M1] [plan §3.1; Opus m15] The adapter is a bijection. -/
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

/-- [PC-SA M1] [plan §3.1] A carried HEAD as a v2 object (through the inverse adapter). -/
def ofHead (p : Params) (h : HeadWire p.n) : Obj p := ofWire p ⟨h.auth, .head h.payload⟩

/-- [PC-SA M1] [plan §3.1] A carried row as a v2 object (through the inverse adapter). -/
def ofRow (p : Params) (a : RowWire p.n) : Obj p := ofWire p ⟨a.auth, .row a.payload⟩

/-- [PC-SA M1; pcsa-decisions R-e] A carried ack (of a PC) as a v2 object. -/
def ofAck (p : Params) (a : AckWire p.n) : Obj p := ofWire p ⟨a.auth, .ack a.payload⟩

/-! ### Duties -/

/-- [PC-SA M1; FG-SA duties; pcsa-decisions 3n/4] [spec 197–220] The labels
due at time `t`: the proposal of the slot whose proposal time is `t`, the
HEAD of the slot whose vote time is `t`, the FG action of the round whose
action time is `t`, and the ack of the slot whose early time is `t` (after
the FG action when `e_s = a_r`). The candidates come from the slot of `t`
(the action time of round `r` is in slot `rR + 1`), and each one is due only
if its act time is `t`. -/
def duties (p : Params) (t : Time) : List RunDuty :=
  let s := p.slotOf t
  let r := (s - 1) / p.R
  (if SA.proposalTime p.toParams s = t then [.propAction s] else []) ++
    (if SA.voteTime p.toParams s = t then [.headAction s] else []) ++
    (if p.actionTime r = t then [.fgAction r] else []) ++
    (if SA.earlyTime p.toParams s = t then [.ackAction s] else [])

/-- [PC-SA M1] The slot of a time in slot `s` at offset `k`, `0 ≤ k < 4Δ`, is `s`. -/
theorem slotOf_offset (p : Params) (s : Slot) (k : Int) (hk0 : 0 ≤ k)
    (hk : k < 4 * p.Δ) : p.slotOf (4 * p.Δ * s + k) = s := by
  have hΔ : (4 * p.Δ : Int) ≠ 0 := by have : (0 : Int) < p.Δ := p.deltaPos; omega
  unfold FGSA.Params.slotOf
  rw [add_comm, Int.add_mul_ediv_left _ _ hΔ, Int.ediv_eq_zero_of_lt hk0 hk, zero_add,
    Int.toNat_natCast]

theorem duties_spec (p : Params) (ℓ : RunDuty) (t : Time) :
    ℓ ∈ duties p t ↔ RunDuty.actTime p ℓ = t := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  have hR : 0 < p.R := by have := p.RLarge; omega
  simp only [duties, List.mem_append]
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · split_ifs at h with ht
      · rw [List.mem_singleton] at h; subst h; exact ht
      · simp at h
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
    | propAction s =>
        have h' : SA.proposalTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + 0 := by
          rw [← h']; simp [SA.proposalTime, GridCO.proposalTime, SA.Params.engine]
        have hs : p.slotOf t = s := by rw [ht]; exact slotOf_offset p s 0 le_rfl (by omega)
        left; left; left
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _
    | headAction s =>
        have h' : SA.voteTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + p.Δ := by
          rw [← h']; simp [SA.voteTime, GridCO.voteTime, GridCO.proposalTime,
            SA.Params.engine]
        have hs : p.slotOf t = s := by
          rw [ht]; exact slotOf_offset p s p.Δ (by omega) (by omega)
        left; left; right
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _
    | fgAction r =>
        have h' : p.actionTime r = t := h
        have ht : t = 4 * p.Δ * ((r * p.R + 1 : Nat) : Int) + 2 * p.Δ := by
          rw [← h']
          simp only [FGSA.Params.actionTime, SA.gateTime, GridCO.gateTime, GridCO.proposalTime,
            SA.Params.engine]
          push_cast
          ring
        have hs : p.slotOf t = r * p.R + 1 := by
          rw [ht]; exact slotOf_offset p _ (2 * p.Δ) (by omega) (by omega)
        have hr : (p.slotOf t - 1) / p.R = r := by
          rw [hs, Nat.add_sub_cancel, Nat.mul_div_cancel _ hR]
        left; right
        rw [hr, ite_eq_left h']
        exact List.mem_singleton_self _
    | ackAction s =>
        have h' : SA.earlyTime p.toParams s = t := h
        have ht : t = 4 * p.Δ * s + 2 * p.Δ := by
          rw [← h']; simp [SA.earlyTime, GridCO.earlyTime, GridCO.proposalTime,
            SA.Params.engine]
        have hs : p.slotOf t = s := by
          rw [ht]; exact slotOf_offset p s (2 * p.Δ) (by omega) (by omega)
        right
        rw [hs, ite_eq_left h']
        exact List.mem_singleton_self _

theorem duties_nodup (p : Params) (t : Time) : (duties p t).Nodup := by
  simp only [duties]
  split_ifs <;> simp

/-! ### Duty payloads -/

/-- [PC-SA M1] Replace the app and recompute the full digest. The BODY codec,
signed rows, raw list, support list and carried PC keep their roles. -/
def withApp (p : Params) (a : Nat) : Msg p.n → Msg p.n
  | .proposal (.node P s _ _ raw sup rows pc) =>
      .proposal (namedProposal p P s a raw sup rows pc)
  | m => m

/-- [PC-SA M1; pcsa-decisions 3n/4] [spec 1236–1253, 1276–1302; plan T7.2]
The payload of the base duties (the AP labels): the HEAD vote at `v_s`, the
proposal at `t_s` with the input in the body, and the ack at `e_s` on the
trigger target (`ackTarget?`; no payload when no block has `N(s, B)`). It
reads only the store. There is no base payload for an FG label. -/
def actS (p : Params) {In : Type} (c : AppCodec In) (st : State p.n) :
    RunDuty → In → Option (Msg p.n)
  | .headAction s, _ => some (.head (headVote p st s).root)
  | .fgAction _, _ => none
  | .propAction s, x => (propose p st s).map (withApp p (c.app x))
  | .ackAction s, _ => (ackTarget? p st s).map Msg.ack

/-- [PC-SA M1] [spec 1304–1313, 1391–1399; plan T7.2] The payload of a duty: `actS` on the
base labels, and the `attest` row body on an FG label. `attest` reads Λ; its
identity argument does not change the body, so seat `0` is used. `act`
returns `none` for `.prop 0` (`propose`). -/
def act (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) :
    RunDuty → In → Option (Msg p.n)
  | .fgAction _, _ => (attest p nd.st nd.record ⟨0, p.nPos⟩).1.map Msg.row
  | ℓ, x => actS p c nd.st ℓ x

/-- [PC-SA M1] [spec 681, 1391–1399; Opus m11] The own-record step: an FG row signed with
seat `i` records the row `⟨i, height pair, finality pair⟩` in Λ
(`record_row_once`, which does not read the signer); any other object leaves Λ
unchanged. -/
def recordRow? (p : Params) (Λ : RecordOnce) (o : Obj p) : RecordOnce :=
  match o with
  | ⟨.seat (.base .fg) i, .row body⟩ =>
      record_row_once Λ (body.toRow i)
  | _ => Λ

/-! ### Hooks on the store

Each hook is a function of the store and reads the object through `toWire`. A
malformed wire decodes to `none`: `process` refuses it, and it is not
processed and not excluded. -/

/-- [PC-SA M1] [spec 519–522; I9 D2; plan T7.2] Dependencies: a proposal needs its stored
exact named parent and its FG projection (`parentFG`); other objects have none. -/
def depsS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.block _ N) => namedParentHeld st N && (parentFG st N.erase).isSome
  | _ => true

/-- [PC-SA M1; pcsa-decisions 3n/4] [spec 804–857; DQ9; plan T7.2] Processed:
a proposal by root (a stored FG block has the root of its block, the
duplicate test of `blockAccepted`); a HEAD if its base vote is in the vote
pool; a row if it is in the row pool; an ack if it is in the ack pool; a PC
if every ack of it is in the ack pool (the pools only grow). -/
def processedS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) => decide (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ st.base.votes)
  | some (.row i body) => decide ((⟨.seat .fg i, body⟩ : RowWire p.n) ∈ st.rowPool)
  | some (.block _ N) => decide (∃ Y ∈ st.fg.TF, Y.root = N.root)
  | some (.ack s i b) => decide ((⟨.seat (.ack s) i, b⟩ : AckWire p.n) ∈ st.ackPool)
  | some (.pc c) => c.acks.all (fun a => decide (a ∈ st.ackPool))
  | none => false

/-- [PC-SA M1] [R6] Permanent invalidity once the immutable parent is held. An absent
parent is a missing dependency, not an invalidity result. -/
def invalidForParent (p : Params) (st : State p.n) (N : NamedProposal p.n) : Bool :=
  if !namedParentHeld st N then false else
  match parentFG st N.erase with
  | none => false
  | some P => !rowsValidForParent p P N.slot N.rows

/-- [PC-SA M1] Permanent exclusions: a proposal conflicts with finality or fails R6
against a held parent; a HEAD is excluded by the base vote pool. Decoded rows,
acks and PCs are never excluded. An absent parent remains a dependency condition. -/
def excludesS (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) =>
      GridCO.excludes p.toParams.engine st.base (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n))
  | some (.row _ _) => false
  | some (.block _ N) => blockExcluded st N.erase || invalidForParent p st N
  | some (.ack _ _ _) => false
  | some (.pc _) => false
  | none => false

/-- [PC-SA M1; pcsa-decisions R-e] [spec 804–829; plan T7.2] Handler calls:
the delivered object itself; for a proposal that the store accepts
(`parentFG` and `blockAccepted`, the tests of `admitBlock`), also its carried
HEADs (the raw votes), its carried rows and the acks of its carried PC; for a
PC, its acks; as v2 objects (`ofHead`, `ofRow`, `ofAck`). -/
def handlesS (p : Params) (st : State p.n) (o o' : Obj p) : Prop :=
  o = o' ∨ match (toWire p o).decode with
    | some (.block s N) =>
        (namedParentHeld st N = true ∧ ∃ P, parentFG st N.erase = some P ∧
          blockAccepted p st s N P = true) ∧
          (o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.rows.map (ofRow p) ∨
            o' ∈ N.pcAcks.map (ofAck p))
    | some (.pc c) => o' ∈ c.acks.map (ofAck p)
    | _ => False

/-- [PC-SA M1; pcsa-decisions R-e] [spec 248–255; plan T7.2] Structural
containment: a proposal payload carries its raw HEADs, its support HEADs, its
rows and the acks of its PC; a PC payload carries its acks. -/
def carriesS (p : Params) (o o' : Obj p) : Prop :=
  match o.payload with
  | .proposal N =>
      o' ∈ N.raw.map (ofHead p) ∨ o' ∈ N.support.map (ofHead p) ∨ o' ∈ N.rows.map (ofRow p) ∨
        o' ∈ N.pcAcks.map (ofAck p)
  | .pc c => o' ∈ c.acks.map (ofAck p)
  | _ => False

/-! ### The protocol -/

/-- [PC-SA M1] [plan T7.2; FRAMEWORK E1, E2, E5, E6] PC-SA on engine v2, with the
application codec `c`.

* State: the store and Λ (`Node`). A restart keeps Λ (`Durable := RecordOnce`, the
  slashing-protection database; user decision, plan §1a) and restarts the
  store from `initial`, so the base after a restore does not depend on the
  kept data (E5 restore law).
* `clock` and `process` run the store functions and keep Λ; `recordOwn`
  writes only Λ (`recordRow?`).
* `act`: HEAD, proposal and ack from the store (`actS`), FG row from `attest`.
* The hooks are the store hooks (`depsS`, `processedS`, `excludesS`,
  `handlesS`) at `nd.st`. -/
def pcsa (p : Params) {In : Type} (c : AppCodec In) : V2.ProtocolSpecD In where
  State := Node p
  Label := RunLabel
  Duty := RunDuty
  signLabel := RunDuty.signLabel
  seats := RunLabel.seats p
  Payload := Msg p.n
  Durable := RecordOnce
  init := ⟨initial p.n, RecordOnce.initial⟩
  clock nd t := { nd with st := PCSA.clock p nd.st t }
  actTime := RunDuty.actTime p
  duties := duties p
  duties_spec := duties_spec p
  duties_nodup := duties_nodup p
  act := act p c
  gossip _ _ := []
  process nd o := { nd with st := PCSA.process p nd.st (toWire p o) }
  selfVisible := RunLabel.selfVisible
  recordOwn nd o := { nd with record := recordRow? p nd.record o }
  durable nd := nd.record
  restore d := ⟨initial p.n, d⟩
  wellFormed o := PCSA.wellFormed p (toWire p o)
  depsPresent nd o := depsS p nd.st o
  processed nd o := processedS p nd.st o
  excludes nd o := excludesS p nd.st o
  handles nd o o' := handlesS p nd.st o o'
  carries := carriesS p

/-- [PC-SA M1] Labels of `pcsa` have decidable equality (the instance of `RunLabel`; the
projection does not unfold at instance transparency). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (pcsa p c).Label :=
  inferInstanceAs (DecidableEq RunLabel)

/-- [PC-SA M1] Duties have decidable equality. -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (pcsa p c).Duty :=
  inferInstanceAs (DecidableEq RunDuty)

/-- [PC-SA M1] Payloads of `pcsa` have decidable equality (the instance of `Msg`). -/
instance (p : Params) {In : Type} (c : AppCodec In) : DecidableEq (pcsa p c).Payload :=
  inferInstanceAs (DecidableEq (Msg p.n))

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem ofAuth_eq_1_export :
    type_of% (@ofAuth.eq_1) := @ofAuth.eq_1
private theorem ofAuth_eq_2_export :
    type_of% (@ofAuth.eq_2) := @ofAuth.eq_2
private theorem ofAuth_eq_3_export :
    type_of% (@ofAuth.eq_3) := @ofAuth.eq_3
private theorem ofHead_eq_1_export :
    type_of% (@ofHead.eq_1) := @ofHead.eq_1
private theorem ofRow_eq_1_export :
    type_of% (@ofRow.eq_1) := @ofRow.eq_1
private theorem ofAck_eq_1_export :
    type_of% (@ofAck.eq_1) := @ofAck.eq_1
private theorem ofWire_eq_1_export :
    type_of% (@ofWire.eq_1) := @ofWire.eq_1
private theorem toAuth_eq_1_export :
    type_of% (@toAuth.eq_1) := @toAuth.eq_1
private theorem toAuth_eq_2_export :
    type_of% (@toAuth.eq_2) := @toAuth.eq_2
private theorem toAuth_eq_3_export :
    type_of% (@toAuth.eq_3) := @toAuth.eq_3
private theorem toWire_eq_1_export :
    type_of% (@toWire.eq_1) := @toWire.eq_1

end AvailableChain.PCSA.Run

end
