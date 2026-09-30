module
public import AvailableChainFGSARun.Proofs.Protocol
public import AvailableChainFGSARun.Proofs.Acceptance

@[expose] public section

/-! Smoke tests of the FG-SA protocol on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2): the duties at a
proposal, a vote and an action time; the FG payload and its record; the
application value of the proposal and `rowsOk`; the adapter round trips; the
row exclusion (old, future, full); a malformed wire; a proposal whose body does
not pack its rows. -/

namespace AvailableChain.FGSA.Run.Tests

open AvailableChain.SimplexFG

/-- The test parameters: Δ = 1, n = 1, k = 2, R = 2, w_F = 1, δ_t = 0. The
proposal times are `4s`, the vote times `4s + 1`, and the action time of round
`r` is `a_r = 8r + 6`. -/
abbrev p1 : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, wF := 1, δt := 0, RLarge := by decide, wFPos := by decide }

/-- The codec of a number input (plan §1a, the 2c I1 condition (iv)). -/
def natCodec : AppCodec Nat := ⟨id, some, fun _ => rfl⟩

abbrev P1 := fgsa p1 unitCodec
abbrev P1n := fgsa p1 natCodec

/-- The object of label `ℓ` with seat `0`, on a store label. -/
def baseObj (ℓ : Label) (m : Msg 1) : Obj p1 := ⟨.seat (.base ℓ) ⟨0, Nat.one_pos⟩, m⟩
/-- The object of the proposal duty of slot `s`. -/
def propObj (s : Slot) (m : Msg 1) : Obj p1 := ⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, m⟩

/-! ### Duties -/

/-- A proposal time, a vote time and two action times have their one label;
a time with no act time has none. -/
example : P1.duties 0 = [.prop 0] ∧
    P1.duties 4 = [.prop 1] ∧
    P1.duties 5 = [.base (.head 1)] ∧
    P1.duties 6 = [.base (.fg 0)] ∧
    P1.duties 14 = [.base (.fg 1)] ∧
    P1.duties 10 = [] ∧ P1.duties (-3) = [] := by
  decide +kernel

/-! ### The FG action and its record -/

/-- At the initial node, the FG payload is the `attest` body, and it is the
empty row (no source yet). -/
example : P1.act P1.init (.base (.fg 0)) () =
      some (.row (attest p1 (initial 1) Record.initial ⟨0, Nat.one_pos⟩).1) ∧
    P1.act P1.init (.base (.fg 0)) () = some (.row ⟨.empty, none⟩) := by
  decide +kernel

/-- The record of the emitted FG row is the `attest` record. -/
example (r : Nat) (i : Fin 1) :
    (P1.recordOwn P1.init ⟨.seat (.base (.fg r)) i,
        .row (attest p1 P1.init.st P1.init.record ⟨0, p1.nPos⟩).1⟩).record =
      (attest p1 P1.init.st P1.init.record ⟨0, p1.nPos⟩).2 :=
  recordOwn_attest (c := unitCodec) _ r i

/-- A row with a vote at height `3` records the target at height `3`; a HEAD
object records nothing. -/
example : (recordRow? p1 Record.initial
      (baseObj (.fg 0) (.row ⟨.vote 3 genesisRoot false, none⟩))).target 3 = some genesisRoot ∧
    (recordRow? p1 Record.initial (baseObj (.head 0) (.head .genesis))).target 3 = none := by
  decide +kernel

/-! ### The proposal -/

/-- The proposal of slot `1` at the initial node carries the input `5` in its
body; its block passes `rowsOk`, and the input decodes. With `unitCodec` the
application value is `0` (the I9 proposal). There is no proposal at slot `0`. -/
example : P1n.act P1n.init (.prop 1) 5 =
      some (.proposal (.node .genesis 1 (packBody 5 ([] : List (RowWire 1)))) [] [] []) ∧
    rowsOk (.node .genesis 1 (packBody 5 ([] : List (RowWire 1)))) ([] : List (RowWire 1)) ∧
    natCodec.unapp (appOf (Block.node .genesis 1 (packBody 5 ([] : List (RowWire 1)))).body) =
      some 5 ∧
    P1.act P1.init (.prop 1) () =
      some (.proposal (.node .genesis 1 (packBody 0 ([] : List (RowWire 1)))) [] [] []) ∧
    P1.act P1.init (.prop 0) () = none := by
  decide +kernel

/-- One signed row of round `0`. -/
def rws : List (RowWire 1) := [⟨.seat (.fg 0) 0, ⟨.vote 1 genesisRoot false, none⟩⟩]

/-- `withApp` on a block with one carried row: the rows stay, the application
value changes, and the block passes `rowsOk` with its rows. -/
example : withApp 7 (Msg.proposal (.node .genesis 1 (packBody 0 rws)) [] [] rws) =
      .proposal (.node .genesis 1 (packBody 7 rws)) [] [] rws ∧
    rowsOk (.node .genesis 1 (packBody 7 rws)) rws = true ∧
    appOf (Block.node .genesis 1 (packBody 7 rws)).body = 7 := by
  decide +kernel

/-! ### The adapter -/

/-- The adapter maps a store-label seat to its store seat, a proposal seat to
the proposer key, and an unsigned object to an unsigned wire; it round trips. -/
example : toWire p1 (baseObj (.head 2) (.head .genesis)) = ⟨.seat (.head 2) 0, .head .genesis⟩ ∧
    toWire p1 (propObj 3 (.head .genesis)) = ⟨.proposer 3, .head .genesis⟩ ∧
    toWire p1 ⟨.none, .row ⟨.empty, none⟩⟩ = ⟨.none, .row ⟨.empty, none⟩⟩ ∧
    ofWire p1 (toWire p1 (propObj 3 (.head .genesis))) = propObj 3 (.head .genesis) ∧
    ofWire p1 (toWire p1 (baseObj (.fg 4) (.row ⟨.empty, none⟩))) =
      baseObj (.fg 4) (.row ⟨.empty, none⟩) ∧
    toWire p1 (ofWire p1 ⟨.proposer 2, .row ⟨.empty, none⟩⟩) =
      ⟨.proposer 2, .row ⟨.empty, none⟩⟩ := by
  decide +kernel

/-! ### Row exclusion -/

/-- A store at time `40`: slot `10`, round `5`. -/
def st40 : State 1 := { initial 1 with base := { (initial 1).base with now := 40 } }

/-- A row of round `r` with a vote at height `h`. -/
def rowAt (r h : Nat) : Obj p1 := baseObj (.fg r) (.row ⟨.vote h genesisRoot false, none⟩)

/-- An old row (`1 + w_F < 5`) is refused and excluded; a future row (round `6`)
is refused and not excluded; a current row is admitted and not excluded. -/
example : excludesS p1 st40 (rowAt 1 1) = true ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 1 1))).rowPool = [] ∧
    excludesS p1 st40 (rowAt 6 1) = false ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 6 1))).rowPool = [] ∧
    excludesS p1 st40 (rowAt 5 1) = false ∧
    (FGSA.process p1 st40 (toWire p1 (rowAt 5 1))).rowPool.length = 1 := by
  decide +kernel

/-- The store after two rows of round `5` by seat `0`. -/
def st40' : State 1 :=
  FGSA.process p1 (FGSA.process p1 st40 (toWire p1 (rowAt 5 1))) (toWire p1 (rowAt 5 2))

/-- A third row of round `5` by the same seat is refused and excluded; a row in
the pool is processed and not excluded. -/
example : st40'.rowPool.length = 2 ∧ excludesS p1 st40' (rowAt 5 3) = true ∧
    (FGSA.process p1 st40' (toWire p1 (rowAt 5 3))).rowPool.length = 2 ∧
    processedS p1 st40' (rowAt 5 1) = true ∧ excludesS p1 st40' (rowAt 5 1) = false := by
  decide +kernel

/-! ### Malformed wires and the content check -/

/-- A row payload with a HEAD seat decodes to `none`: it is not well-formed,
not processed and not excluded, and it has no dependency. -/
example : (toWire p1 (baseObj (.head 0) (.row ⟨.empty, none⟩))).decode = none ∧
    P1.wellFormed (baseObj (.head 0) (.row ⟨.empty, none⟩)) = false ∧
    P1.processed P1.init (baseObj (.head 0) (.row ⟨.empty, none⟩)) = false ∧
    P1.excludes P1.init (baseObj (.head 0) (.row ⟨.empty, none⟩)) = false ∧
    P1.depsPresent P1.init (baseObj (.head 0) (.row ⟨.empty, none⟩)) = true := by
  decide +kernel

/-- A proposal whose body is not the packing of its rows (`rowsOk = false`) is
not well-formed; with the packed body it is. -/
example : P1.wellFormed (propObj 1 (.proposal (.node .genesis 1 99) [] [] [])) = false ∧
    P1.wellFormed (propObj 1 (.proposal (.node .genesis 1 (packBody 0 ([] : List (RowWire 1))))
      [] [] [])) = true := by
  decide +kernel

-- Acceptance controls (plan T7.7).

open AvailableChain.SimplexFG

private def t77Rows : List (RowWire 1) :=
  [⟨.seat (.fg 0) 0, ⟨.empty, none⟩⟩,
   ⟨.seat (.fg 0) 0, ⟨.vote 1 genesisRoot false, none⟩⟩,
   ⟨.seat (.fg 0) 0, ⟨.vote 2 genesisRoot false, none⟩⟩]

private def t77Envelope : Obj p1 :=
  propObj 1 (.proposal (.node .genesis 1 (packBody 0 t77Rows)) [] [] t77Rows)

private def t77Third : Obj p1 :=
  baseObj (.fg 0) (.row ⟨.vote 2 genesisRoot false, none⟩)

private def t77Pre : Node p1 := P1.clock P1.init 4

/-- The third row is ready at the pre-state. The cap reached inside the
proposal delivery excludes it at the post-state. -/
theorem fgsa_carried_row_cap_control :
    let rows : List (RowWire 1) :=
      [⟨.seat (.fg 0) 0, ⟨.empty, none⟩⟩,
       ⟨.seat (.fg 0) 0, ⟨.vote 1 genesisRoot false, none⟩⟩,
       ⟨.seat (.fg 0) 0, ⟨.vote 2 genesisRoot false, none⟩⟩]
    let envelope := propObj 1 (.proposal (.node .genesis 1 (packBody 0 rows)) [] [] rows)
    let third := baseObj (.fg 0) (.row ⟨.vote 2 genesisRoot false, none⟩)
    let pre := P1.clock P1.init 4
    P1.wellFormed envelope = true ∧
      P1.excludes pre third = false ∧
      P1.processed (P1.process pre envelope) third = false ∧
      P1.excludes (P1.process pre envelope) third = true := by
  decide +kernel

/-- The capped third row is still a handled child. -/
example : P1.handles t77Pre t77Envelope t77Third := by
  change handlesS p1 t77Pre.st t77Envelope t77Third
  right
  change (∃ P, parentFG t77Pre.st _ = some P ∧
    blockAccepted p1 t77Pre.st 1 _ P t77Rows = true) ∧
      (t77Third ∈ [].map (ofHead p1) ∨ t77Third ∈ t77Rows.map (ofRow p1))
  constructor
  · exact ⟨.genesis, by decide +kernel, by decide +kernel⟩
  · right
    decide +kernel

/-- A slot-zero HEAD can be admitted before the honest vote time of 1. Its
admission threshold is zero. -/
example :
    P1.processed (P1.process P1.init (baseObj (.head 0) (.head .genesis)))
      (baseObj (.head 0) (.head .genesis)) = true ∧
    fgsaTimely p1 P1.init (baseObj (.head 0) (.head .genesis)) := by
  unfold fgsaTimely
  decide +kernel

/-- A negative store clock shows why AdmitSound requires a nonnegative clock. -/
example :
    let nd : Node p1 := ⟨{ initial 1 with base.now := -1 }, Record.initial⟩
    P1.processed (P1.process nd (baseObj (.head 0) (.head .genesis)))
      (baseObj (.head 0) (.head .genesis)) = true ∧
    ¬ fgsaTimely p1 nd (baseObj (.head 0) (.head .genesis)) := by
  unfold fgsaTimely
  decide +kernel

end AvailableChain.FGSA.Run.Tests

end
