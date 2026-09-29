module
public import AvailableChainFGSA.Model.Store

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [spec 831–842] `on_goldfish_vote`: SA's vote pool, unchanged. -/
def admitHead (p : Params) (st : State p.n) (s : Slot) (i : Fin p.n) (b : Block) : State p.n :=
  { st with base := GridCO.admitVote p.toParams.engine st.base ⟨.seat s i, .head b⟩ }

/-- [spec 433–439, 844–857] `on_attestation`: a row of round `r` enters the pool
if `r` is in the window `[max 0 (r_now − w_F), r_now]`, it is not already
there, and its identity has fewer than two rows of round `r`. -/
def admitRow (p : Params) (st : State p.n) (a : RowWire p.n) : State p.n :=
  match a.decode? with
  | some (r, i, _) =>
      let now := p.round (st.slot p)
      let mine := st.rowPool.filter (fun c => c.decode?.map (fun x => (x.1, x.2.1)) == some (r, i))
      if r + p.wF < now || now < r || decide (a ∈ mine) || 2 ≤ mine.length then st
      else { st with rowPool := st.rowPool ++ [a] }
  | none => st

/-- [spec 519–522; M3] The stored FG parent of an erased block. `pickPair`
returns `none` on two candidates; Task 10 shows there is at most one. -/
def parentFG {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun P => decide (eraseFG P = b.parent))

/-- [spec 818–819, 902–912; M3; D9] The FG block of an admitted proposal: the
stored parent, the slot of the wire block, the inner packed value of its
application value and signed rows, and the decoded rows. Under `rowsOk` its
erasure is the wire block (`eraseFG_fgBlock`). -/
def fgBlock {n : Nat} (P : FGBlock (Fin n)) (b : Block) (rows : List (RowWire n)) :
    FGBlock (Fin n) :=
  .node P b.slot (packInner (appOf b.body) rows) (rows.filterMap RowWire.toRow?)

/-- [spec 530–536, 806–817; M5, DQ2, DQ12, DQ14; D9] The acceptance tests of
`on_block`, all before any write: not genesis; `b.slot ≤ Σ.s`; no stored block
has the root of `b` (the duplicate test); `F ⪯ B`; `b.parent.slot < b.slot`;
the slot-`b.slot` proposer signs it; every row decodes as a row with round
`≤ round(b.slot)`; the body packs the carried rows (`rowsOk`, the same check as
in `wellFormed`). The parent test is `parentFG st b = some P`. -/
def blockAccepted (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (P : FGBlock (Fin p.n)) (rows : List (RowWire p.n)) : Bool :=
  b != .genesis && decide (b.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = b.root) &&
    FGBlock.preceq st.fg.F (fgBlock P b rows) &&
    decide (b.parent.slot < b.slot) && s == b.slot &&
    rows.all (fun a => match a.decode? with
      | some (r, _, _) => decide (r ≤ p.round b.slot)
      | none => false) &&
    rowsOk b rows

/-- [spec 804–829; M6] `on_block`. On refusal the state does not change. On
acceptance: the SA block admission and the carried votes (SA code on the
cumulative base, with the erased block); the FG admission (`on_block` of the FG
module: insert, then `update_finality`); the proposal wire is stored; if F
moved, `reconcile`; then the carried rows pass `admitRow`. The FG acceptance
decides; if the base admission then refused the block, the state would diverge
(a block in Σ.T but not in the base list); `base_admitProposal_accepts`
(Task 10) excludes this under the store invariant. -/
def admitBlock (p : Params) (st : State p.n) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) : State p.n :=
  match parentFG st b with
  | none => st
  | some P =>
      if blockAccepted p st s b P rows then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s b raw support) b (raw.map baseHead)
          fg := on_block p.E p.cfg st.fg (fgBlock P b rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal b raw support rows⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        rows.foldl (admitRow p) st2
      else st

/-- [spec 804–857] The delivery handler. It reads the wire only through
`Wire.decode` (J1). It does not run the input check (DQ14). -/
def process (p : Params) (st : State p.n) (o : Wire p.n) : State p.n :=
  match o.decode with
  | some (.vote s i b) => admitHead p st s i b
  | some (.row _ _ body) => admitRow p st ⟨o.auth, body⟩
  | some (.block s b raw support rows) => admitBlock p st s b raw support rows
  | none => st

/-- [spec 247–255, 505–518; M12, DQ9, DQ14] The input check, as a pure function
(T7 binds it). A vote: a HEAD seat. A row: an FG seat and a valid body. A block:
not genesis; the proposer key of its slot; every carried vote a HEAD seat of
slot `b.slot − 1`; support ⊆ votes; every carried row passes the SAME row check
(`RowWire.valid`). The flat wire carries the parent slot and the row rounds, so
the check also has `b.parent.slot < b.slot` and `round ≤ round(b.slot)` (DQ14;
`blockAccepted` keeps both, in the spec's place). The body packs the carried
rows (`rowsOk`, D9): a content check, the same one as in `blockAccepted`. -/
def wellFormed (p : Params) (o : Wire p.n) : Bool :=
  match o.decode with
  | some (.vote _ _ _) => true
  | some (.row _ _ body) => body.valid
  | some (.block s b raw support rows) =>
      b != .genesis && s == b.slot && decide (b.parent.slot < b.slot) &&
        raw.all (fun v => match v.decode? with
          | some (r, _, _) => r + 1 == b.slot
          | none => false) &&
        support.all (fun v => decide (v ∈ raw)) &&
        rows.all (fun a => a.valid && match a.decode? with
          | some (r, _, _) => decide (r ≤ p.round b.slot)
          | none => false) &&
        rowsOk b rows
  | none => false

end AvailableChain.FGSA
end
