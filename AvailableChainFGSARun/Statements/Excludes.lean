module
public import Mathlib.Logic.Relation
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

/-! The epoch of a store and the clock-free exclusions (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2; lead input
`excludes_inert`, 2026-09-29).

A restart restarts the store from `initial` (`fgsa`, `restore`), so an
exclusion holds only inside one restart epoch of a node. Inside an epoch the
store changes only by deliveries (`FGSA.process`) and ticks (`FGSA.clock`;
the own record does not change the store). `Epoch p true` also asks that no
tick moves the store clock back; the old-label exclusions of HEADs and rows
need this. The other exclusions (`excludesFixed`) hold on `Epoch p false`,
with any clock steps. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- One store step inside a restart epoch: a delivery of any store wire, or a
tick. With `mono = true`, a tick does not move the store clock back. -/
inductive EpochStep (p : Params) (mono : Bool) : State p.n → State p.n → Prop
  | deliver (st : State p.n) (w : Wire p.n) : EpochStep p mono st (FGSA.process p st w)
  | clock (st : State p.n) (t : Time) (ht : mono = true → st.base.now ≤ t) :
      EpochStep p mono st (FGSA.clock p st t)

/-- A part of a restart epoch: a finite sequence of epoch steps from `st` to
`st'`. -/
abbrev Epoch (p : Params) (mono : Bool) : State p.n → State p.n → Prop :=
  Relation.ReflTransGen (EpochStep p mono)

/-- The exclusions that do not read the clock: a proposal whose block is not
compatible with F; a HEAD that is not stored and whose seat equivocates at its
label; a row that is not in the pool and whose seat has two rows of its round
in the pool. Each one implies `excludesS` (`excludesFixed_excludesS`). -/
def excludesFixed (p : Params) (st : State p.n) (o : Obj p) : Bool :=
  match (toWire p o).decode with
  | some (.vote s i b) =>
      !decide (baseVote (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ st.base.votes) &&
        GridCO.equivocates (GridCO.votesAt st.base s) i
  | some (.row r i body) =>
      !decide ((⟨.seat (.fg r) i, body⟩ : RowWire p.n) ∈ st.rowPool) && decide (2 ≤ rowCount st r i)
  | some (.block _ b _ _ _) => blockExcluded st b
  | none => false

end AvailableChain.FGSA.Run

end
