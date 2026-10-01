module
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Slashing
public import AvailableChainSimplexFG.Evidence

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- DC `DecoupledConsensusModel/Protocol/Evidence.lean:67–68` defines
`store_attestations st := st.T.biUnion chain_attestations`: the rows carried
in stored block chains. This accessor uses the same set in FG-SA:
`nd.st.fg.TF` is the cumulative admitted tree, and `chainRows` reads its rows.
TS `spec/fgsa-protocol.tex:493–500` maps that tree to DC's `Σ.T`.
The row pool (`Σ.attestations`, spec:573–580) is not part of this set.
FG blocks already carry decoded `SimplexFG.Row` values; this accessor has no
wire decoder and drops no stored row. FG-SA admission decodes signed rows
with `RowWire.toRow?`; a wire that fails to decode is not an FG row.
DC carries `CombinedAttestation` values; FG-SA carries FG rows only. -/
def fgsaEvidence {p : Params} (nd : Node p) : Finset (SimplexFG.Row (Fin p.n)) :=
  nd.st.fg.TF.biUnion SimplexFG.chainRows

/-- DC `DecoupledConsensusStatements/Instantiation.lean:76–80`: two inclusive
time reads, at any nodes, hold slashable evidence for a seat index `i`, and `v`
holds seat `i` in every FG round.
V2 `readAt` needs `E` because the run does not contain its environment;
DC reads capture their environment through `S`. The two nodes need not be
honest, and the nodes and times can be equal.

Class INTENTIONAL (lead F-H ruling, TS `codex/reports/dc-align-full.md:135–141`,
and lead ruling 2026-10-01). DC attributes a row to its signer. An FG row
carries the seat index, not the round (FGSA `Model/Objects.lean:94–97`), and
the holder of a seat can depend on the round. The holder is attributed only
when it is round-independent. So no validator is attributed evidence for a
seat that it does not hold. Under `Linked` one bijection `e` holds every FG
round (`fgsa_linked_seats`), and the attribution is DC's at `e.symm v`
(`fgsaSlashing_slashes_iff_of_seats`). Without `Linked`, decoded rows cannot
name a round, so a round-varying holder is not attributed.

Alternative (not taken; reopen it for a claim without `Linked`): read the
signed rows (`RowWire`, auth `.seat (.fg r) i`) of the admitted proposals in
`nd.st.proposals` and attribute each row to `holder rho a.auth`. This needs a
lemma that their decoded rows are this evidence set. SimplexFG `on_block`
(`Store.lean:70–73`) and FG-SA `blockAccepted` (`Handlers.lean:38–45`) test
the same four conditions, but that lemma is not proved. -/
def fgsaSlashing (p : Params) {In : Type} (c : AppCodec In)
    (E : Generic.Env (Fin p.n)) : Gen.V2.SlashingInterface (V := Fin p.n) (fgsa p c) where
  toInterface := fgsaInterface p c
  finalized := finalizedOut
  slashes rho v := ∃ (u u' : Fin p.n) (t t' : Time) (i : Fin p.n),
    SimplexFG.SlashableBetween
      (fgsaEvidence (V2.Run.readAt E rho t u))
      (fgsaEvidence (V2.Run.readAt E rho t' u')) i ∧
    ∀ r, rho.seatOf (.base (.fg r)) i = v

end AvailableChain.FGSA.Run
