module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSARun.Proofs.SelfDelivery

/-! Own-row analysis, Option 1: the base regime survives the same-time self-delivery of a
released FG row. With `AvailableChainFGSARun.Proofs.SelfDelivery`, this records that a run
in which the sender processes its own row at the action time (the specification's
`on_tick` followed by `on_attestation`) is a valid run under `Base₂`, and that the
per-object delivery premises of the other regimes survive the append. -/

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [own-row Option 1; DC N3] `Base₂` survives the same-time self-delivery of a released FG
row, appended after the last event of the sender. `valid` is the engine append law with
`EmitOk` from `fgsa_emitOk_row`; the committee fields read only `seatOf`; `NoRestart`
and `NamedRootCollisionFree` do not see a row delivery. -/
theorem Base₂.snoc_ownRow (h : Base₂ p c E rho) {i : Nat} {v : V} {t : Time}
    (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Base₂ p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t] }) where
  valid := executionValid_snoc_selfDelivery h.valid hkey hi hlast ho
  linked := h.linked
  cstar := h.cstar
  noRestart := noRestart_snoc_deliver h.noRestart
  delta := h.delta
  idealization := namedRootCollisionFree_snoc_row h.idealization

end AvailableChain.FGSA.Run

end
