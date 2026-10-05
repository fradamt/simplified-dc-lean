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
and `NamedRootCollisionFree` do not see a row delivery. Scope: `hkey` restricts the run to
events at or before `(t, 2)`, so the run ends at the action time `t`; `Base₂.ownRow_run`
removes the restriction through the cut. -/
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

/-- [own-row Option 1; DC N3] `Base₂` survives the cut after the ticks at `t` (horizon `t`):
`executionValid_cut`, the committee fields, `noRestart_cut` and
`namedRootCollisionFree_cut`. -/
theorem Base₂.cutAt (h : Base₂ p c E rho) {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) :
    Base₂ p c E ({ rho with events := rho.events.take n, horizon := t }) where
  valid := by
    obtain ⟨ht0, hth⟩ := h.valid.in_horizon _ (List.mem_of_getElem? hi)
    exact executionValid_cut h.valid hcut ht0 hth
  linked := h.linked
  cstar := h.cstar
  noRestart := noRestart_cut h.noRestart
  delta := h.delta
  idealization := namedRootCollisionFree_cut h.idealization

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary `Base₂` run: cut after the
ticks at the action time `t`, then the same-time self-delivery of the row released by the
tick of `v` at `t`. It is a `Base₂` run. -/
theorem Base₂.ownRow_run (h : Base₂ p c E rho) {n i : Nat} {v : V} {t : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    Base₂ p c E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) := by
  have hin : i < n := (hcut i _ hi).mpr (tick_key_le.mpr le_rfl)
  exact (h.cutAt hcut hi).snoc_ownRow (cut_key_le hcut) (getElem?_cut_iff.mpr ⟨hin, hi⟩)
    (cut_lastEvent h.valid.toScheduleWellFormed hcut hi) (by rw [emitsAt_cut_of_lt hin]; exact ho)

/-- [own-row Option 1; DC N3] The cut index exists for every `Base₂` run (`exists_cut` on
the sorted schedule), so every FG row released in a `Base₂` run has its spec-like run. -/
theorem Base₂.ownRow_run_exists (h : Base₂ p c E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    ∃ n, (∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1))) ∧
      Base₂ p c E
        ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                    horizon := t }) := by
  obtain ⟨n, hcut⟩ := exists_cut h.valid.sorted (toLex (t, 1))
  exact ⟨n, hcut, h.ownRow_run hcut hi ho⟩

end AvailableChain.FGSA.Run

end
