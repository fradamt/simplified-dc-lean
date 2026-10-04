module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle -- shake: keep (RPhase tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot -- shake: keep (bootstrap tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (foundation producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi
-- shake: keep (foundation producer)

set_option linter.privateModule false

/-!
H-PHASE r2 coverage (plan S20, 2026-10-02). The r1 handoff stays in
Tests/HealingPhase.lean.

* P3: `healing_settle_event`, the third frozen RPhase clause. Its two
  `match kind` terms list all three kinds; the frozen text uses a wildcard.
  The checker rejects a sparse matcher that a theorem owns.
  `healing_phase_held_receipt` relays every carrier held at the event prefix
  by max(t, GST) + Δ, so carriers accepted before GST are covered.
  `healing_phase_window` fixes the frontier and both evidence bits until the
  next effective event. `healing_phase_top_node` gives h_j + 1 = m and fixes
  the local J on a relayed top carrier. The common top J follows from the
  global absence of contest evidence. No fault bound is an input (B20 permits
  `FinalitySlashableBound`; it is not used).
* P6: `healing_rPhase`, the exact `RPhase`, with no new premise.
* Bootstrap (B21). Private m = 1 lemmas in PhaseBoot: `boot_height_one`
  (H = 1, j = 0, J = genesis, no contest, rootIsJ, lo = 0), `boot_phase_one`
  (the m = 1 PhaseInterval with root `some genesis`, from the strict cut), and
  `boot_not_effective_one` (clause 3 is vacuous at m = 1). Public:
  `healing_phase_first_rise` locates the first rise to height two;
  `healing_attemptValid_of_event` starts a raise attempt from an effective
  event after GST.

Merge onto the freeze line (B21 1 ≤ m, B25 strict lower cut):
* `healing_phase_entries_eq` has no h_j ≠ 0 premise: at h_j = 0 both J are
  genesis. Thus `healing_phase_contest_persist` and `healing_phase_top_node`
  have no bound on m, and RPhase clause 1 holds at m = 1.
* `healing_settle_event` and `healing_rPhase` take 1 ≤ m. The settled
  controls hold from the strict cut at ev.time + Δ, which is at or before
  the strict cut at ev.time + 3Δ.
* No remaining proof uses 2 ≤ m.

Foundation inputs are hypotheses: RMono from `fgsa_rMono`, RXing from
`fgsa_apiFinalLockClaim_body`. The other inputs are ExecutionValid,
NoRestart, E.Δ = p.Δ (Base₂), and PartialSynchronyBy (Recovery₂.sync).
-/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPhaseSettle
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

-- P6: the frozen contract from the foundation producers and the regime fields.
example [Fintype V] (hp : FinalizedSafetyPrem p c E rho ())
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)) :
    RPhase p c E rho :=
  healing_rPhase (hroots := hroots) p c E rho (fgsa_rMono p c E rho)
    (fgsa_apiFinalLockClaim_body p c E rho () hp) hvalid hnr hdelta hsync

-- An event at the deadline is not before the strict relay cut, but it is inside
-- the inclusive cut.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) :
    ¬ i < V2.D.Run.idxBefore rho d ∧ i < timeIdx rho d :=
  ⟨fun hl => (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp hl),
    healing_phase_lt_timeIdx p c E rho hs hi le_rfl⟩

-- If the first rise is after GST, it starts a valid attempt at frontier two or more.
example (hne : rho.honest.Nonempty) {n : Nat} (hn : 2 ≤ frontierAtIdx p c E rho n)
    (hlen : n ≤ rho.events.length)
    (hgst : ∀ (i : Nat) ev, rho.events[i]? = some ev → E.t_GST ≤ ev.time) :
    ∃ k, AttemptValid p c E rho k := by
  obtain ⟨i, hin, _, h2, heff⟩ := healing_phase_first_rise p c E rho hne hn
  have hev : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨k, -, -, -, hk⟩ :=
    healing_attemptValid_of_event p c E rho hev (hgst i _ hev) heff (by omega)
  exact ⟨k, hk⟩

end AvailableChain.FGSA.Run.Tests.HealingPhaseSettle
end
