module
public import AvailableChainFGSAProofs.Proofs.Healing.Phase -- shake: keep (phase boundary tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay -- shake: keep (strict relay tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle -- shake: keep (RPhase tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseBoot -- shake: keep (bootstrap tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (foundation producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (foundation producer)

set_option linter.privateModule false

/-!
H-PHASE coverage (plan S20, r1 and r2, 2026-10-02):

* P1: `healing_phase_order`, the first frozen RPhase clause.
* P2: `healing_evidence_spread`, the second frozen clause, and
  `healing_phase_rows_spread`, the common row cut from HB4.
* P3: `healing_settle_event`, the third frozen clause. Its statement is the
  clause text. `healing_phase_held_receipt` relays every carrier held at the
  event prefix by max(t, GST) + Δ, so carriers accepted before GST are covered.
  `healing_phase_window` fixes the frontier and both evidence bits until the
  next effective event. `healing_phase_top_node` gives h_j + 1 = m and fixes
  the local J on a relayed top carrier. The common top J then follows from the
  global absence of contest evidence. No fault bound is an input.
* P4: `healing_settled_frame`, the fourth frozen clause.
* P5: `healing_frontier_mem`, the fifth frozen clause.
* P6: `healing_rPhase`, all five clauses as `RPhase` with no new premise.
* P7: `HealingPhaseWitness` and `healing_phaseWitness`. The record contains
  actual held carriers for frontier, top-J, and contest evidence.

Bootstrap (r2, partial). `healing_phase_initial_frontier` gives frontier one
at prefix zero. `healing_phase_height_one` gives the genesis top-J frame at
frontier one. `healing_phase_first_rise` locates the first rise to height two
as an effective event, if a later prefix has frontier at least two.
`healing_attemptValid_of_event` starts a raise attempt from an effective event
after GST at frontier at least two. Still open: a producer that the rise
occurs, that is, actual height-one ExactService and the first rise after GST.
The frozen service contracts read PhaseInterval, which requires 2 ≤ m, so no
frozen route reaches m = 1. A first rise before GST is not an AttemptValid
start; the inclusive-cut alternative then applies only if the frontier is at
least two at that cut. No M ≥ 2 premise is asserted here.

Foundation inputs cross the lane boundary as hypotheses. RMono comes from
`fgsa_rMono`; RXing comes from `fgsa_apiFinalLockClaim_body`; TRowsReceipt
comes from `fgsa_tRowsReceipt` through HB4. Assembly discharges these inputs.
The Healing modules import no Foundations proof. They use neither HB1 nor TDel.
P1 also takes NoRestart. P2, P3, and the held relay take ExecutionValid,
NoRestart, E.Δ = p.Δ, and PartialSynchronyBy with fgsaDelay. P6 takes the
union of the P1–P5 inputs. The row companion takes ScheduleWellFormed,
NoRestart, TRowsReceipt, GST/horizon bounds, and actual emissions by its cut.
P4 and P5 take RXing and their frozen clause antecedents. P7 takes m >= 2 and
the actual frontier equality. The initial-frontier and first-rise lemmas take
honest.Nonempty.

All public theorems are in Tests/Axioms. Each print reports exactly
`[propext, Classical.choice, Quot.sound]`. The structural helpers take only
their displayed membership, certificate, height, honesty, and index facts;
the persistence helpers take RMono and NoRestart; the root helper takes RXing.
-/

section
namespace AvailableChain.FGSA.Run.Tests.HealingPhase
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- The first clause has the frozen quantifiers and uses the existing RMono producer.
example (hnr : V2.D.NoRestart rho) (a b m : Nat)
    (hab : a ≤ b) (hb : b ≤ rho.events.length) (hm : 2 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence p c E rho i m → TopEvidence p c E rho i m) :=
  healing_phase_order p c E rho (fgsa_rMono p c E rho) hnr a b m hab hb hm hfixed

-- The settled-frame proof uses the accepted certificate form of final lock.
example [Fintype V] (hp : FinalizedSafetyPrem p c E rho ())
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested :=
  healing_settled_frame p c E rho (fgsa_apiFinalLockClaim_body p c E rho () hp)
    u v m J contested hgst hphase i x hui hiv hx

-- The witness producer has no phase or service premise.
example {i m : Nat} (hm : 2 ≤ m) (hf : frontierAtIdx p c E rho i = m) :
    HealingPhaseWitness p c E rho i m := healing_phaseWitness p c E rho hm hf

-- Genesis is a real height-one frontier. It cannot enter AttemptValid directly.
example (hne : rho.honest.Nonempty) : frontierAtIdx p c E rho 0 = 1 :=
  healing_phase_initial_frontier p c E rho hne

example {k : AttemptKey} (hk : k.frontier = 1) : ¬ AttemptValid p c E rho k := by
  rintro ⟨ev, _, _, _, _, hm, _⟩
  omega

-- Receipt at the exact deadline is excluded from the strict prefix used by P2.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro hl
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp hl)

-- P6: the frozen contract from the foundation producers and the regime fields.
example [Fintype V] (hp : FinalizedSafetyPrem p c E rho ())
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF)) :
    RPhase p c E rho :=
  healing_rPhase p c E rho (fgsa_rMono p c E rho)
    (fgsa_apiFinalLockClaim_body p c E rho () hp) hvalid hnr hdelta hsync

-- At frontier one the live root is genesis.
example {i : Nat} {x : V} (hx : x ∈ rho.honest) (hf : frontierAtIdx p c E rho i = 1) :
    (R_at p c E rho i x).Z = .genesis := by
  obtain ⟨_, _, hJ, _, hr⟩ := healing_phase_height_one p c E rho hx hf
  change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
  rw [hr]
  exact hJ

-- If the first rise is after GST, it starts a valid attempt at frontier two or more.
example (hne : rho.honest.Nonempty) {n : Nat} (hn : 2 ≤ frontierAtIdx p c E rho n)
    (hlen : n ≤ rho.events.length)
    (hgst : ∀ (i : Nat) ev, rho.events[i]? = some ev → E.t_GST ≤ ev.time) :
    ∃ k, AttemptValid p c E rho k := by
  obtain ⟨i, hin, _, h2, heff⟩ := healing_phase_first_rise p c E rho hne hn
  have hev : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨k, -, -, -, hk⟩ :=
    healing_attemptValid_of_event p c E rho hev (hgst i _ hev) heff h2
  exact ⟨k, hk⟩

end AvailableChain.FGSA.Run.Tests.HealingPhase
end
