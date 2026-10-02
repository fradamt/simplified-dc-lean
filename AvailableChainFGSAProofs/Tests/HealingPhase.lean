module
public import AvailableChainFGSAProofs.Proofs.Healing.Phase -- shake: keep (phase boundary tests)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay -- shake: keep (strict relay tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Store -- shake: keep (foundation producer)
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalityApi -- shake: keep (foundation producer)

set_option linter.privateModule false

/-!
H-PHASE coverage (plan S20, 2026-10-02):

* P1: `healing_phase_order`, the first frozen RPhase clause.
* P2: `healing_evidence_spread`, the second frozen clause, and
  `healing_phase_rows_spread`, the common row cut from HB4.
* P4: `healing_settled_frame`, the fourth frozen clause.
* P5: `healing_frontier_mem`, the fifth frozen clause.
* P7: `HealingPhaseWitness` and `healing_phaseWitness`. The record contains
  actual held carriers for frontier, top-J, and contest evidence.

P3 remains open. Under the exact event, GST, horizon, phase, and no-later-event
hypotheses of RPhase clause 3 (ComposeStmt:472–483), produce one J and both
`PhaseInterval (ev.time + 3 * p.Δ) v m root contested` and the HEAD frames.
The unresolved step is common top-J identity and common live controls across
all receivers throughout that interval, including carriers accepted before GST.
For held C and D with equal positive top justification height, the needed
identity is `(heightView p C).J = (heightView p D).J`. The local phase-order
proof does not supply it: it permits the cached J to change at the same height.
No new hypothesis for this step was added. P6 is omitted until P3 is proved.

Bootstrap remains open. `healing_phase_initial_frontier` proves that the
initial frontier is one for a nonempty honest set. The missing producer must
give actual height-one ExactService and the first effective frontier rise,
then construct the height-at-least-two AttemptValid input. No M >= 2 premise
or height-one AttemptValid witness is asserted here.

Foundation inputs cross the lane boundary as hypotheses. RMono comes from
`fgsa_rMono`; RXing comes from `fgsa_apiFinalLockClaim_body`; TRowsReceipt
comes from `fgsa_tRowsReceipt` through HB4. Assembly discharges these inputs.
The Healing modules import no Foundations proof. They use neither HB1 nor TDel.
P1 also takes NoRestart. P2 takes ExecutionValid, NoRestart, E.Δ = p.Δ, and
PartialSynchronyBy with fgsaDelay. The row companion takes ScheduleWellFormed,
NoRestart, TRowsReceipt, GST/horizon bounds, and actual emissions by its cut.
P4 and P5 take RXing and their frozen clause antecedents. P7 takes m >= 2 and
the actual frontier equality. The initial-frontier lemma takes honest.Nonempty.

All 17 public theorems are in Tests/Axioms. Each print reports exactly
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

-- Genesis is a real height-one frontier. Since ruling B21, AttemptValid admits frontier 1
-- (H.10 at m = 1, 21:1467–1468, 2570–2571).
example (hne : rho.honest.Nonempty) : frontierAtIdx p c E rho 0 = 1 :=
  healing_phase_initial_frontier p c E rho hne

-- Receipt at the exact deadline is excluded from the strict prefix used by P2.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro hl
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp hl)

end AvailableChain.FGSA.Run.Tests.HealingPhase
end
