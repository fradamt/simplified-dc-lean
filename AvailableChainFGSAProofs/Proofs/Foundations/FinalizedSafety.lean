module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAClaims.Statements.Packages.Safety

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

set_option linter.unusedVariables false in
/-- Finalized safety through the all-run FGSASlashableBound.
DC DecoupledConsensusInternal/Legacy/Definitions/FinalitySafety.lean:83
(WholeRunFinalitySafety); stored non-genesis blocks are run blocks.
The frozen hx and hy binders are unused: reachable stores at any node suffice.
Local F only extends by fgsa_rMono under NoRestart. -/
theorem fgsa_finalizedSafety (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {Pt : Type} {pt : Pt} (hp : FinalizedSafetyPrem p c E rho pt)
    (e e' : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest) :
    FGBlock.compatible (storeAt p c E rho e x).fg.F
      (storeAt p c E rho e' y).fg.F = true := by
  exact fgsa_eventPrefixAgreement_of_bound p c E rho
    (fgsa_slashableBound_of_base p c E rho hp.set hp.fault) e e' x y

private theorem finality_filter_prefix {α : Type} {R : α → α → Prop} {q : α → Bool}
    (hd : ∀ a b, R a b → q b = true → q a = true)
    (xs : List α) (hs : xs.Pairwise R) : xs.filter q = xs.takeWhile q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
      by_cases hq : q a = true
      · rw [List.filter_cons_of_pos hq, List.takeWhile_cons_of_pos hq, ih hs]
      · rw [List.filter_cons_of_neg hq, List.takeWhile_cons_of_neg hq]
        exact List.filter_eq_nil_iff.mpr (fun b hb hqb => hq (hd a b (ha b hb) hqb))

/-- DC DecoupledConsensusStatements/Generic/Claims.lean:61 (finalizedMonotone),
from DecoupledConsensusProofs/Protocol/Handlers/FinalityMonotoneCore.lean:277
(stateBefore_F_mono). Sorted inclusive time reads inherit event-prefix order.
Motivated divergence: FG-SA restore resets F to genesis, so NoRestart is required;
DC's world events have no restart constructor. No fault or signature premise. -/
theorem fgsa_finalizedMonotone (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  have hr (t : Time) : V2.D.Run.readAt E rho t = V2.D.Run.stateBefore E rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    have hf := finality_filter_prefix (q := fun e => decide (e.time ≤ t))
      (fun a b hk hb => decide_eq_true
        (le_trans (V2.D.Engine.time_le_of_key_le a b hk) (of_decide_eq_true hb))) rho.events hs
    have hp : (rho.events.filter (fun e => decide (e.time ≤ t))).IsPrefix rho.events := by
      rw [hf]
      exact List.takeWhile_prefix _
    exact congrArg (fun es => es.foldl (V2.D.World.step E rho) V2.D.World.init)
      (List.prefix_iff_eq_take.mp hp)
  intro x hx t t' htt
  rw [hr t, hr t']
  exact eraseFG_preceq
    (fgsa_rMono p c E rho hnr _ _ x hx (V2.D.Engine.read_length_mono t t' htt)).1

end AvailableChain.FGSA.Run
end
