module
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport
public import AvailableChainFGSAProofs.Proofs.Finality.Rows -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge

set_option linter.privateModule false

public section

namespace AvailableChain.FGSA.Run.Tests.P0a
open AvailableChain.SimplexFG AvailableChain.FGCompose

private theorem tree_restore (p : Params) {In : Type} (c : AppCodec In) :
    FGTreeRestoreLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [fgsaCoreReads_def]
  exact congrArg (fun st => st.TF) (acRestart_fg p nd.st t)

private theorem tree_keep (p : Params) {In : Type} (c : AppCodec In) :
    FGTreeKeepLaws (fgsaCoreReads p c) := by
  constructor
  intro nd t
  rw [(tree_restore p c).restart_eq]

private theorem fgsa_retained_tree (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) {i j : Nat} (hij : i ≤ j) (x : V) :
    (V2.D.Run.stateBefore E rho i x).st.fg.TF ⊆ (V2.D.Run.stateBefore E rho j x).st.fg.TF := by
  have h := tf_cumulative_all (fgsaCoreReads p c) E rho (fgsaCoreLaws p c)
    (tree_keep p c) hij x
  rw [TFAt_def, TFAt_def, fgsaCoreReads_def] at h
  exact h

private theorem strict_tick_tree (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t)) :
    (V2.D.Run.stateBefore E rho i x).st.fg.TF =
      (V2.D.Run.stateBeforeTime E rho t x).st.fg.TF := by
  have h := tf_before_tick_eq_beforeTime (fgsaCoreReads p c) E rho hs (tree_restore p c) hi
  rw [TFAt_def, fgsaCoreReads_def] at h
  exact h

private abbrev params : Params :=
  { Δ := 1, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 1, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev env : Generic.Env (Fin 3) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => false

-- An inhabited FG electorate and two faulty nodes with no FG seat.
-- This is a population interface model, not an ExecutionValid fixture.
private abbrev trace : V2.D.Run (Fin 3) (fgsa params unitCodec) where
  honest := {0}
  horizon := 1
  events := []
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

private theorem off_electorate_counts :
    (Finset.univ.filter (fun i : Fin params.n =>
      safetyHolder (fgsaSafetyReads params unitCodec) trace i ∉ trace.honest)).card = 0 ∧
    (Gen.V2.Duty.faulty trace).card = 2 := by decide

private theorem fg_strict_premise :
    (Finset.univ.filter (fun i : Fin params.n =>
      safetyHolder (fgsaSafetyReads params unitCodec) trace i ∉ trace.honest)).card <
        2 * Gen.Pure.qF params.n - params.n := by decide

private theorem node_strict_premise_fails :
    ¬ (Gen.V2.Duty.faulty trace).card < 2 * Gen.Pure.qF params.n - params.n := by decide

private theorem no_run_blocks (B : FGBlock (Fin params.n)) :
    ¬ safetyRunBlock (fgsaCoreReads params unitCodec) (fgsaSafetyReads params unitCodec)
      env trace B := by
  simp [safetyRunBlock, V2.D.Run.emits, trace]

private theorem no_emitted_slash (x : Fin 3) :
    safetyNoSlash (fgsaSafetyReads params unitCodec) env trace x := by
  intro a b ha
  obtain ⟨k, t, hk, _⟩ := ha
  simp at hk

private theorem off_electorate_bound :
    safetyBound (fgsaCoreReads params unitCodec) (fgsaSafetyReads params unitCodec)
      params.E env trace :=
  safety_fault_count_bound_fg_lt (fgsaCoreReads params unitCodec)
    (fgsaSafetyReads params unitCodec) params.E env trace (fgsaSafetyUnitLaws params)
    (fun B hB => False.elim (no_run_blocks B hB)) (fun x _ => no_emitted_slash x)
    fg_strict_premise

#print axioms tree_restore
#print axioms tree_keep
#print axioms fgsa_retained_tree
#print axioms strict_tick_tree
#print axioms off_electorate_counts
#print axioms fg_strict_premise
#print axioms node_strict_premise_fails
#print axioms off_electorate_bound
#print axioms AvailableChain.FGSA.Run.kmid_chainRows_of_head
#print axioms AvailableChain.FGSA.Run.kmid_head_held_from
#print axioms AvailableChain.FGSA.Run.finality_action_source
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_finalizedMonotone_restart

end AvailableChain.FGSA.Run.Tests.P0a
end
