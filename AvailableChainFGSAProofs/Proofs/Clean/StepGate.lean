module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate

public section

/-! P3 §8.7 F2.5a; bp02 §§5.4–5.5. Independent gate guard.
History assembly waits for active-batch counts and SameLabel. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In)
    [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- P3 §8.7 F2.5a, bp02 §5.5. Class B (FG-SA run instance).
DC: NamedConfirmationWalk.lean:38 and JointHistoryGapsIdx.lean:26.
INTENTIONAL divergence: DC has no lease veto; the SA whole-result guard
uses old local lease origins (spec/fgsa-protocol.tex:2506–2525).
The supplied Ordered clause suffices before new Continues is available. -/
theorem clean_gate_passed_of_ordered (b₀ : Time) :
    CleanCut₂ p c E rho b₀ → Gen.Pure.FaultQ p.n (Gen.V2.faulty rho).card →
    FGFoundation p c E rho → SrcFrameAboveStmt p c E rho →
    ∀ i x s B, i < timeIdx rho b₀ → IsGateTick p c rho i x s →
      CleanHist p c E rho i → (∀ k, k ≤ i → CleanState p c E rho k) →
      gateResultAt p c E rho i = some (some B) →
      (∀ r C, (r, C) ∈ cleanResults p c E rho i → r < s → Block.Preceq C B) →
      gatePassedAt p c E rho i := by
  intro b _ _ _ i x s B _ ht _ hall hB hord
  have hsch := b.base.valid.toScheduleWellFormed
  refine ⟨x, s, ht, ?_, B, ?_, ?_⟩
  · change ((clockPre p (storeAt p c E rho i x) _).base.genuine.find? _).map _ = none
    rw [clockPre_genuine]
    exact fgsa_gate_fresh E rho hsch ht
  · exact Option.some.inj ((clean_gate_raw hsch ht).symm.trans hB)
  · apply List.any_eq_false.mpr
    intro row hr
    have hold : row ∈ (storeAt p c E rho i x).base.obligations :=
      (clockPre_obligations_sublist p _ _).subset hr
    obtain ⟨k, hk, r, C, hkt, _, hC, hrow⟩ := (hall i le_rfl).leases x row hold
    have htime := fgsa_tick_time_strict E rho hsch hkt ht hk
    have hrs : r < s := by
      change 4 * p.Δ * (r : Int) + 6 * p.Δ <
        4 * p.Δ * (s : Int) + 6 * p.Δ at htime
      have hd := p.deltaPos
      exact_mod_cast (show (r : Int) < (s : Int) by nlinarith)
    have hCB := hord r C ⟨k, hk, x, hkt, hC⟩ hrs
    have hc := block_compatible_of_common (block_preceq_trans hrow hCB)
      (block_preceq_refl B)
    simpa only [Block.Compatible, Bool.not_eq_true', Bool.not_eq_false] using hc

-- These are the exact run-side obligations still assigned to Shared/Count
-- and the active-honest-batch instance. They stay private, with hconf.
omit [Fintype V] in
private theorem ordered_of_confirmation
    (hconf : ∀ (p : Params) (v : GridCO.State p.n) (a B : Block) (s : Slot),
      Block.Compatible a B →
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s a →
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s B →
      (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks) →
      ∃ C, SA.confirmationFrom p.toParams a v s = some C ∧ Block.Preceq B C)
    {i : Nat} (hsch : V2.ScheduleWellFormed E rho)
    (hh : CleanHist p c E rho i) (hs : CleanState p c E rho i)
    (hbatch : ∀ x s, IsGateTick p c rho i x s →
      ∀ r B, (r, B) ∈ cleanResults p c E rho i → r < s →
      let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams s)
      let v := actView pre
      let a := eraseFG pre.fg.F
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s a ∧
      GridCO.voterCount (GridCO.lateVotes p.toParams.engine v s) <
        2 * SA.prefixSupport p.toParams v s B ∧
      (∀ X, Block.Preceq a X → Block.Preceq X B → X ≠ a → X ∈ v.blocks)) :
    ∀ s r B C, (s, B) ∈ cleanResults p c E rho (i + 1) →
      (r, C) ∈ cleanResults p c E rho (i + 1) → s < r → Block.Preceq B C := by
  have hlabels : ∀ {j x y s r}, j ≤ i → IsGateTick p c rho j x s →
      IsGateTick p c rho i y r → s ≤ r := by
    intro j x y s r hji hj hi
    have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
      rcases hji.eq_or_lt with rfl | hlt
      · exact le_of_eq (V2.Event.tick.inj (Option.some.inj (hj.symm.trans hi))).2
      · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
        have hk := (List.pairwise_iff_getElem.mp hsch.sorted) j i hjl hil hlt
        rw [hje, hie] at hk
        exact V2.Engine.time_le_of_key_le _ _ hk
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤
      4 * p.Δ * (r : Int) + 6 * p.Δ at ht
    have hd := p.deltaPos
    exact_mod_cast (show (s : Int) ≤ (r : Int) by nlinarith)
  intro s r B C hB hC hsr
  rcases cleanResults_mem_succ_iff.mp hC with hCold | ⟨x, ht, hCnew⟩
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · exact hh.ordered s r B C hBold hCold hsr
    · obtain ⟨j, hj, x, hx, _⟩ := hCold
      exact (Nat.not_lt_of_ge (hlabels (Nat.le_of_lt hj) hx hu) hsr).elim
  · rcases cleanResults_mem_succ_iff.mp hB with hBold | ⟨y, hu, _⟩
    · let pre := clockPre p (storeAt p c E rho i x) (SA.gateTime p.toParams r)
      have hac : Block.Compatible (eraseFG pre.fg.F) B := by
        change Block.Compatible (eraseFG (clockPre p _ _).fg.F) B
        rw [clockPre_fg]
        rcases (hs.gateInputs x r ht).1 with hg | ⟨t, D, hD, _, haD⟩
        · change Block.Compatible (F_at p c E rho i x) B
          rw [hg]
          exact block_compatible_of_common (block_genesis_preceq B) (block_preceq_refl B)
        · exact block_compatible_of_preceq_compatible haD (cleanHist_results_compatible hh hD hBold)
      obtain ⟨ha, hb, hpath⟩ := hbatch x r ht s B hBold hsr
      obtain ⟨D, hD, hBD⟩ := hconf p (actView pre) (eraseFG pre.fg.F) B r hac ha hb hpath
      have hraw := Option.some.inj ((clean_gate_raw hsch ht).symm.trans hCnew)
      have he : D = C := Option.some.inj (hD.symm.trans hraw)
      exact he ▸ hBD
    · exact (Nat.not_lt_of_ge (hlabels le_rfl ht hu) hsr).elim

#print axioms ordered_of_confirmation

end AvailableChain.FGSA.Run
end
