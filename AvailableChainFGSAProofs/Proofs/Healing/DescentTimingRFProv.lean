module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainKitV2.DutyExecution

public section

/-! The low-certificate arm of RFProv clause 1 (B19).
Use its after-action lower cut. The high arm needs the finality source bound.
The reset release q_(sStar) is before that action. This low arm cannot
be applied there. T2 applies at arbitrary read indices; T1 remains an obligation.
Blueprint: W3 21:542–546, H.17 21:2946–3040, H.18 21:3049–3060. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem timing_tick_cut (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {t : Time} (hj : rho.events[j]? = some (.tick x t)) :
    j < afterTicksIdx rho t := by
  by_contra hn
  have hc : cutPred (P := fgsa p c) t (.tick x t) = true := by
    change decide (toLex (t, 1) ≤ toLex (t, 1)) = true
    exact decide_eq_true le_rfl
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
    (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
    (Nat.le_of_not_gt hn) hj
  rw [hc] at hf
  contradiction

/-- The actual action source is held at its pre-action store. -/
theorem healing_action_source_held (hs : V2.D.ScheduleWellFormed E rho)
    {j r : Nat} {x : V} {K : FGBlock (Fin p.n)}
    (hj : rho.events[j]? = some (.tick x (p.actionTime r)))
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    K ∈ (storeAt p c E rho j x).fg.TF := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hK; contradiction
  | some i =>
    have hij : i = j := by
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hi)
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      exact (List.Nodup.getElem_inj_iff hs.nodup).mp (hie.trans hje.symm)
    simp only [hi, Option.map_some, Option.some.injEq, hij] at hK
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r)
    have hm : K ∈ fullTree p st := by
      change deepest _ = some K at hK
      exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hK).1).1
    have hm' : K ∈ st.fg.TF := (Finset.mem_filter.mp hm).1
    change K ∈ (FGSA.clock p _ _).fg.TF at hm'
    rwa [FGSA.clock_fg] at hm'

/-- The low-certificate arm of T3. This uses the actual CStar source
from H0Reset.fresh and RXing, after RFProv's action cut.
The full F producer stops at T1's field-only emission obligation. -/
theorem healing_low_finality_at_reset (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (xing : RXing p c E rho)
    (w : HealingWitness) (h0 : H0 p c E rho w) {i : Nat} {x : V}
    {D : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hD : D ∈ (storeAt p c E rho i x).fg.TF)
    (hDF : (finalityView p D).F = (storeAt p c E rho i x).fg.F)
    (hlow : (finalityView p D).h_F ≤ w.M) :
    Block.Preceq (F_at p c E rho i x) w.CStar := by
  obtain ⟨j, y, a, C, ha, _, hC, hCS, hCh⟩ := h0.fresh
  have hji : j ≤ i := (Nat.le_of_lt (timing_tick_cut p c E rho hs ha.2.1)).trans hi
  have hheld := healing_action_source_held p c E rho hs ha.2.1 hC
  have hheld' := (fgsa_store_cumulative p c E rho hnr hji y).1 hheld
  have hFC := xing i i x y D C hx le_rfl hD hDF ⟨ha.1, hheld'⟩
    (by rw [hCh]; exact Nat.lt_succ_of_le hlow)
  rw [← hCS]
  exact eraseFG_preceq hFC

end AvailableChain.FGSA.Run
end
