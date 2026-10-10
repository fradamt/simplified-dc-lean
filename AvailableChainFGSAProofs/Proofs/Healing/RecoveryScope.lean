module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSARun.Proofs.Join
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time}

/-- Recovery bounds each honest restart through the exact horizon by GST.
A restart at GST is permitted. -/
theorem healing_recovery_restart_bound (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {t : Time} (hh : t ≤ rho.horizon)
    {w : Time} (hwt : w ≤ t) (he : V2.Event.restart x w ∈ rho.events) :
    w ≤ E.t_GST := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  by_contra hn
  exact hrec.suffixNoRestart x hx j w hj (lt_of_not_ge hn)
    ((hwt.trans hh).trans_lt (lt_add_of_pos_right _ (by decide)))

/-- The recovery suffix supplies the exact proposer restart cutoff.
The caller must prove GST is at or before the previous slot start. -/
theorem healing_recovery_restart_cutoff (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {t b : Time} (hh : t ≤ rho.horizon)
    (hb : E.t_GST ≤ b) :
    ∀ w, 0 ≤ w → w ≤ t → V2.Event.restart x w ∈ rho.events → w ≤ b := by
  intro w _ hwt he
  exact (healing_recovery_restart_bound hrec hx hh hwt he).trans hb

/-- Convert the exact recovery cutoff to the post-clock joined duty guard. -/
theorem healing_recovery_joinedNow (hrec : RecoverySleep₂ p c E rho G ΔF)
    {i : Nat} {x : V} {t : Time} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x t)) (hh : t ≤ rho.horizon)
    (hb : E.t_GST ≤ slotStartZ p ((p.slotOf t : Int) - 1)) :
    joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st t) = true := by
  exact fgsa_joinedNow_of_joinedEnv E rho hrec.base.valid.toScheduleWellFormed hi
    (healing_recovery_restart_cutoff hrec hx hh hb)

/-- The receiver epoch starts after all restart events at the action anchor.
Use event indices; a restart at the anchor is already inside actionCut. -/
theorem healing_recovery_restartFree (hrec : RecoverySleep₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {a d : Time}
    (ha : E.t_GST ≤ a) (hd : d ≤ rho.horizon) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho d) := by
  have hs := hrec.base.valid.toScheduleWellFormed
  intro k w hka hkd he
  have hwa : a < w := by
    have hn := (V2.D.Engine.index_lt_actionCut_iff hs he a).not.mp (Nat.not_lt.mpr hka)
    change ¬ (w < a ∨ (w = a ∧ (0 : Nat) = 0)) at hn
    rcases lt_trichotomy w a with hlt | heq | hgt
    · exact (hn (Or.inl hlt)).elim
    · exact (hn (Or.inr ⟨heq, rfl⟩)).elim
    · exact hgt
  have hwd := (Gen.V2.Duty.index_lt_idxBefore_iff hs he d).mp hkd
  exact hrec.suffixNoRestart x hx k w he (ha.trans_lt hwa)
    ((hwd.le.trans hd).trans_lt (lt_add_of_pos_right _ (by decide)))

omit [Fintype V] in
/-- Durable FG trees remain available to H2 consumers across each restart. -/
theorem healing_recovery_durable (durable : RStoreDurable p c E rho)
    (i j : Nat) (x : V) (hx : x ∈ rho.honest)
    (hij : i ≤ j) (hj : j ≤ rho.events.length) :
    (storeAt p c E rho i x).fg.TF ⊆ (storeAt p c E rho j x).fg.TF :=
  (durable i j x hx hij hj).1

omit [Fintype V] in
/-- FG finality is monotone through the kept store, including pre-GST restarts. -/
theorem healing_recovery_finality (mono : RMonoAll p c E rho)
    (i j : Nat) (x : V) (hx : x ∈ rho.honest)
    (hij : i ≤ j) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F (storeAt p c E rho j x).fg.F :=
  (mono i j x hx hij).1

/-- Recovery preserves stamps only on the exact receiver event interval. -/
theorem healing_recovery_stamps (hrec : RecoverySleep₂ p c E rho G ΔF)
    (epoch : RStoreEpoch p c E rho)
    {x : V} (hx : x ∈ rho.honest) {a d : Time}
    (ha : E.t_GST ≤ a) (hd : d ≤ rho.horizon)
    (hij : V2.D.Run.actionCut rho a ≤ V2.D.Run.idxBefore rho d)
    (hj : V2.D.Run.idxBefore rho d ≤ rho.events.length) :
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.blockStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.blockStamp ∧
    (storeAt p c E rho (V2.D.Run.actionCut rho a) x).base.voteStamp <+:
      (storeAt p c E rho (V2.D.Run.idxBefore rho d) x).base.voteStamp :=
  epoch _ _ x hx hij hj (healing_recovery_restartFree hrec hx ha hd)

end AvailableChain.FGSA.Run
end
