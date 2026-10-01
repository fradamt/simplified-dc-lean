module
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2.Duty

theorem partialSynchrony_iff_by_const_statement : PartialSynchronyIffByConstStatement := by
  intro V _ In P E rho
  exact ⟨fun h => ⟨h.broadcast_emitted, h.relay_accepted⟩,
    fun h => ⟨h.broadcast_emitted, h.relay_accepted⟩⟩

set_option linter.unusedVariables false in
theorem partialSynchrony_iff_by_const :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  D.PartialSynchrony E rho ↔ PartialSynchronyBy E rho (fun _ => E.Δ) :=
  @partialSynchrony_iff_by_const_statement

theorem healthyPrefix_iff_by_const_statement : HealthyPrefixIffByConstStatement := by
  intro V _ In P E rho cut
  exact ⟨fun h => ⟨h.broadcast_emitted, h.relay_accepted⟩,
    fun h => ⟨h.broadcast_emitted, h.relay_accepted⟩⟩

set_option linter.unusedVariables false in
theorem healthyPrefix_iff_by_const :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (cut : Time), D.HealthyPrefixDelivery E rho cut ↔
    HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut :=
  @healthyPrefix_iff_by_const_statement

theorem deliveryWithin_iff_on_true_statement : DeliveryWithinIffOnTrueStatement := by
  intro V _ In P E rho dl cut
  constructor
  · intro h
    exact ⟨fun v hv o _ t => h.broadcast v hv o t,
      fun v hv i o _ t => h.relay v hv i o t⟩
  · intro h
    exact ⟨fun v hv o t => h.broadcast v hv o trivial t,
      fun v hv i o t => h.relay v hv i o trivial t⟩

set_option linter.unusedVariables false in
theorem deliveryWithin_iff_on_true :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (dl : Time → Time) (cut : Time), DeliveryWithin E rho dl cut ↔
    DeliveryWithinOn E rho (fun _ => True) dl cut :=
  @deliveryWithin_iff_on_true_statement

theorem DeliveryWithinOn_mono_statement : DeliveryWithinOnMonoStatement := by
  intro V _ In P E rho Q Q' dl cut h hQ
  exact ⟨fun v hv o ho t => h.broadcast v hv o (hQ o ho) t,
    fun v hv i o ho t => h.relay v hv i o (hQ o ho) t⟩

set_option linter.unusedVariables false in
theorem DeliveryWithinOn.of_subfamily :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Q Q' : P.Object → Prop} {dl : Time → Time} {cut : Time},
  DeliveryWithinOn E rho Q dl cut → (∀ o, Q' o → Q o) →
    DeliveryWithinOn E rho Q' dl cut :=
  @DeliveryWithinOn_mono_statement

theorem labelSync_to_on_statement : LabelSyncToOnStatement := by
  intro V _ In P E rho Q vt dt h
  rcases h with ⟨dl, cut, hD, hrest⟩
  exact ⟨dl, cut, DeliveryWithinOn.of_subfamily E rho
    ((deliveryWithin_iff_on_true E rho dl cut).1 hD) (fun _ _ => trivial), hrest⟩

set_option linter.unusedVariables false in
theorem labelSync_to_on :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time),
  LabelSync E rho vt dt → LabelSyncOn E rho Q vt dt :=
  @labelSync_to_on_statement

theorem labelFacts_to_on_statement : LabelFactsToOnStatement := by
  intro V _ In P E rho Q vt dt h m hf
  exact ⟨labelSync_to_on E rho Q vt dt hf.sync, hf.batch⟩

set_option linter.unusedVariables false in
theorem labelFacts_to_on :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  LabelFacts E rho vt dt h m → LabelFactsOn E rho Q vt dt h m :=
  @labelFacts_to_on_statement

theorem deliveryWithinOn_of_partialSynchronyBy_statement :
    DeliveryWithinOnOfPartialSynchronyByStatement := by
  intro V _ In P E rho delayOf h Q δ hQ
  constructor
  · intro v hv o ho t he w hw hc hx
    rw [← hQ o ho] at hc hx ⊢
    exact h.broadcast_emitted v hv o t he w hw hc hx
  · intro v hv i o ho t ha w hw hp hc hx
    rw [← hQ o ho] at hc hx ⊢
    exact h.relay_accepted v hv i o t ha w hw hp hc hx

set_option linter.unusedVariables false in
theorem deliveryWithinOn_of_partialSynchronyBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time},
  PartialSynchronyBy E rho delayOf → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => max t E.t_GST + δ) rho.horizon :=
  @deliveryWithinOn_of_partialSynchronyBy_statement

theorem deliveryWithinOn_of_healthyPrefixBy_statement :
    DeliveryWithinOnOfHealthyPrefixByStatement := by
  intro V _ In P E rho delayOf cut h Q δ hQ
  constructor
  · intro v hv o ho t he w hw hc hx
    rw [← hQ o ho] at hc hx ⊢
    exact h.broadcast_emitted v hv o t he w hw hc hx
  · intro v hv i o ho t ha w hw hp hc hx
    rw [← hQ o ho] at hc hx ⊢
    exact h.relay_accepted v hv i o t ha w hw hp hc hx

set_option linter.unusedVariables false in
theorem deliveryWithinOn_of_healthyPrefixBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (cut : Time),
  HealthyPrefixDeliveryBy E rho delayOf cut → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => t + δ) cut :=
  @deliveryWithinOn_of_healthyPrefixBy_statement

theorem LabelSyncOn_of_cleanCutBy_statement : LabelSyncOnOfCleanCutByStatement := by
  intro V _ In P E rho delayOf Q b₀ vt dt h hQ hvd hb hb₀
  refine ⟨(fun t => t + E.Δ), b₀,
    deliveryWithinOn_of_healthyPrefixBy E rho b₀ h Q E.Δ hQ, ?_, ?_, ?_,
    hvd, hb, hb.trans hb₀⟩
  · exact fun _ _ h => add_le_add h le_rfl
  · exact fun t => lt_add_of_pos_right t E.Δ_pos
  · exact fun t => add_le_add (le_max_left t vt) le_rfl

set_option linter.unusedVariables false in
theorem LabelSyncOn.of_cleanCutBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → LabelSyncOn E rho Q vt dt :=
  @LabelSyncOn_of_cleanCutBy_statement

theorem LabelSyncOn_of_recoveryBy_statement : LabelSyncOnOfRecoveryByStatement := by
  intro V _ In P E rho delayOf Q vt dt h hQ hG hvd hh
  refine ⟨(fun t => max t E.t_GST + E.Δ), rho.horizon,
    deliveryWithinOn_of_partialSynchronyBy E rho h Q E.Δ hQ, ?_, ?_, ?_, hvd, hh, hh⟩
  · exact fun _ _ h => add_le_add (max_le_max h le_rfl) le_rfl
  · exact fun t => (le_max_left t E.t_GST).trans_lt
      (lt_add_of_pos_right (max t E.t_GST) E.Δ_pos)
  · exact fun _ => add_le_add (max_le_max le_rfl hG) le_rfl

set_option linter.unusedVariables false in
theorem LabelSyncOn.of_recoveryBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → LabelSyncOn E rho Q vt dt :=
  @LabelSyncOn_of_recoveryBy_statement

theorem LabelFactsOn_of_cleanCutBy_statement : LabelFactsOnOfCleanCutByStatement := by
  intro V _ In P E rho delayOf Q b₀ vt dt h m hp hQ hvd hb hb₀ hB
  exact ⟨LabelSyncOn.of_cleanCutBy E rho Q b₀ vt dt hp hQ hvd hb hb₀, hB⟩

set_option linter.unusedVariables false in
theorem LabelFactsOn.of_cleanCutBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time) (h m : Nat),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m :=
  @LabelFactsOn_of_cleanCutBy_statement

theorem LabelFactsOn_of_recoveryBy_statement : LabelFactsOnOfRecoveryByStatement := by
  intro V _ In P E rho delayOf Q vt dt h m hp hQ hG hvd hh hB
  exact ⟨LabelSyncOn.of_recoveryBy E rho Q vt dt hp hQ hG hvd hh, hB⟩

set_option linter.unusedVariables false in
theorem LabelFactsOn.of_recoveryBy :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m :=
  @LabelFactsOn_of_recoveryBy_statement

theorem delay_pos_of_env_le_statement : DelayPosOfEnvLeStatement := by
  intro V E ΔF hΔ
  exact E.Δ_pos.trans_le hΔ

set_option linter.unusedVariables false in
theorem delay_pos_of_env_le :
  ∀ {V : Type} (E : Generic.Env V) {ΔF : Time}, E.Δ ≤ ΔF → 0 < ΔF :=
  @delay_pos_of_env_le_statement

theorem accepted_by_deadline_on_statement : AcceptedByDeadlineOnStatement := by
  intro V _ In P E rho Timely Inv Q dl cut o t w hD hQ hT hw hcut hlt hS
    hES hPS hReady hA C hInv hAdm j hj hrf hNX
  let n := D.Run.idxBefore rho (dl t)
  have hdeadline : D.Run.stateBefore E rho n = D.Run.stateBeforeTime E rho (dl t) :=
    stateBefore_idxBefore E rho (dl t) hS
  have hNXn : P.excludes (D.Run.stateBefore E rho n w) o = false := by
    rw [hdeadline]
    exact hNX
  rw [← hdeadline]
  have hhandled : ∀ a t', t ≤ t' → t' < dl t → D.Run.handlesAt E rho a w o t' →
      P.processed (D.Run.stateBefore E rho n w) o = true := by
    intro a t' htt htd ha
    obtain ⟨o', hea, hhandles⟩ := ha
    have han : a < n := (index_lt_idxBefore_iff hS hea (dl t)).2 htd
    have hja : j < a := tick_index_lt_delivery E rho hS hj hea
      ((pubFloor_le E t).trans htt)
    have htimely := timely_of_clock E rho C hS w o (pubFloor E t) j a hAdm hj hja
      (hrf.mono le_rfl (Nat.le_of_lt han))
    obtain ⟨hWF, hdeps⟩ := hReady a t' han ⟨o', hea, hhandles⟩
    have hpost : D.Run.stateBefore E rho (a + 1) w =
        P.process (D.Run.stateBefore E rho a w) o' := by
      rw [D.Run.stateBefore_succ E rho hea]
      dsimp only [D.World.step]
      rw [Function.update_self]
    have hrfpost : D.restartFree rho w (a + 1) n :=
      hrf.mono (Nat.le_trans (Nat.le_of_lt hja) (Nat.le_succ a)) le_rfl
    rcases hA.accepts _ o' o (hInv a) hhandles hWF hdeps htimely with hP | hX
    · exact hPS w o (a + 1) n (Nat.succ_le_of_lt han) hrfpost (by rwa [hpost])
    · have hXn := hES w o (a + 1) n (Nat.succ_le_of_lt han) hrfpost
        (by rwa [hpost])
      rw [hNXn] at hXn
      exact Bool.noConfusion hXn
  rw [Trigger_def] at hT
  rcases hT with ⟨v, hv, hemits⟩ | ⟨v, hv, i, hacc⟩
  · obtain ⟨t', htt, htd, a, ha⟩ := hD.broadcast v hv o hQ t hemits w hw hcut hNX
    exact hhandled a t' htt htd ha
  · cases hprocessed : P.processed (D.Run.stateBefore E rho (i + 1) w) o with
    | false =>
        obtain ⟨t', htt, htd, a, ha⟩ := hD.relay v hv i o hQ t hacc w hw
          hprocessed hcut hNX
        exact hhandled a t' htt htd ha
    | true =>
        obtain ⟨⟨o', hei, _⟩, _, _⟩ := hacc
        have hin : i < n := (index_lt_idxBefore_iff hS hei (dl t)).2 hlt
        have hji : j < i := tick_index_lt_delivery E rho hS hj hei (pubFloor_le E t)
        exact hPS w o (i + 1) n (Nat.succ_le_of_lt hin)
          (hrf.mono (Nat.le_trans (Nat.le_of_lt hji) (Nat.le_succ i)) le_rfl) hprocessed

set_option linter.unusedVariables false in
theorem accepted_by_deadline_on :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ {Inv : P.State → Prop},
  ∀ (Q : P.Object → Prop),
  ∀ (dl : Time → Time),
  ∀ (cut : Time),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (w : V),
  ∀ (hD : DeliveryWithinOn E rho Q dl cut),
  ∀ (hQ : Q o),
  ∀ (hT : Trigger E rho o t),
  ∀ (hw : w ∈ rho.honest),
  ∀ (hcut : dl t ≤ cut),
  ∀ (hlt : t < dl t),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (hES : ∀ v o i j, i ≤ j → D.restartFree rho v i j →
      P.excludes (D.Run.stateBefore E rho i v) o = true →
      P.excludes (D.Run.stateBefore E rho j v) o = true),
  ∀ (hPS : ∀ v o i j, i ≤ j → D.restartFree rho v i j →
      P.processed (D.Run.stateBefore E rho i v) o = true →
      P.processed (D.Run.stateBefore E rho j v) o = true),
  ∀ (hReady : ∀ i t', i < D.Run.idxBefore rho (dl t) → D.Run.handlesAt E rho i w o t' →
      P.wellFormed o = true ∧ P.depsPresent (D.Run.stateBefore E rho i w) o = true),
  ∀ (hA : AcceptanceLaw P Timely Inv),
  ∀ (C : TimelyClock P Timely),
  ∀ (hInv : ∀ i, Inv (D.Run.stateBefore E rho i w)),
  ∀ (hAdm : C.actTime o ≤ pubFloor E t),
  ∀ (j : Nat),
  ∀ (hj : rho.events[j]? = some (.tick w (pubFloor E t))),
  ∀ (hrf : D.restartFree rho w j (D.Run.idxBefore rho (dl t))),
  ∀ (hNX : P.excludes (D.Run.stateBeforeTime E rho (dl t) w) o = false),
    P.processed (D.Run.stateBeforeTime E rho (dl t) w) o = true :=
  @accepted_by_deadline_on_statement

end AvailableChain.Gen.V2.Duty
