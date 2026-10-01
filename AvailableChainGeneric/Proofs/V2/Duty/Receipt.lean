module
public import AvailableChainGeneric.Statements.V2.Duty.Receipt
public import AvailableChainEngineV2.Conditions.Duty.Delivery
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainKitV2.DutyEngineClock

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
  {E : Generic.Env V} {rho : D.Run V P}

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:17.
theorem deliveryWithin_of_partialSynchrony (h : D.PartialSynchrony E rho) :
    DeliveryWithin E rho (fun t => max t E.t_GST + E.Δ) rho.horizon :=
  ⟨h.broadcast_emitted, h.relay_accepted⟩

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:22.
theorem deliveryWithin_of_healthyPrefix (b₀ : Time) (h : D.HealthyPrefixDelivery E rho b₀) :
    DeliveryWithin E rho (fun t => t + E.Δ) b₀ :=
  ⟨h.broadcast_emitted, h.relay_accepted⟩

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:27.
theorem timely_of_clock_statement : TimelyOfClockStatement := by
  intro V _ In P E rho Timely C hS w o T j i hact hj hji hrf
  apply (C.timely_iff _ o).2
  rw [C.clockOf_eq]
  apply le_trans hact
  have hbase : T ≤ C.clock.now (D.Run.stateBefore E rho (j + 1) w) := by
    rw [(D.Run.step_tick_eq E rho hj).1, C.clock.now_tick]
  refine stateBefore_step_induction E rho (fun st => T ≤ C.clock.now st)
    (Nat.succ_le_of_lt hji) w ?_ hbase
  intro k e hjk hki he hv hk
  cases e with
  | restart u t =>
      dsimp only [Event.node] at hv
      subst u
      exact absurd he (hrf k t (Nat.le_trans (Nat.le_succ j) hjk) hki)
  | tick u t =>
      dsimp only [Event.node] at hv
      subst u
      dsimp only [D.World.step]
      rw [Function.update_self, C.clock.now_tick]
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp he
      have hkey := (List.pairwise_iff_getElem.mp hS.sorted) j k hjl hkl
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hjk)
      rw [hje, hke] at hkey
      exact time_le_of_key_le _ _ hkey
  | deliver u o' t =>
      dsimp only [Event.node] at hv
      subst u
      dsimp only [D.World.step]
      rw [Function.update_self, C.clock.process]
      exact hk

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:61.
theorem timely_of_emit_statement : TimelyOfEmitStatement := by
  intro V _ In P E rho Timely C o t ht hpub hth
  exact publicTime_le_pubFloor E hpub hth

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:66.
theorem timely_of_relay_statement : TimelyOfRelayStatement := by
  intro V _ In P E rho Timely C hAS hS hrestore v i o t hacc
  have hzero : 0 ≤ (0 : Time) ∧ V2.PublicTime E 0 := by
    refine ⟨le_rfl, ?_⟩
    unfold V2.PublicTime
    exact ⟨0, (Int.zero_mul E.Δ).symm⟩
  have hclock : 0 ≤ C.clock.now (D.Run.stateBefore E rho i v) ∧
      V2.PublicTime E (C.clock.now (D.Run.stateBefore E rho i v)) := by
    refine stateBefore_step_induction E rho
      (fun st => 0 ≤ C.clock.now st ∧ V2.PublicTime E (C.clock.now st))
      (Nat.zero_le i) v ?_ ?_
    · intro k e h0k hki he hv hk
      cases e with
      | restart u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, hrestore]
          exact hzero
      | tick u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, C.clock.now_tick]
          have hmem := List.mem_of_getElem? he
          exact ⟨(hS.in_horizon _ hmem).1, hS.tick_public v t' hmem⟩
      | deliver u o' t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [D.World.step]
          rw [Function.update_self, C.clock.process]
          exact hk
    · unfold D.Run.stateBefore D.World.init
      simp only [List.take_zero, List.foldl_nil, C.clock.init]
      exact hzero
  unfold D.Run.acceptsAt D.Run.handlesAt at hacc
  rcases hacc with ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩
  rw [D.Run.stateBefore_succ E rho hi] at htrue
  dsimp only [D.World.step] at htrue
  rw [Function.update_self] at htrue
  have htimely := hAS.timely _ o' o
    (by rw [C.clockOf_eq]; exact hclock.1) hfalse htrue hhandles
  have hact := (C.timely_iff _ o).1 htimely
  rw [C.clockOf_eq] at hact
  exact hact.trans (publicTime_le_pubFloor E hclock.2
    (stateBefore_now_le_event C.clock (fun d => le_of_eq (hrestore d)) E rho hS hi v))

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:114.
theorem firstAccept_of_processed_statement : FirstAcceptOfProcessedStatement := by
  intro V _ In P E rho w o i₀ k hik hrf h₀ hk htick hdeliv
  by_contra hno
  have hfalse : P.processed (D.Run.stateBefore E rho k w) o = false := by
    refine stateBefore_step_induction E rho (fun st => P.processed st o = false)
      hik w ?_ h₀
    intro i e hi hik' he hv hprev
    cases e with
    | restart u t =>
        dsimp only [Event.node] at hv
        subst u
        exact absurd he (hrf i t hi hik')
    | tick u t =>
        dsimp only [Event.node] at hv
        subst u
        rw [← D.Run.stateBefore_succ E rho he]
        exact htick i t hi hik' he hprev
    | deliver u o' t' =>
        dsimp only [Event.node] at hv
        subst u
        dsimp only [D.World.step]
        rw [Function.update_self]
        cases hprocessed : P.processed (P.process (D.Run.stateBefore E rho i w) o') o with
        | false => rfl
        | true =>
            have hnext : P.processed (D.Run.stateBefore E rho (i + 1) w) o = true := by
              rw [D.Run.stateBefore_succ E rho he]
              dsimp only [D.World.step]
              rw [Function.update_self]
              exact hprocessed
            apply False.elim
            apply hno
            refine ⟨i, t', hi, hik', ?_⟩
            unfold D.Run.acceptsAt D.Run.handlesAt
            exact ⟨⟨o', he, hdeliv i o' t' hi hik' he hprev hprocessed⟩, hprev, hnext⟩
  rw [hk] at hfalse
  exact Bool.noConfusion hfalse

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:154.
theorem timely_of_clock :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (w : V), ∀ (o : P.Object), ∀ (T : Time), ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : D.restartFree rho w j i),
    Timely (D.Run.stateBefore E rho i w) o :=
  @timely_of_clock_statement

set_option linter.unusedVariables false in
set_option linter.unusedDecidableInType false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:171.
theorem timely_of_emit :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object), ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : V2.PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_emit_statement

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:185.
theorem timely_of_relay :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
  ∀ (v : V), ∀ (i : Nat), ∀ (o : P.Object), ∀ (t : Time),
  ∀ (hacc : D.Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_relay_statement

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:200.
theorem firstAccept_of_processed :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (w : V), ∀ (o : P.Object), ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : D.restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (D.Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (D.Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (D.Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (P.process (D.Run.stateBefore E rho i w) o') o = true →
      P.handles (D.Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t' :=
  @firstAccept_of_processed_statement

-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:219.
theorem accepted_by_deadline_statement : AcceptedByDeadlineStatement := by
  intro V _ In P E rho Timely Inv dl cut o t w hD hT hw hcut hlt hS
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
  · obtain ⟨t', htt, htd, a, ha⟩ := hD.broadcast v hv o t hemits w hw hcut hNX
    exact hhandled a t' htt htd ha
  · cases hprocessed : P.processed (D.Run.stateBefore E rho (i + 1) w) o with
    | false =>
        obtain ⟨t', htt, htd, a, ha⟩ := hD.relay v hv i o t hacc w hw
          hprocessed hcut hNX
        exact hhandled a t' htt htd ha
    | true =>
        obtain ⟨⟨o', hei, _⟩, _, _⟩ := hacc
        have hin : i < n := (index_lt_idxBefore_iff hS hei (dl t)).2 hlt
        have hji : j < i := tick_index_lt_delivery E rho hS hj hei (pubFloor_le E t)
        exact hPS w o (i + 1) n (Nat.succ_le_of_lt hin)
          (hrf.mono (Nat.le_trans (Nat.le_of_lt hji) (Nat.le_succ i)) le_rfl) hprocessed

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Receipt.lean:270.
theorem accepted_by_deadline :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ {Inv : P.State → Prop},
  ∀ (dl : Time → Time), ∀ (cut : Time), ∀ (o : P.Object), ∀ (t : Time), ∀ (w : V),
  ∀ (hD : DeliveryWithin E rho dl cut),
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
  @accepted_by_deadline_statement

end AvailableChain.Gen.V2.Duty
