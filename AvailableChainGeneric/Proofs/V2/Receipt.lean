module
public import AvailableChainGeneric.Statements.V2.Receipt
public import AvailableChainEngineV2.Conditions.Delivery
public import AvailableChainGeneric.Proofs.V2.Reads
public import AvailableChainKitV2.EngineClock

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
  {E : Generic.Env V} {rho : Run V P}

-- GLY:1166–1167; Delivery.lean:25–38 supplies the same two fields.
theorem deliveryWithin_of_partialSynchrony (h : PartialSynchrony E rho) :
    DeliveryWithin E rho (fun t => max t E.t_GST + E.Δ) rho.horizon :=
  ⟨h.broadcast, h.relay⟩

-- GLY:1168–1169; Delivery.lean:43–56 supplies the same two fields.
theorem deliveryWithin_of_healthyPrefix (b₀ : Time) (h : HealthyPrefixDelivery E rho b₀) :
    DeliveryWithin E rho (fun t => t + E.Δ) b₀ :=
  ⟨h.broadcast, h.relay⟩

-- S3-02; Statements/V2/Receipt.lean:77–91; KitV2/Stable.lean:49.
theorem timely_of_clock_statement : TimelyOfClockStatement := by
  intro V _ In P E rho Timely C hS w o T j i hact hj hji hrf
  apply (C.timely_iff _ o).2
  rw [C.clockOf_eq]
  apply le_trans hact
  have hbase : T ≤ C.clock.now (Run.stateBefore E rho (j + 1) w) := by
    rw [(Run.step_tick_eq E rho hj).1, C.clock.now_tick]
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
      dsimp only [World.step]
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
      dsimp only [World.step]
      rw [Function.update_self, C.clock.process]
      exact hk

-- S3-02; Statements/V2/Receipt.lean:95–105; Proofs/V2/Reads.lean:40.
theorem timely_of_emit_statement : TimelyOfEmitStatement := by
  intro V _ In P E rho Timely C o t ht hpub hth
  exact publicTime_le_pubFloor E hpub hth

-- S3-02; Statements/V2/Receipt.lean:109–122; KitV2/EngineClock.lean:104.
theorem timely_of_relay_statement : TimelyOfRelayStatement := by
  intro V _ In P E rho Timely C hAS hS hrestore v i o t hacc
  have hzero : 0 ≤ (0 : Time) ∧ PublicTime E 0 := by
    refine ⟨le_rfl, ?_⟩
    unfold PublicTime
    exact ⟨0, (Int.zero_mul E.Δ).symm⟩
  have hclock : 0 ≤ C.clock.now (Run.stateBefore E rho i v) ∧
      PublicTime E (C.clock.now (Run.stateBefore E rho i v)) := by
    refine stateBefore_step_induction E rho
      (fun st => 0 ≤ C.clock.now st ∧ PublicTime E (C.clock.now st))
      (Nat.zero_le i) v ?_ ?_
    · intro k e h0k hki he hv hk
      cases e with
      | restart u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, hrestore]
          exact hzero
      | tick u t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, C.clock.now_tick]
          have hmem := List.mem_of_getElem? he
          exact ⟨(hS.in_horizon _ hmem).1, hS.tick_public v t' hmem⟩
      | deliver u o' t' =>
          dsimp only [Event.node] at hv
          subst u
          dsimp only [World.step]
          rw [Function.update_self, C.clock.process]
          exact hk
    · unfold Run.stateBefore World.init
      simp only [List.take_zero, List.foldl_nil, C.clock.init]
      exact hzero
  unfold Run.acceptsAt Run.handlesAt at hacc
  rcases hacc with ⟨⟨o', hi, hhandles⟩, hfalse, htrue⟩
  rw [Run.stateBefore_succ E rho hi] at htrue
  dsimp only [World.step] at htrue
  rw [Function.update_self] at htrue
  have htimely := hAS.timely _ o' o
    (by rw [C.clockOf_eq]; exact hclock.1) hfalse htrue hhandles
  have hact := (C.timely_iff _ o).1 htimely
  rw [C.clockOf_eq] at hact
  exact hact.trans (publicTime_le_pubFloor E hclock.2
    (stateBefore_now_le_event C.clock (fun d => le_of_eq (hrestore d)) E rho hS hi v))

-- S3-03; Statements/V2/Receipt.lean:162–179; KitV2/Stable.lean:49.
theorem firstAccept_of_processed_statement : FirstAcceptOfProcessedStatement := by
  intro V _ In P E rho w o i₀ k hik hrf h₀ hk htick hdeliv
  by_contra hno
  have hfalse : P.processed (Run.stateBefore E rho k w) o = false := by
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
        rw [← Run.stateBefore_succ E rho he]
        exact htick i t hi hik' he hprev
    | deliver u o' t' =>
        dsimp only [Event.node] at hv
        subst u
        dsimp only [World.step]
        rw [Function.update_self]
        cases hprocessed : P.processed (P.process (Run.stateBefore E rho i w) o') o with
        | false => rfl
        | true =>
            have hnext : P.processed (Run.stateBefore E rho (i + 1) w) o = true := by
              rw [Run.stateBefore_succ E rho he]
              dsimp only [World.step]
              rw [Function.update_self]
              exact hprocessed
            apply False.elim
            apply hno
            refine ⟨i, t', hi, hik', ?_⟩
            unfold Run.acceptsAt Run.handlesAt
            exact ⟨⟨o', he, hdeliv i o' t' hi hik' he hprev hprocessed⟩, hprev, hnext⟩
  rw [hk] at hfalse
  exact Bool.noConfusion hfalse

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem timely_of_clock :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (w : V), ∀ (o : P.Object), ∀ (T : Time), ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : restartFree rho w j i),
    Timely (Run.stateBefore E rho i w) o :=
  @timely_of_clock_statement

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
set_option linter.unusedDecidableInType false in
theorem timely_of_emit :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object), ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_emit_statement

-- S3-02 LINK; preserve all frozen binders.
set_option linter.unusedVariables false in
theorem timely_of_relay :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
  ∀ (v : V), ∀ (i : Nat), ∀ (o : P.Object), ∀ (t : Time),
  ∀ (hacc : Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t :=
  @timely_of_relay_statement

-- S3-03 LINK; only unused proof binder names have a leading underscore.
theorem firstAccept_of_processed :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ (w : V), ∀ (o : P.Object), ∀ (i₀ k : Nat),
  ∀ (_hik : i₀ ≤ k),
  ∀ (_hrf : restartFree rho w i₀ k),
  ∀ (_h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
  ∀ (_hk : P.processed (Run.stateBefore E rho k w) o = true),
  ∀ (_htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (_hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
      P.handles (Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t' :=
  @firstAccept_of_processed_statement

-- S3-04; Statements/V2/Receipt.lean:126–158; KitV2/Execution.lean:128.
theorem accepted_by_deadline_statement : AcceptedByDeadlineStatement := by
  intro V _ In P E rho Timely Inv dl cut o t w hD hT hw hcut hlt hS
    hES hPS hReady hA C hInv hAdm j hj hrf hNX
  let n := Run.idxBefore rho (dl t)
  have hdeadline : Run.stateBefore E rho n = Run.stateBeforeTime E rho (dl t) :=
    stateBefore_idxBefore E rho (dl t) hS
  have hNXn : P.excludes (Run.stateBefore E rho n w) o = false := by
    rw [hdeadline]
    exact hNX
  rw [← hdeadline]
  have hhandled : ∀ a t', t ≤ t' → t' < dl t → Run.handlesAt E rho a w o t' →
      P.processed (Run.stateBefore E rho n w) o = true := by
    intro a t' htt htd ha
    obtain ⟨o', hea, hhandles⟩ := ha
    have han : a < n := (index_lt_idxBefore_iff hS hea (dl t)).2 htd
    have hja : j < a := tick_index_lt_delivery E rho hS hj hea
      ((pubFloor_le E t).trans htt)
    have htimely := timely_of_clock E rho C hS w o (pubFloor E t) j a hAdm hj hja
      (hrf.mono le_rfl (Nat.le_of_lt han))
    obtain ⟨hWF, hdeps⟩ := hReady a t' han ⟨o', hea, hhandles⟩
    have hpost : Run.stateBefore E rho (a + 1) w =
        P.process (Run.stateBefore E rho a w) o' := by
      rw [Run.stateBefore_succ E rho hea]
      dsimp only [World.step]
      rw [Function.update_self]
    have hrfpost : restartFree rho w (a + 1) n :=
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
  · cases hprocessed : P.processed (Run.stateBefore E rho (i + 1) w) o with
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

-- S3-04 LINK; only unused proof binder names have a leading underscore.
theorem accepted_by_deadline :
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ {Inv : P.State → Prop},
  ∀ (dl : Time → Time), ∀ (cut : Time), ∀ (o : P.Object), ∀ (t : Time), ∀ (w : V),
  ∀ (_hD : DeliveryWithin E rho dl cut),
  ∀ (_hT : Trigger E rho o t),
  ∀ (_hw : w ∈ rho.honest),
  ∀ (_hcut : dl t ≤ cut),
  ∀ (_hlt : t < dl t),
  ∀ (_hS : ScheduleWellFormed E rho),
  ∀ (_hES : ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.excludes (Run.stateBefore E rho i v) o = true →
      P.excludes (Run.stateBefore E rho j v) o = true),
  ∀ (_hPS : ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.processed (Run.stateBefore E rho i v) o = true →
      P.processed (Run.stateBefore E rho j v) o = true),
  ∀ (_hReady : ∀ i t', i < Run.idxBefore rho (dl t) → Run.handlesAt E rho i w o t' →
      P.wellFormed o = true ∧ P.depsPresent (Run.stateBefore E rho i w) o = true),
  ∀ (_hA : AcceptanceLaw P Timely Inv),
  ∀ (C : TimelyClock P Timely),
  ∀ (_hInv : ∀ i, Inv (Run.stateBefore E rho i w)),
  ∀ (_hAdm : C.actTime o ≤ pubFloor E t),
  ∀ (j : Nat),
  ∀ (_hj : rho.events[j]? = some (.tick w (pubFloor E t))),
  ∀ (_hrf : restartFree rho w j (Run.idxBefore rho (dl t))),
  ∀ (_hNX : P.excludes (Run.stateBeforeTime E rho (dl t) w) o = false),
    P.processed (Run.stateBeforeTime E rho (dl t) w) o = true :=
  @accepted_by_deadline_statement

end AvailableChain.Gen.V2
