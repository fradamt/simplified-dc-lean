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

end AvailableChain.Gen.V2
