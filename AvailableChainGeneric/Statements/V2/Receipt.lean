module
public import AvailableChainEngineV2.Engine.Run
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainKitV2.ClockLaws
public import AvailableChainGeneric.Statements.V2.Reads

@[expose] public section

/-! Source: `claude-files/a0/generic-layer.md` (GLY), r3.13, §C.3.
Step-2 item I05. D01 requires closed Statement definitions.
The common binders are from GLY:1109–1110. -/

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1123–1125.
def Trigger (E : Generic.Env V) (rho : Run V P) (o : P.Object) (t : Time) : Prop :=
  (∃ v ∈ rho.honest, Run.emits E rho v o t) ∨
  (∃ v ∈ rho.honest, ∃ i, Run.acceptsAt E rho i v o t)

-- GLY:1123–1125; BUILD §7.2 B3a requires this equation lemma.
theorem Trigger_def (E : Generic.Env V) (rho : Run V P) (o : P.Object) (t : Time) :
    Trigger E rho o t =
      ((∃ v ∈ rho.honest, Run.emits E rho v o t) ∨
        (∃ v ∈ rho.honest, ∃ i, Run.acceptsAt E rho i v o t)) := by
  rw [Trigger]

-- GLY:1127–1138.
structure DeliveryWithin (E : Generic.Env V) (rho : Run V P)
    (dl : Time → Time) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, Run.emits E rho v o t → ∀ w ∈ rho.honest,
    dl t ≤ cut → P.excludes (Run.stateBeforeTime E rho (dl t) w) o = false →
    ∃ t', t ≤ t' ∧ t' < dl t ∧ ∃ j, Run.handlesAt E rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t, Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    P.processed (Run.stateBefore E rho (i + 1) w) o = false →
    dl t ≤ cut → P.excludes (Run.stateBeforeTime E rho (dl t) w) o = false →
    ∃ t', t ≤ t' ∧ t' < dl t ∧ ∃ j, Run.handlesAt E rho j w o t'
  -- = PartialSynchrony (Conditions/Delivery.lean:25–35) with
  --   max t E.t_GST + E.Δ ↦ dl t and rho.horizon ↦ cut.
  -- ReceiptForm, psForm, hpdForm (r3.4) are SUPERSEDED (S3 A11/D14/D22).

-- GLY:1140–1145.
structure TimelyClock (P : ProtocolSpec In) (Timely : P.State → P.Object → Prop) where
  actTime : P.Object → Time      -- the handler ADMISSION THRESHOLD (L19)
  clockOf : P.State → Time
  timely_iff : ∀ st o, Timely st o ↔ actTime o ≤ clockOf st
  clock : ClockLaws P            -- KitV2/ClockLaws.lean:18
  clockOf_eq : ∀ st, clockOf st = clock.now st

-- GLY:1147–1153.
structure AcceptanceLaw (P : ProtocolSpec In) (Timely : P.State → P.Object → Prop)
    (Inv : P.State → Prop) : Prop where
  accepts : ∀ st o' o, Inv st → P.handles st o' o → P.wellFormed o = true →
    P.depsPresent st o = true → Timely st o →
    P.processed (P.process st o') o = true ∨ P.excludes (P.process st o') o = true
  -- Negative controls of the r2 form: see below. `excludes_process` is NOT a
  -- field (L20): no generic lemma consumes it.

-- GLY:1155–1163.
structure AdmitSound (P : ProtocolSpec In) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) : Prop where
  timely : ∀ st o' o, 0 ≤ C.clockOf st → P.processed st o = false →
    P.processed (P.process st o') o = true → P.handles st o' o → Timely st o
  -- THE ONE WRITTEN FORM of AdmitSound (Opus m3). SYN §5, S3 and T7 cite this
  -- block and do not restate its binders.
  -- L30: the premise 0 ≤ C.clockOf st is needed (see "Negative clock" below).
  -- The `wellFormed o` conjunct of L19 is dropped: neither instance checks
  -- the full `wellFormed` in its handler (see "AdmitSound" below).

-- Keep every source binder name, including unused proof binders (D01).

-- GLY:1172–1176; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def TimelyOfClockStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (T : Time),
  ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : restartFree rho w j i),
    Timely (Run.stateBefore E rho i w) o

set_option linter.unusedVariables false in
theorem TimelyOfClockStatement_def :
    TimelyOfClockStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hS : ScheduleWellFormed E rho),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (T : Time),
      ∀ (j i : Nat),
      ∀ (hact : C.actTime o ≤ T),
      ∀ (hj : rho.events[j]? = some (.tick w T)),
      ∀ (hji : j < i),
      ∀ (hrf : restartFree rho w j i),
        Timely (Run.stateBefore E rho i w) o) := by
  rw [TimelyOfClockStatement]

-- GLY:1177–1180; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def TimelyOfEmitStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
theorem TimelyOfEmitStatement_def :
    TimelyOfEmitStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (ht : 0 ≤ t),
      ∀ (hpub : PublicTime E (C.actTime o)),
      ∀ (hth : C.actTime o ≤ t),
        C.actTime o ≤ pubFloor E t) := by
  rw [TimelyOfEmitStatement]

-- GLY:1181–1185; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def TimelyOfRelayStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
  ∀ (v : V),
  ∀ (i : Nat),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (hacc : Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
theorem TimelyOfRelayStatement_def :
    TimelyOfRelayStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hAS : AdmitSound P C),
      ∀ (hS : ScheduleWellFormed E rho),
      ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
      ∀ (v : V),
      ∀ (i : Nat),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (hacc : Run.acceptsAt E rho i v o t),
        C.actTime o ≤ pubFloor E t) := by
  rw [TimelyOfRelayStatement]

-- GLY:1188–1215; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def AcceptedByDeadlineStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ {Inv : P.State → Prop},
  ∀ (dl : Time → Time),
  ∀ (cut : Time),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (w : V),
  ∀ (hD : DeliveryWithin E rho dl cut),
  ∀ (hT : Trigger E rho o t),
  ∀ (hw : w ∈ rho.honest),
  ∀ (hcut : dl t ≤ cut),
  ∀ (hlt : t < dl t),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (hES : ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.excludes (Run.stateBefore E rho i v) o = true →
      P.excludes (Run.stateBefore E rho j v) o = true),
  ∀ (hPS : ∀ v o i j, i ≤ j → restartFree rho v i j →
      P.processed (Run.stateBefore E rho i v) o = true →
      P.processed (Run.stateBefore E rho j v) o = true),
  ∀ (hReady : ∀ i t', i < Run.idxBefore rho (dl t) → Run.handlesAt E rho i w o t' →
      P.wellFormed o = true ∧ P.depsPresent (Run.stateBefore E rho i w) o = true),
  ∀ (hA : AcceptanceLaw P Timely Inv),
  ∀ (C : TimelyClock P Timely),
  ∀ (hInv : ∀ i, Inv (Run.stateBefore E rho i w)),
  ∀ (hAdm : C.actTime o ≤ pubFloor E t),
  ∀ (j : Nat),
  ∀ (hj : rho.events[j]? = some (.tick w (pubFloor E t))),
  ∀ (hrf : restartFree rho w j (Run.idxBefore rho (dl t))),
  ∀ (hNX : P.excludes (Run.stateBeforeTime E rho (dl t) w) o = false),
    P.processed (Run.stateBeforeTime E rho (dl t) w) o = true

set_option linter.unusedVariables false in
theorem AcceptedByDeadlineStatement_def :
    AcceptedByDeadlineStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ {Inv : P.State → Prop},
      ∀ (dl : Time → Time),
      ∀ (cut : Time),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (w : V),
      ∀ (hD : DeliveryWithin E rho dl cut),
      ∀ (hT : Trigger E rho o t),
      ∀ (hw : w ∈ rho.honest),
      ∀ (hcut : dl t ≤ cut),
      ∀ (hlt : t < dl t),
      ∀ (hS : ScheduleWellFormed E rho),
      ∀ (hES : ∀ v o i j, i ≤ j → restartFree rho v i j →
          P.excludes (Run.stateBefore E rho i v) o = true →
          P.excludes (Run.stateBefore E rho j v) o = true),
      ∀ (hPS : ∀ v o i j, i ≤ j → restartFree rho v i j →
          P.processed (Run.stateBefore E rho i v) o = true →
          P.processed (Run.stateBefore E rho j v) o = true),
      ∀ (hReady : ∀ i t', i < Run.idxBefore rho (dl t) → Run.handlesAt E rho i w o t' →
          P.wellFormed o = true ∧ P.depsPresent (Run.stateBefore E rho i w) o = true),
      ∀ (hA : AcceptanceLaw P Timely Inv),
      ∀ (C : TimelyClock P Timely),
      ∀ (hInv : ∀ i, Inv (Run.stateBefore E rho i w)),
      ∀ (hAdm : C.actTime o ≤ pubFloor E t),
      ∀ (j : Nat),
      ∀ (hj : rho.events[j]? = some (.tick w (pubFloor E t))),
      ∀ (hrf : restartFree rho w j (Run.idxBefore rho (dl t))),
      ∀ (hNX : P.excludes (Run.stateBeforeTime E rho (dl t) w) o = false),
        P.processed (Run.stateBeforeTime E rho (dl t) w) o = true) := by
  rw [AcceptedByDeadlineStatement]

-- GLY:1218–1229; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def FirstAcceptOfProcessedStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
      P.handles (Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t'

set_option linter.unusedVariables false in
theorem FirstAcceptOfProcessedStatement_def :
    FirstAcceptOfProcessedStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (i₀ k : Nat),
      ∀ (hik : i₀ ≤ k),
      ∀ (hrf : restartFree rho w i₀ k),
      ∀ (h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
      ∀ (hk : P.processed (Run.stateBefore E rho k w) o = true),
      ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
          P.processed (Run.stateBefore E rho i w) o = false →
          P.processed (Run.stateBefore E rho (i + 1) w) o = false),
      ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
          P.processed (Run.stateBefore E rho i w) o = false →
          P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
          P.handles (Run.stateBefore E rho i w) o' o),
        ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t') := by
  rw [FirstAcceptOfProcessedStatement]

end AvailableChain.Gen.V2
