module
public import AvailableChainEngineV2.Engine.Duty.Run
public import AvailableChainEngineV2.Conditions.Duty.Schedule
public import AvailableChainKitV2.DutyClockLaws
public import AvailableChainGeneric.Statements.V2.Duty.Reads

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: Conditions.lean:114,122; same: Same emission or acceptance; GLY r3.19 S112.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:21.
def Trigger (E : Generic.Env V) (rho : D.Run V P) (o : P.Object) (t : Time) : Prop :=
  (∃ v ∈ rho.honest, D.Run.emits E rho v o t) ∨
  (∃ v ∈ rho.honest, ∃ i, D.Run.acceptsAt E rho i v o t)

-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:26.
theorem Trigger_def (E : Generic.Env V) (rho : D.Run V P) (o : P.Object) (t : Time) :
    Trigger E rho o t =
      ((∃ v ∈ rho.honest, D.Run.emits E rho v o t) ∨
        (∃ v ∈ rho.honest, ∃ i, D.Run.acceptsAt E rho i v o t)) := rfl

-- DC: Conditions.lean:110,134; INTENTIONAL: One record for both regimes; GLY r3.19 S113.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:34.
structure DeliveryWithin (E : Generic.Env V) (rho : D.Run V P)
    (dl : Time → Time) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, D.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    dl t ≤ cut → P.excludes (D.Run.stateBeforeTime E rho (dl t) w) o = false →
    ∃ t', t ≤ t' ∧ t' < dl t ∧ ∃ j, D.Run.handlesAt E rho j w o t'
  relay : ∀ v ∈ rho.honest, ∀ i o t, D.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    P.processed (D.Run.stateBefore E rho (i + 1) w) o = false →
    dl t ≤ cut → P.excludes (D.Run.stateBeforeTime E rho (dl t) w) o = false →
    ∃ t', t ≤ t' ∧ t' < dl t ∧ ∃ j, D.Run.handlesAt E rho j w o t'

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:48.
structure TimelyClock (P : ProtocolSpecD In) (Timely : P.State → P.Object → Prop) where
  actTime : P.Object → Time
  clockOf : P.State → Time
  timely_iff : ∀ st o, Timely st o ↔ actTime o ≤ clockOf st
  clock : ClockLaws P
  clockOf_eq : ∀ st, clockOf st = clock.now st

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:56.
structure AcceptanceLaw (P : ProtocolSpecD In) (Timely : P.State → P.Object → Prop)
    (Inv : P.State → Prop) : Prop where
  accepts : ∀ st o' o, Inv st → P.handles st o' o → P.wellFormed o = true →
    P.depsPresent st o = true → Timely st o →
    P.processed (P.process st o') o = true ∨ P.excludes (P.process st o') o = true

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:65.
structure AdmitSound (P : ProtocolSpecD In) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) : Prop where
  timely : ∀ st o' o, 0 ≤ C.clockOf st → P.processed st o = false →
    P.processed (P.process st o') o = true → P.handles st o' o → Timely st o

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:79.
def TimelyOfClockStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (T : Time),
  ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : D.restartFree rho w j i),
    Timely (D.Run.stateBefore E rho i w) o

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:96.
theorem TimelyOfClockStatement_def :
    TimelyOfClockStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hS : D.ScheduleWellFormed E rho),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (T : Time),
      ∀ (j i : Nat),
      ∀ (hact : C.actTime o ≤ T),
      ∀ (hj : rho.events[j]? = some (.tick w T)),
      ∀ (hji : j < i),
      ∀ (hrf : D.restartFree rho w j i),
        Timely (D.Run.stateBefore E rho i w) o) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:116.
def TimelyOfEmitStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : V2.PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:129.
theorem TimelyOfEmitStatement_def :
    TimelyOfEmitStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (ht : 0 ≤ t),
      ∀ (hpub : V2.PublicTime E (C.actTime o)),
      ∀ (hth : C.actTime o ≤ t),
        C.actTime o ≤ pubFloor E t) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:145.
def TimelyOfRelayStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
  ∀ (v : V),
  ∀ (i : Nat),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (hacc : D.Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:161.
theorem TimelyOfRelayStatement_def :
    TimelyOfRelayStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hAS : AdmitSound P C),
      ∀ (hS : D.ScheduleWellFormed E rho),
      ∀ (hrestore : ∀ d, C.clock.now (P.restore d) = 0),
      ∀ (v : V),
      ∀ (i : Nat),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (hacc : D.Run.acceptsAt E rho i v o t),
        C.actTime o ≤ pubFloor E t) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:180.
def AcceptedByDeadlineStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
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
    P.processed (D.Run.stateBeforeTime E rho (dl t) w) o = true

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:215.
theorem AcceptedByDeadlineStatement_def :
    AcceptedByDeadlineStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
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
        P.processed (D.Run.stateBeforeTime E rho (dl t) w) o = true) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:253.
def FirstAcceptOfProcessedStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (i₀ k : Nat),
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
    ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t'

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:273.
theorem FirstAcceptOfProcessedStatement_def :
    FirstAcceptOfProcessedStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (i₀ k : Nat),
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
        ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t') := rfl

end AvailableChain.Gen.V2.Duty
