# X1c — holder-aware client at actual driver observations

Statement checkpoint on p0-x1c, base dfd8aee727458d2eb852b80b6d72dcdf001809c7.

## Reuse and scope

The accepted `FGHolderClientLaws` in Statements/ExecutionBridges.lean is reused unchanged.
It already binds the injective holder map, both exact duty inputs, non-holder silence,
and durable record changes to the own-write microsteps. No `Fin n ≃ V` is assumed.
X1a supplies the canonical observations, their cut/release laws and ordinary emission
correspondence. X1b supplies history/origin reasoning; none is duplicated here.

New module: `AvailableChainFGCompose.Statements.HolderClient`.
The driver statements bind directly to `driverFGExecutionObs E rho F T Op`.
The row conclusion distinguishes the current release from a strictly prior release and
retains the exact wire. The prior-origin premise is conditional, as in the frozen theorem.
No ordinary-delivery/process correspondence or A13 implementation is introduced.

## Exact statement checkpoint declarations

Inside `AvailableChain.FGCompose`, with `SimplexFG` and `KitFG` open:

```lean
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire Body : Type}
variable (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P)

def obsSafetyInputAt (x : V) (j : Nat) :
    Option (Option (FGBlock (Fin n)) × HeadFields) :=
  match rho.events[j]? with
  | some (.tick y t) =>
    if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
      some (S.inputs (obsDutyState O x j)) else none
  | _ => none

theorem obsSafetyInputAt_def (x : V) (j : Nat) :
    obsSafetyInputAt S E rho O x j =
      (match rho.events[j]? with
      | some (.tick y t) =>
        if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
          some (S.inputs (obsDutyState O x j)) else none
      | _ => none) := rfl

def obsOwnReleasedBefore (x : V) (k : Nat) : List P.Object :=
  (List.range k).flatMap (obsOwnReleased O x)

theorem obsOwnReleasedBefore_def (x : V) (k : Nat) :
    obsOwnReleasedBefore O x k = (List.range k).flatMap (obsOwnReleased O x) := rfl

def obsSafetyNoSlash (x : V) : Prop :=
  ∀ a b, (∃ t, obsEmits O rho x (S.encode a) t) →
    (∃ t, obsEmits O rho x (S.encode b) t) →
    ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v

theorem obsSafetyNoSlash_def (x : V) :
    obsSafetyNoSlash S rho O x =
      (∀ a b, (∃ t, obsEmits O rho x (S.encode a) t) →
        (∃ t, obsEmits O rho x (S.encode b) t) →
        ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v) := rfl

def obsHonestRowAt (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) : Prop :=
  x ∈ rho.honest ∧ rho.events[j]? = some (.tick x (T.action r)) ∧
    S.encode a ∈ O.released x j

theorem obsHonestRowAt_def (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) :
    obsHonestRowAt S rho O T j x r a =
      (x ∈ rho.honest ∧ rho.events[j]? = some (.tick x (T.action r)) ∧
        S.encode a ∈ O.released x j) := rfl

def FGHolderClientTrace (holder : Fin n → V) : Prop :=
  ∀ i, holder i ∈ rho.honest → ∀ k,
    S.record (O.stateBefore k (holder i)) =
      clientRecordOnce Ef cfg i RecordOnce.initial
        ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i))) ∧
    (obsOwnReleasedBefore O (holder i) k).filterMap S.decodeObject =
      clientRunOnce Ef cfg i RecordOnce.initial
        ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i)))

theorem FGHolderClientTrace_def (holder : Fin n → V) :
    FGHolderClientTrace S Ef cfg E rho O holder =
      (∀ i, holder i ∈ rho.honest → ∀ k,
        S.record (O.stateBefore k (holder i)) =
          clientRecordOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i))) ∧
        (obsOwnReleasedBefore O (holder i) k).filterMap S.decodeObject =
          clientRunOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i)))) := rfl

def FGHolderRowCoverage (T : FGTiming) (entry : Wire → Option (Height × BlockId))
    (x : V) (j r : Nat) (target : Height × BlockId) : Prop :=
  (∃ a, obsHonestRowAt S rho O T j x r a ∧ entry a = some target) ∨
    ∃ k rSent a, k < j ∧ rSent ≤ r ∧ obsHonestRowAt S rho O T k x rSent a ∧
      entry a = some target

theorem FGHolderRowCoverage_def (T : FGTiming) (entry : Wire → Option (Height × BlockId))
    (x : V) (j r : Nat) (target : Height × BlockId) :
    FGHolderRowCoverage S rho O T entry x j r target =
      ((∃ a, obsHonestRowAt S rho O T j x r a ∧ entry a = some target) ∨
        ∃ k rSent a, k < j ∧ rSent ≤ r ∧ obsHonestRowAt S rho O T k x rSent a ∧
          entry a = some target) := rfl

variable (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
variable (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
variable (holder : Fin n → V)

def SafetyClientTraceDriverStatement : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
    FGHolderClientTrace S Ef cfg E rho O holder

theorem SafetyClientTraceDriverStatement_def :
    SafetyClientTraceDriverStatement S Ef cfg E rho F T Op holder =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
         FGHolderClientTrace S Ef cfg E rho O holder) := rfl

def SafetyEmittedNoSlashDriverStatement : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
    FGSafetyWireLaws S → ∀ i, holder i ∈ rho.honest → obsSafetyNoSlash S rho O (holder i)

theorem SafetyEmittedNoSlashDriverStatement_def :
    SafetyEmittedNoSlashDriverStatement S Ef cfg E rho F T Op holder =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
         FGSafetyWireLaws S → ∀ i, holder i ∈ rho.honest →
           obsSafetyNoSlash S rho O (holder i)) := rfl

def RowPermissionCoveredDriverStatement (H : FGHeightView (Fin n))
    (timing : FGTiming) (entry : Wire → Option (Height × BlockId)) : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
  FGTimingLaws timing → FGRowPermissionWireLaws S entry → V2.D.ScheduleWellFormed E rho →
  (∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
    ((H C).h, (H C).T_h.root)) →
  ∀ seat j r C, holder seat ∈ rho.honest →
    rho.events[j]? = some (.tick (holder seat) (timing.action r)) →
    FGRowPermissionInputs S H (obsDutyState O (holder seat) j) C →
    FGRowRecordHistory (S.record (obsDutyState O (holder seat) j)) →
    (∀ b ∈ (S.record (O.stateBefore j (holder seat))).sent,
      ∃ k rSent a, k < j ∧ obsHonestRowAt S rho O timing k (holder seat) rSent a ∧
        entry a = namedEntry b.1) →
    E.awake (holder seat) (timing.action r) = true →
    S.enabled (timing.action r) = true →
    FGHolderRowCoverage S rho O timing entry (holder seat) j r ((H C).h, (H C).T_h.root)

theorem RowPermissionCoveredDriverStatement_def (H : FGHeightView (Fin n))
    (timing : FGTiming) (entry : Wire → Option (Height × BlockId)) :
    RowPermissionCoveredDriverStatement S Ef cfg E rho F T Op holder H timing entry =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
       FGTimingLaws timing → FGRowPermissionWireLaws S entry →
       V2.D.ScheduleWellFormed E rho →
       (∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
         ((H C).h, (H C).T_h.root)) →
       ∀ seat j r C, holder seat ∈ rho.honest →
         rho.events[j]? = some (.tick (holder seat) (timing.action r)) →
         FGRowPermissionInputs S H (obsDutyState O (holder seat) j) C →
         FGRowRecordHistory (S.record (obsDutyState O (holder seat) j)) →
         (∀ b ∈ (S.record (O.stateBefore j (holder seat))).sent,
           ∃ k rSent a, k < j ∧ obsHonestRowAt S rho O timing k (holder seat) rSent a ∧
             entry a = namedEntry b.1) →
         E.awake (holder seat) (timing.action r) = true →
         S.enabled (timing.action r) = true →
         FGHolderRowCoverage S rho O timing entry (holder seat) j r
           ((H C).h, (H C).T_h.root)) := rfl
```

## Planned proof and ordinary bridges

- `safety_client_trace_driver`: `SafetyClientTraceDriverStatement` above.
- `safety_emitted_noSlash_driver`: `SafetyEmittedNoSlashDriverStatement` above.
- `rowPermission_covered_driver`: `RowPermissionCoveredDriverStatement` above.
- Ordinary input, record and release correspondence: equality.
- Ordinary no-slash and honest-row predicates: iff.
- Frozen global client laws plus an explicit bijection imply the ordinary holder laws:
  one-way; the run-local law cannot recover global off-run laws.
- Current/prior ordinary coverage implies the frozen existential coverage conclusion:
  one-way; the latter forgets the strict earlier-index/current-index split.

## PC E1F/E2 producers

E1F must produce `FGExecutionObsLaws` and the accepted `FGHolderClientLaws` on the
canonical driver trace and operations, including raw restore, reconstruct/replay/rebuild,
both drains and exact own writes. E2 must bind holder assignment, actual enabled gates,
and both selection inputs to those same observations. No-slash also needs the existing
`FGSafetyWireLaws`. Coverage needs timing/schedule, the exact wire decoder, height-view
agreement, duty permission, durable sent-key history and exact earlier wire origins.

## Checks

Statement module: `lake build --wfail AvailableChainFGCompose.Statements.HolderClient`.
Proofs, controls and central acceptance are not yet complete.
