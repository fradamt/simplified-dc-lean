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

## Proved exports and ordinary bridges

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
The touched library and tests build with `--wfail`; all 34 new public names and the
control results have only `propext`, `Classical.choice`, and `Quot.sound`.
Shake reports 0 NEW. Final revision-stamped acceptance results, command lines, exit codes,
environment and log hashes are recorded in `.lake/x1c/manifest.txt`.

## Controls

All are **driver-interface executions**, not concrete PC or `ValidDriverPrefix` fixtures.
They use `driverFGExecutionObs` of one exact executable driver/run, one FG seat and two
honest runtime nodes. Events are holder tick 6, holder restart 14, holder tick 14, and
non-holder tick 15. The horizon is 20, strictly beyond the control deadline 16 and every
event. The source is genesis and its fresh row is nonempty, signed, decoded and enabled.
The canonical drained duty, own writes and both completion states satisfy all observation
and holder laws. There are no deliveries and no ordinary-driver delivery assumption.

| Control | Exact premise witness | Inspected result |
|---|---|---|
| Non-holder | `nonholder_premises_sat` | `nonholder_no_fg_release`: awake node 1 releases no FG row |
| Extra node | `extra_node_premises_sat` | `extra_node_no_slash`: driver no-slash applies despite a node outside the holder image |
| Restart | `restart_premises_sat` | `restart_own_record_survives`: raw restore and later prefix keep the full sent record; trace has exactly the original row |
| Wrong finality input | `wrong_finality_premises_sat` | `wrong_finality_rejected`: same source, different second input, actual nonempty release contradicts the altered holder law |
| Current coverage | `current_coverage_premises_sat` | `current_coverage`: apply the driver consumer, rule out a prior index, inspect the exact wire |
| Prior coverage | `prior_coverage_premises_sat` | `prior_coverage`: apply the driver consumer after restart, rule out a current release, inspect the original wire |

Each listed name is private in `AvailableChainFGCompose.Tests.X1c` and is axiom-audited
there. `common_premises_sat` also proves the nonempty holder reader scope, honest set,
full schedule, timing and both wire-law records on the same run. The coverage fixtures
prove the conditional earlier-origin leaf; they do not assume the coverage conclusion.

## Central entries and import edges

- Checker registration commit `b8a683ab` adds exactly the facade's three new targets in
  `scripts/check-layers.py` and `scripts/CheckFGAxioms.lean`:
  `Statements.HolderClient`, `Proofs.HolderClient`, `Proofs.OrdinaryHolderClient`.
  No checker logic, baseline or previously accepted edge changes.
- Facade, Tests/Axioms (34 names), source inventory, proof-audit coverage, laneUpstream,
  development scope and `scripts/dev-pkg/X1c.txt` (6 targets) are registered.
- Snapshot comparison against dfd8aee7: all old roots/nodes exact; +34 roots and +37 nodes.
  Snapshot and coverage preserve existing ordering/text; the snapshot has no removed lines.
- New proof imports remain inside Compose. The ordinary bridge keeps the existing
  SafetyClient import as the policy-compliant supplier of ordinary record-fold reasoning.
- No accepted declaration, FG-SA claim, CONTRACT, frozen manifest, or baseline changes.

## Exact compiled public signatures

This is the successful Lean `#check` output for all 34 new public names. The ordinary
trace iff is explicitly restricted to honest holders, matching the new driver consumer.
The no-slash iff is predicate equality for any selected node. The row bridge is one-way
because the frozen conclusion forgets current/prior event-index information.

```text
AvailableChain.FGCompose.obsSafetyInputAt {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V] {n : ℕ}
  {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (E : AvailableChain.Generic.Env V)
  (rho : AvailableChain.V2.D.Run V P) (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) (j : ℕ) :
  Option (Option (AvailableChain.SimplexFG.FGBlock (Fin n)) × AvailableChain.SimplexFG.HeadFields)
AvailableChain.FGCompose.obsSafetyInputAt_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (E : AvailableChain.Generic.Env V)
  (rho : AvailableChain.V2.D.Run V P) (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) (j : ℕ) :
  AvailableChain.FGCompose.obsSafetyInputAt S E rho O x j =
    match rho.events[j]? with
    | some (AvailableChain.V2.Event.tick y t) =>
      if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
        some (S.inputs (AvailableChain.FGCompose.obsDutyState O x j))
      else none
    | x => none
AvailableChain.FGCompose.obsOwnReleasedBefore {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) (k : ℕ) : List P.Object
AvailableChain.FGCompose.obsOwnReleasedBefore_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) (k : ℕ) :
  AvailableChain.FGCompose.obsOwnReleasedBefore O x k =
    List.flatMap (AvailableChain.FGCompose.obsOwnReleased O x) (List.range k)
AvailableChain.FGCompose.obsSafetyNoSlash {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ} {Wire : Type}
  (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) : Prop
AvailableChain.FGCompose.obsSafetyNoSlash_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ}
  {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (x : V) :
  AvailableChain.FGCompose.obsSafetyNoSlash S rho O x =
    ∀ (a b : Wire),
      (∃ t, AvailableChain.FGCompose.obsEmits O rho x (S.encode a) t) →
        (∃ t, AvailableChain.FGCompose.obsEmits O rho x (S.encode b) t) →
          ∀ (u v : AvailableChain.SimplexFG.Row (Fin n)),
            S.decode a = some u → S.decode b = some v → ¬AvailableChain.SimplexFG.Slashable u v
AvailableChain.FGCompose.obsHonestRowAt {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ} {Wire : Type}
  (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (T : AvailableChain.FGCompose.FGTiming) (j : ℕ) (x : V) (r : ℕ)
  (a : Wire) : Prop
AvailableChain.FGCompose.obsHonestRowAt_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ} {Wire : Type}
  (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (T : AvailableChain.FGCompose.FGTiming) (j : ℕ) (x : V) (r : ℕ)
  (a : Wire) :
  AvailableChain.FGCompose.obsHonestRowAt S rho O T j x r a =
    (x ∈ rho.honest ∧ rho.events[j]? = some (AvailableChain.V2.Event.tick x (T.action r)) ∧ S.encode a ∈ O.released x j)
AvailableChain.FGCompose.FGHolderClientTrace {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (holder : Fin n → V) : Prop
AvailableChain.FGCompose.FGHolderClientTrace_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (holder : Fin n → V) :
  AvailableChain.FGCompose.FGHolderClientTrace S Ef cfg E rho O holder =
    ∀ (i : Fin n),
      holder i ∈ rho.honest →
        ∀ (k : ℕ),
          S.record (O.stateBefore k (holder i)) =
              AvailableChain.SimplexFG.clientRecordOnce Ef cfg i AvailableChain.SimplexFG.RecordOnce.initial
                (List.filterMap (AvailableChain.FGCompose.obsSafetyInputAt S E rho O (holder i)) (List.range k)) ∧
            List.filterMap S.decodeObject (AvailableChain.FGCompose.obsOwnReleasedBefore O (holder i) k) =
              AvailableChain.SimplexFG.clientRunOnce Ef cfg i AvailableChain.SimplexFG.RecordOnce.initial
                (List.filterMap (AvailableChain.FGCompose.obsSafetyInputAt S E rho O (holder i)) (List.range k))
AvailableChain.FGCompose.FGHolderRowCoverage {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ}
  {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (T : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) (x : V) (j r : ℕ)
  (target : AvailableChain.SimplexFG.Height × AvailableChain.BlockId) : Prop
AvailableChain.FGCompose.FGHolderRowCoverage_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} {n : ℕ}
  {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) (T : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) (x : V) (j r : ℕ)
  (target : AvailableChain.SimplexFG.Height × AvailableChain.BlockId) :
  AvailableChain.FGCompose.FGHolderRowCoverage S rho O T entry x j r target =
    ((∃ a, AvailableChain.FGCompose.obsHonestRowAt S rho O T j x r a ∧ entry a = some target) ∨
      ∃ k rSent a,
        k < j ∧ rSent ≤ r ∧ AvailableChain.FGCompose.obsHonestRowAt S rho O T k x rSent a ∧ entry a = some target)
AvailableChain.FGCompose.SafetyClientTraceDriverStatement {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) : Prop
AvailableChain.FGCompose.SafetyClientTraceDriverStatement_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) :
  AvailableChain.FGCompose.SafetyClientTraceDriverStatement S Ef cfg E rho F T Op holder =
    have O := AvailableChain.FGCompose.driverFGExecutionObs E rho F T Op;
    AvailableChain.FGCompose.FGExecutionObsLaws E rho O →
      AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder →
        AvailableChain.FGCompose.FGHolderClientTrace S Ef cfg E rho O holder
AvailableChain.FGCompose.SafetyEmittedNoSlashDriverStatement {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) : Prop
AvailableChain.FGCompose.SafetyEmittedNoSlashDriverStatement_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) :
  AvailableChain.FGCompose.SafetyEmittedNoSlashDriverStatement S Ef cfg E rho F T Op holder =
    have O := AvailableChain.FGCompose.driverFGExecutionObs E rho F T Op;
    AvailableChain.FGCompose.FGExecutionObsLaws E rho O →
      AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder →
        AvailableChain.FGCompose.FGSafetyWireLaws S →
          ∀ (i : Fin n), holder i ∈ rho.honest → AvailableChain.FGCompose.obsSafetyNoSlash S rho O (holder i)
AvailableChain.FGCompose.RowPermissionCoveredDriverStatement {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) (H : AvailableChain.KitFG.FGHeightView (Fin n)) (timing : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) : Prop
AvailableChain.FGCompose.RowPermissionCoveredDriverStatement_def {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (holder : Fin n → V) (H : AvailableChain.KitFG.FGHeightView (Fin n)) (timing : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) :
  AvailableChain.FGCompose.RowPermissionCoveredDriverStatement S Ef cfg E rho F T Op holder H timing entry =
    have O := AvailableChain.FGCompose.driverFGExecutionObs E rho F T Op;
    AvailableChain.FGCompose.FGExecutionObsLaws E rho O →
      AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder →
        AvailableChain.FGCompose.FGTimingLaws timing →
          AvailableChain.FGCompose.FGRowPermissionWireLaws S entry →
            AvailableChain.V2.D.ScheduleWellFormed E rho →
              (∀ (C : AvailableChain.SimplexFG.FGBlock (Fin n)),
                  ((AvailableChain.SimplexFG.derive Ef cfg C).h, (AvailableChain.SimplexFG.derive Ef cfg C).T_h.root) =
                    ((H C).h, (H C).T_h.root)) →
                ∀ (seat : Fin n) (j r : ℕ) (C : AvailableChain.SimplexFG.FGBlock (Fin n)),
                  holder seat ∈ rho.honest →
                    rho.events[j]? = some (AvailableChain.V2.Event.tick (holder seat) (timing.action r)) →
                      AvailableChain.FGCompose.FGRowPermissionInputs S H
                          (AvailableChain.FGCompose.obsDutyState O (holder seat) j) C →
                        AvailableChain.FGCompose.FGRowRecordHistory
                            (S.record (AvailableChain.FGCompose.obsDutyState O (holder seat) j)) →
                          (∀ b ∈ (S.record (O.stateBefore j (holder seat))).sent,
                              ∃ k rSent a,
                                k < j ∧
                                  AvailableChain.FGCompose.obsHonestRowAt S rho O timing k (holder seat) rSent a ∧
                                    entry a = AvailableChain.FGCompose.namedEntry b.1) →
                            E.awake (holder seat) (timing.action r) = true →
                              S.enabled (timing.action r) = true →
                                AvailableChain.FGCompose.FGHolderRowCoverage S rho O timing entry (holder seat) j r
                                  ((H C).h, (H C).T_h.root)
AvailableChain.FGCompose.holder_record_at_duty {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) {holder : Fin n → V}
  (EL : AvailableChain.FGCompose.FGExecutionObsLaws E rho O)
  (J : AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder) {x : V} {j : ℕ} {t : AvailableChain.Time}
  (he : rho.events[j]? = some (AvailableChain.V2.Event.tick x t)) :
  S.record (AvailableChain.FGCompose.obsDutyState O x j) = S.record (O.stateBefore j x)
AvailableChain.FGCompose.safety_client_trace_obs {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) {holder : Fin n → V}
  (EL : AvailableChain.FGCompose.FGExecutionObsLaws E rho O)
  (J : AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder) :
  AvailableChain.FGCompose.FGHolderClientTrace S Ef cfg E rho O holder
AvailableChain.FGCompose.safety_client_trace_driver {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) {holder : Fin n → V}
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object) :
  AvailableChain.FGCompose.SafetyClientTraceDriverStatement S Ef cfg E rho F T Op holder
AvailableChain.FGCompose.safety_emitted_noSlash_obs {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) {holder : Fin n → V}
  (EL : AvailableChain.FGCompose.FGExecutionObsLaws E rho O)
  (J : AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder)
  (W : AvailableChain.FGCompose.FGSafetyWireLaws S) (i : Fin n) (hi : holder i ∈ rho.honest) :
  AvailableChain.FGCompose.obsSafetyNoSlash S rho O (holder i)
AvailableChain.FGCompose.safety_emitted_noSlash_driver {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) {holder : Fin n → V}
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object) :
  AvailableChain.FGCompose.SafetyEmittedNoSlashDriverStatement S Ef cfg E rho F T Op holder
AvailableChain.FGCompose.rowPermission_covered_obs {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (O : AvailableChain.FGCompose.FGExecutionObs V P) {holder : Fin n → V}
  (EL : AvailableChain.FGCompose.FGExecutionObsLaws E rho O)
  (J : AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho O holder)
  (H : AvailableChain.KitFG.FGHeightView (Fin n)) (timing : AvailableChain.FGCompose.FGTiming)
  (hT : AvailableChain.FGCompose.FGTimingLaws timing)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId))
  (W : AvailableChain.FGCompose.FGRowPermissionWireLaws S entry) (hs : AvailableChain.V2.D.ScheduleWellFormed E rho)
  (hheight :
    ∀ (C : AvailableChain.SimplexFG.FGBlock (Fin n)),
      ((AvailableChain.SimplexFG.derive Ef cfg C).h, (AvailableChain.SimplexFG.derive Ef cfg C).T_h.root) =
        ((H C).h, (H C).T_h.root))
  (j r : ℕ) (i : Fin n) (hi : holder i ∈ rho.honest)
  (htick : rho.events[j]? = some (AvailableChain.V2.Event.tick (holder i) (timing.action r)))
  (C : AvailableChain.SimplexFG.FGBlock (Fin n))
  (hperm : AvailableChain.FGCompose.FGRowPermissionInputs S H (AvailableChain.FGCompose.obsDutyState O (holder i) j) C)
  (hhist :
    AvailableChain.FGCompose.FGRowRecordHistory (S.record (AvailableChain.FGCompose.obsDutyState O (holder i) j)))
  (horigin :
    ∀ b ∈ (S.record (O.stateBefore j (holder i))).sent,
      ∃ k rSent a,
        k < j ∧
          AvailableChain.FGCompose.obsHonestRowAt S rho O timing k (holder i) rSent a ∧
            entry a = AvailableChain.FGCompose.namedEntry b.1)
  (hawake : E.awake (holder i) (timing.action r) = true) (henabled : S.enabled (timing.action r) = true) :
  AvailableChain.FGCompose.FGHolderRowCoverage S rho O timing entry (holder i) j r ((H C).h, (H C).T_h.root)
AvailableChain.FGCompose.rowPermission_covered_driver {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire Body : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) {holder : Fin n → V}
  (F : AvailableChain.FGCompose.FGDependencyDriver V Body P)
  (T : V → AvailableChain.FGCompose.FGDependencyTrace P.State)
  (Op :
    V →
      ℕ →
        AvailableChain.FGCompose.FGDependencyOperation Body (AvailableChain.FGCompose.FGReceiptToken V P.Object)
          P.Object)
  (H : AvailableChain.KitFG.FGHeightView (Fin n)) (timing : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) :
  AvailableChain.FGCompose.RowPermissionCoveredDriverStatement S Ef cfg E rho F T Op holder H timing entry
AvailableChain.FGCompose.ordinary_obsDutyState_tick {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) {x : V} {j : ℕ}
  {t : AvailableChain.Time} (he : rho.events[j]? = some (AvailableChain.V2.Event.tick x t)) :
  AvailableChain.FGCompose.obsDutyState (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) x j =
    P.clock (AvailableChain.V2.D.Run.stateBefore E rho j x) t
AvailableChain.FGCompose.ordinary_obsSafetyInputAt {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (x : V) (j : ℕ) :
  AvailableChain.FGCompose.obsSafetyInputAt S E rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) x j =
    AvailableChain.FGCompose.safetyInputAt S E rho x j
AvailableChain.FGCompose.ordinary_obsOwnReleased {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In} [DecidableEq V]
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (x : V) (j : ℕ) :
  AvailableChain.FGCompose.obsOwnReleased (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) x j =
    AvailableChain.V2.D.Engine.ownReleasedAt E rho x j
AvailableChain.FGCompose.ordinary_obsOwnReleasedBefore {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (x : V) (k : ℕ) :
  AvailableChain.FGCompose.obsOwnReleasedBefore (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) x k =
    AvailableChain.V2.D.Engine.ownReleased E rho x 0 k
AvailableChain.FGCompose.ordinary_obsSafetyNoSlash_iff {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (x : V) :
  AvailableChain.FGCompose.obsSafetyNoSlash S rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) x ↔
    AvailableChain.FGCompose.safetyNoSlash S E rho x
AvailableChain.FGCompose.ordinary_obsHonestRowAt_iff {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (T : AvailableChain.FGCompose.FGTiming) (j : ℕ)
  (x : V) (r : ℕ) (a : Wire) :
  AvailableChain.FGCompose.obsHonestRowAt S rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) T j x r a ↔
    AvailableChain.FGCompose.HonestRowAt S E rho T j x r a
AvailableChain.FGCompose.ordinary_FGHolderClientTrace_iff {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (holder : Fin n → V) :
  AvailableChain.FGCompose.FGHolderClientTrace S Ef cfg E rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho)
      holder ↔
    ∀ (i : Fin n),
      holder i ∈ rho.honest →
        ∀ (k : ℕ),
          S.record (AvailableChain.V2.D.Run.stateBefore E rho k (holder i)) =
              AvailableChain.SimplexFG.clientRecordOnce Ef cfg i AvailableChain.SimplexFG.RecordOnce.initial
                (List.filterMap (AvailableChain.FGCompose.safetyInputAt S E rho (holder i)) (List.range k)) ∧
            List.filterMap S.decodeObject (AvailableChain.V2.D.Engine.ownReleased E rho (holder i) 0 k) =
              AvailableChain.SimplexFG.clientRunOnce Ef cfg i AvailableChain.SimplexFG.RecordOnce.initial
                (List.filterMap (AvailableChain.FGCompose.safetyInputAt S E rho (holder i)) (List.range k))
AvailableChain.FGCompose.ordinary_rowPermission_covered {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P) (T : AvailableChain.FGCompose.FGTiming)
  (entry : Wire → Option (AvailableChain.SimplexFG.Height × AvailableChain.BlockId)) (x : V) (j r : ℕ)
  (target : AvailableChain.SimplexFG.Height × AvailableChain.BlockId)
  (h :
    AvailableChain.FGCompose.FGHolderRowCoverage S rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) T entry x
      j r target) :
  ∃ k rSent a, rSent ≤ r ∧ AvailableChain.FGCompose.HonestRowAt S E rho T k x rSent a ∧ entry a = some target
AvailableChain.FGCompose.ordinary_FGHolderClientLaws {In V : Type} {P : AvailableChain.V2.ProtocolSpecD In}
  [DecidableEq V] {n : ℕ} {Wire : Type} (S : AvailableChain.FGCompose.FGSafetyReads P n Wire)
  (Ef : AvailableChain.SimplexFG.Electorate (Fin n)) (cfg : AvailableChain.SimplexFG.FGConfig)
  (E : AvailableChain.Generic.Env V) (rho : AvailableChain.V2.D.Run V P)
  (J : AvailableChain.FGCompose.FGSafetyClientLaws S Ef cfg) (e : Fin n ≃ V)
  (he : ∀ (i : Fin n), rho.seatOf S.fgLabel (S.fgSeats i) = e i) :
  AvailableChain.FGCompose.FGHolderClientLaws S Ef cfg E rho (AvailableChain.FGCompose.ordinaryFGExecutionObs E rho) ⇑e
```


## Acceptance iteration

The first precheck found F-13 short-name collisions in the new private helpers
`client_step` and `emitted_mem`. They are now `holder_client_step` and
`holder_emitted_mem`; no public type changed. The first DCK run had passed all 76 strict
axiom audits. The final suite is rerun at the corrected committed revision, and the earlier
manifest and failing precheck logs are retained under `.lake/x1c/`.

The first whole-tree CheckProofEqns run detected 24 lazy imported equation exports from
simplification in the two new proof modules. Explicit `_def` equations, case lemmas and
private ordinary-cut reductions replace those simplifications. The resulting whole-tree
preflight passes: 924 proof modules, 1033 exports, 0 unaccepted. No baseline or public
signature changed. The final acceptance suite runs on the committed proof-only fix.
