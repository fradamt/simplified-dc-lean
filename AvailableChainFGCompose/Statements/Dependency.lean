module
public import AvailableChainFGCompose.Statements.HistoricalReads

@[expose] public section

namespace AvailableChain.FGCompose

inductive FGDependencyOutcome where
  | accepted | definitiveRefused | pending | duplicate | future | invalid
  deriving DecidableEq

inductive FGDependencyStepKind where
  | arrival | leafRetry | refusalPropagation | notification
  | ordinary | ownRecord | clock | restore
  deriving DecidableEq

/-- Body identity comes from the cumulative historical store, never a frame. -/
structure FGDependencyReads (State Body Origin Latest : Type) where
  accepted : State → Body → Prop
  refused : State → Body → BlockId → BlockId → Prop
  pending : State → Body → Origin → Prop
  originAvailable : State → Body → Origin → Prop
  validBody : Body → Prop
  priorChecks : State → Body → Prop
  timely : State → Body → Prop
  conflictsFinal : State → Body → Prop
  latest : State → Latest
  notified : State → Body → Prop
  matching : Latest → Body → Prop
  companionHeld : Latest → Body → Prop

variable {State Body Origin Latest V : Type}

def dependencyRefused (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) (b : Body) : Prop :=
  D.refused st b (H.root b) (H.root (H.parent b))

def dependencyResolved (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) (b : Body) : Prop :=
  D.accepted st b ∨ dependencyRefused H D st b

def Effect (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (st : State) (b : Body) (o : Origin) : Prop :=
  D.originAvailable st b o ∧ (D.pending st b o ∨ dependencyResolved H D st b)

/-- The witness relation is supplied by a one-body handler, not by metadata work. -/
structure FGDependencyLeaf (State Body Origin : Type) where
  step : State → Body → Origin → FGDependencyOutcome → State → Prop
  callback : State → Body → Origin → State → Prop
  report : State → Body → Origin → State → Prop
  initial : State
  genesis : Body

/-- Refusal evidence has an authenticated chain ending at a direct leaf refusal. -/
inductive FGDependencyRefusalEvidence (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin) : Body → Prop
  | direct (st st' b o) : D.validBody b → D.priorChecks st b →
      D.accepted st (H.parent b) → D.conflictsFinal st b →
      L.step st b o .definitiveRefused st' → FGDependencyRefusalEvidence H D L b
  | inherited (b) : D.validBody b → FGDependencyRefusalEvidence H D L (H.parent b) →
      FGDependencyRefusalEvidence H D L b

structure FGDependencyStateLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin) : Prop where
  accepted_domain : ∀ st b, D.accepted st b ↔ b ∈ H.acceptedBodies st
  accepted_refused_disjoint : ∀ st b, D.validBody b →
    D.accepted st b → ¬ dependencyRefused H D st b
  pending_valid : ∀ st b o, D.pending st b o → D.validBody b ∧ D.originAvailable st b o
  refused_valid : ∀ st b r pr, D.refused st b r pr → ∃ o,
    D.validBody b ∧ H.root b = r ∧ H.root (H.parent b) = pr ∧
    D.originAvailable st b o ∧ FGDependencyRefusalEvidence H D L b
  genesis_accepted : D.accepted L.initial L.genesis
  initial_pending : ∀ b o, ¬ D.pending L.initial b o
  initial_refused : ∀ b r pr, ¬ D.refused L.initial b r pr
  accepted_leaf : ∀ st b, D.accepted st b → b ≠ L.genesis → ∃ a z o,
    L.step a b o .accepted z ∧ ¬ D.accepted a b ∧ D.accepted z b ∧
    D.originAvailable st b o

structure FGDependencyStepLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin)
    (Step : FGDependencyStepKind → V → State → State → Prop)
    (restore : State → Time → State) (emitsSigning : State → State → Prop) : Prop where
  accepted_keep : ∀ k x st st' b, Step k x st st' → D.accepted st b → D.accepted st' b
  refused_keep : ∀ k x st st' b r pr, Step k x st st' →
    D.refused st b r pr → D.refused st' b r pr
  pending_effect : ∀ k x st st' b o, Step k x st st' → D.pending st b o → Effect H D st' b o
  origin_keep : ∀ k x st st' b o, Step k x st st' →
    D.originAvailable st b o → D.originAvailable st' b o
  metadata_fg_eq : ∀ k x st st', Step k x st st' →
    k ≠ .arrival → k ≠ .leafRetry → H.acceptedBlocks st' = H.acceptedBlocks st
  insertion_leaf : ∀ k x st st' b, Step k x st st' →
    D.accepted st' b → ¬ D.accepted st b → ∃ o, L.step st b o .accepted st'
  one_body : ∀ st st' b o result, L.step st b o result st' →
    ∀ c, D.accepted st' c → D.accepted st c ∨ (c = b ∧ result = .accepted)
  restore_exact : ∀ st t,
    H.acceptedBlocks (restore st t) = H.acceptedBlocks st ∧
    H.acceptedBodies (restore st t) = H.acceptedBodies st ∧
    (∀ b r pr, D.refused (restore st t) b r pr ↔ D.refused st b r pr) ∧
    (∀ b o, D.pending (restore st t) b o ↔ D.pending st b o) ∧
    (∀ b o, D.originAvailable (restore st t) b o ↔ D.originAvailable st b o)
  no_signing : ∀ k x st st', Step k x st st' → ¬ emitsSigning st st'

structure FGDependencyArrivalLeafLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (L : FGDependencyLeaf State Body Origin)
    (Arrival : State → Body → Origin → State → Prop)
    (Notify : State → Body → State → Prop) : Prop where
  direct_refusal_iff : ∀ st b o st', L.step st b o .definitiveRefused st' ↔
    D.validBody b ∧ D.priorChecks st b ∧ D.timely st b ∧ ¬ D.accepted st b ∧
    D.accepted st (H.parent b) ∧ D.conflictsFinal st b ∧
    dependencyRefused H D st' b ∧ D.originAvailable st' b o ∧ L.report st b o st'
  arrival_inherits : ∀ st st' b o, Arrival st b o st' → D.validBody b →
    dependencyRefused H D st (H.parent b) →
    dependencyRefused H D st' b ∧ D.originAvailable st' b o ∧ L.report st b o st'
  arrival_pending : ∀ st st' b o, Arrival st b o st' → D.validBody b → D.timely st b →
    ¬ D.accepted st b → ¬ D.accepted st (H.parent b) →
    ¬ dependencyRefused H D st (H.parent b) → ¬ dependencyRefused H D st b →
    D.pending st' b o
  held_parent_accepts : ∀ st st' b o, L.step st b o .accepted st' ↔
    D.validBody b ∧ D.priorChecks st b ∧ D.timely st b ∧ ¬ D.accepted st b ∧
    D.accepted st (H.parent b) ∧ ¬ D.conflictsFinal st b ∧ D.accepted st' b ∧
    D.originAvailable st' b o ∧ H.erase b ∈ H.acceptedBlocks st'
  accepted_callback : ∀ st st' b o, L.step st b o .accepted st' → L.callback st b o st'
  callback_only : ∀ st st' b o, L.callback st b o st' →
    L.step st b o .accepted st' ∧ ¬ D.accepted st b ∧ ¬ dependencyRefused H D st' b
  refusal_report : ∀ st st' b o, L.report st b o st' →
    dependencyRefused H D st' b ∧ ¬ D.accepted st' b
  rejected_no_refusal : ∀ st st' b o result, L.step st b o result st' →
    (result = .invalid ∨ result = .future ∨ result = .duplicate ∨ result = .pending) →
    dependencyRefused H D st' b → dependencyRefused H D st b
  callback_latest : ∀ st st' b, Notify st b st' → D.accepted st b →
    D.notified st' b ∧
    (∀ c, D.matching (D.latest st) c → c = b → D.companionHeld (D.latest st') c) ∧
    (∀ c, c ≠ b → (D.companionHeld (D.latest st') c ↔ D.companionHeld (D.latest st) c))

/-- Enabled work is fixed by retained inputs and outcomes. It is not a queue flag. -/
inductive FGDependencyEnabled (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) : Prop
  | inherit (b o) : D.pending st b o → dependencyRefused H D st (H.parent b) →
      ¬ dependencyResolved H D st b → FGDependencyEnabled H D st
  | retry (b o) : D.pending st b o → D.validBody b → D.priorChecks st b →
      D.timely st b → D.accepted st (H.parent b) → ¬ dependencyResolved H D st b →
      FGDependencyEnabled H D st
  | notify (b) : dependencyResolved H D st b → ¬ D.notified st b →
      FGDependencyEnabled H D st
  | companion (b) : D.accepted st b → D.matching (D.latest st) b →
      ¬ D.companionHeld (D.latest st) b → FGDependencyEnabled H D st

def dependencyClosed (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest) (st : State) : Prop :=
  ¬ FGDependencyEnabled H D st

/-- Every boundary in a finite segment is a typed transition. -/
inductive FGDependencySteps
    (Step : FGDependencyStepKind → V → State → State → Prop) (x : V) : State → State → Prop
  | refl (st) : FGDependencySteps Step x st st
  | tail {a b c} (k) : FGDependencySteps Step x a b → Step k x b c →
      FGDependencySteps Step x a c

structure FGDependencyReadClosureLaws (H : FGHistoricalReads State Body)
    (D : FGDependencyReads State Body Origin Latest)
    (Step : FGDependencyStepKind → V → State → State → Prop)
    (Read : V → Nat → State → Prop) : Prop where
  read_closed : ∀ x i st, Read x i st → dependencyClosed H D st
  finite_completion : ∀ x i st, Read x i st → ∃ entry,
    FGDependencySteps Step x entry st ∧ dependencyClosed H D st

/-- A finite named parent path, with genesis as its held base. -/
inductive FGDependencyPath (H : FGHistoricalReads State Body) (genesis : Body) :
    Body → List Body → Prop
  | root : FGDependencyPath H genesis genesis []
  | snoc {parent b path} : FGDependencyPath H genesis parent path → H.parent b = parent →
      FGDependencyPath H genesis b (path ++ [b])

end AvailableChain.FGCompose
end
