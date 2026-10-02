module
public import AvailableChainFGSAClaims.Statements.FinalityApi
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSARun.Statements.Slashing
public import AvailableChainGeneric.Statements.Pure.Props

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure

variable (p : Params)

/-- F-API, dc-align-full.md:78–86;
DC Generic/Claims.lean:56 Consensus.certificatesAccountable; class: INTENTIONAL.
SAME conclusion shape. FG content roots are injective; no root premise is needed. -/
def PureAccountableClaim : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true

/-- F-API, dc-align-full.md:84–87;
DC certificatesAccountable agreement corollary (L/FinalitySafety.lean:45);
class: INTENTIONAL.
SAME conclusion shape. FG content roots are injective; no root premise is needed. -/
def PureAgreementClaim : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
      FGBlock.compatible T₁ T₂ = true

/-- F-API, dc-align-full.md:94–110;
DC Generic/Claims.lean:59,65 Consensus.finalizedAccountable/finalizedSafe;
class: INTENTIONAL.
SAME conclusion shape. FG content roots are injective; no root premise is needed. -/
def WholeRunAccountableClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    FinalityExecution p c rho → WholeRunAccountable p c E rho

/-- F-API, dc-align-full.md:104–112;
DC Generic/Claims.lean:59,65 Consensus.finalizedAccountable/finalizedSafe;
class: INTENTIONAL.
SAME conclusion shape. FG content roots are injective; no root premise is needed. -/
def WholeRunAgreementClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    FinalityExecution p c rho → FinalitySlashableBound p c E rho →
    WholeRunAgreement p c E rho

/-- F-API, dc-align-full.md:112;
DC L/FinalitySafety.lean:61 (internal; no direct public field); class: INTENTIONAL.
Event-prefix observations use stored W finality. FG content roots are injective. -/
def EventPrefixAgreementClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    FinalityExecution p c rho → FinalitySlashableBound p c E rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j,
      FGBlock.compatible (storeAt p c E rho i x).fg.F (storeAt p c E rho j y).fg.F = true

/-- F-API, dc-align-full.md:123–129;
DC L/FinalitySafety.lean:117 (internal; no direct public field); class: INTENTIONAL.
Linked maps fixed FG seats to holders. Authentic row carriage covers all run blocks;
unit weights give the count bound. -/
def FaultCountSlashableBoundClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    V2.D.Linked (fgsaFamilies p c).linked rho →
    (∀ K, FinalityBlock p c E rho K → FinalityRowCarriage p c E rho (chainRows K)) →
    (∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x) →
    (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 →
    FinalitySlashableBound p c E rho

/-- F-API, dc-align-full.md:131–134; DC G/Claims.lean:61; L/FinalitySafety.lean:103; class:
INTENTIONAL.
FG restore resets F to genesis; NoRestart is required. No fault bound is needed. -/
def FinalizedMonotonicityClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x))

/-- G-F0b F-H; DC `Generic/Claims.lean:63` (`honestNeverSlashed`).
`UnforgeableSignatures` is SAME as the signature part of DC `UnforgeableRun`.
`Linked` is INTENTIONAL: FG rows are signed by fixed seat; the holder map
supplies DC's validator identity (F-H, `dc-align-full.md:135–141`).
The conclusion is SAME as DC. No sorted, honest_only, horizon, fault bound,
regime or restart premise is required. -/
def HonestNeverSlashedClaim (p : Params) : Prop :=
  ∀ {In : Type} (c : AppCodec In) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (fgsa p c)),
    V2.D.UnforgeableSignatures E rho →
    V2.D.Linked (fgsaFamilies p c).linked rho →
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho

/-- bp.finalizedSafety.v1 (00:683–687; P3 §4.7).
DC: Generic/Claims.lean:61,65 finalizedMonotone/finalizedSafe.
INTENTIONAL: event-index reads include intermediate states in one time batch. -/
def FinalizedSafetyConcl (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
  MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length)

/-- bp.finalizedSafety.v1 (00:683–687; P3 §4.7).
DC: Claims.lean:61,65 Consensus.finalizedMonotone/finalizedSafe.
INTENTIONAL: the FG-SA BaseSet and a ≤ f are the run-level premises;
no recovery, proposer honesty, recurrence, or delay-ratio premise is added. -/
def FinalizedSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FinalizedSafetyPrem p c E rho pt →
    FinalizedSafetyConcl p c E rho

/-- fg.finalLock.v2 (00:643–650; P3 App. A.4; adopted carrier read in RXing).
DC: DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50
NamedFinalizationBridge.finalized_preceq_of_height_lt.
INTENTIONAL: this is the fault-bounded, held-block channel over each accepted
certificate carrier; RXing retains its certificate h_F, also for genesis.
The accountability alternative is a separate result, not an added premise. -/
def FinalLockClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FinalizedSafetyPrem p c E rho pt → RXing p c E rho

end AvailableChain.FGSA.Run
end
