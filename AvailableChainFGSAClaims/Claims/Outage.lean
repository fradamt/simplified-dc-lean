module
public import AvailableChainFGSAClaims.Statements.Packages.Outage
public import AvailableChainFGSAClaims.Statements.Packages.Inclusion
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainGeneric.Statements.Pure.Props

@[expose] public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure (ServedOn MonoOn)

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- bp.exactProposal.v2; 00:985–997; 03 §4:332–394; P3:3234.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: this local adoption
contract gives admitted proposals and exact HEADs, used to prove inclusion.
The deterministic read clocks the strict-before state and also covers an
asleep reader; it does not require a tick or an emitted HEAD. -/
def ExactProposalAt (pt : PtSP) : Prop :=
  (∀ x ∈ rho.honest, ∃ o i t,
    (fgsaInterface p c).block o.payload = some pt.P ∧
    t < SA.voteTime p.toParams pt.s ∧ V2.D.Run.acceptsAt E rho i x o t) ∧
  (∀ x ∈ rho.honest,
    FGSA.headVote p
      ((fgsa p c).clock (V2.D.Run.stateBeforeTime E rho (SA.voteTime p.toParams pt.s) x)
        (SA.voteTime p.toParams pt.s)).st pt.s = pt.P) ∧
  (∀ x ∈ rho.honest, E.awake x (SA.voteTime p.toParams pt.s) = false →
    ∀ o, ¬ V2.D.Run.emits E rho x o (SA.voteTime p.toParams pt.s))

/-- bp.exactProposal.v2; 00:985–997; 03 §4; P3:3914.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast: INTENTIONAL: exact local HEAD
adoption is the FG-SA producer of the generic inclusion property. -/
def ExactProposalClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    ExactProposalPrem p c E rho pt ΔF → ExactProposalAt p c E rho pt

/-- bp.cleanInclusion.v2; 03:397–431; P3:3234–3240; S3a Q12:3454.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: the event-prefix post-gate read and monotonicity supply the
inclusive public read after same-time deliveries (S3a Q12). -/
def InclusionPostGateAt (pt : PtSP) : Prop :=
  ServedOn (· ∈ rho.honest) (S_at p c E rho) pt.P
    (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
  MonoOn (· ∈ rho.honest) (S_at p c E rho) (· ≤ rho.events.length)

/-- bp.cleanInclusion.v2; 00:999–1007; 03:397–400; P3:3234–3240.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: a supplied honest proposal and all later finite-horizon reads,
including asleep readers, replace DC's existential deadline read (03 §5). -/
def InclusionAt (pt : PtSP) : Prop :=
  ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ServedOn (· ∈ rho.honest) (fun t x => V2.D.outputAt E rho g x t) pt.P
      (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon)

/-- bp.cleanInclusion.v2; S3a Q12:3454–3458; 03 §5.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast:
INTENTIONAL: expose the post-gate
read plus event monotonicity before deriving the public-read form (O13). -/
def CleanInclusionPostGateClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    CleanInclusionPrem p c E rho pt ΔF → InclusionPostGateAt p c E rho pt

/-- bp.cleanInclusion.v2; 00:999–1007; S3a Q12:3454–3458; P3:3234–3240.
DC Generic/Claims.lean:67,73 Consensus.available/stableIncludedFast: INTENTIONAL: the public-read
corollary covers each later read within the Clean horizon (03 §5).
Its proof is deferred; the post-gate claim and monotonicity are its route. -/
def CleanInclusionClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) (ΔF : Time),
    CleanInclusionPrem p c E rho pt ΔF → InclusionAt p c E rho pt

/-- bp.fastP1.v2 / bp.slowP1.v2; 00:1031–1054; S3a FS8:2010–2032.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: FG-SA also protects emitted HEADs and proposal parents;
these are separate from the persistence predicate (00:875–878). -/
def DutiesExtendOn (B : Block) (b₀ b₁ : Time) : Prop :=
  ∀ x t o, x ∈ rho.honest → b₀ ≤ t → t < b₁ → V2.D.Run.emits E rho x o t →
    (∀ H, o.payload = .head H → Block.Preceq B H) ∧
    (∀ C raw sup rows, o.payload = .proposal C raw sup rows → Block.Preceq B C.parent)

/-- bp.outageCompatibility.v2; 00:1009–1029; S3a FS8:2020–2022.
DC Generic/Claims Consensus.stableAsynchronyResilient: INTENTIONAL:
FG-SA must also control its finalized state during the outage (03 §§6–8). -/
def FCompatBefore (B : Block) (b₁ : Time) : Prop :=
  ∀ t x, 0 ≤ t → t < b₁ → x ∈ rho.honest →
    Block.Compatible B (V2.D.outputAt E rho finalizedOut x t)

/-- bp.fastP1.v2 / bp.slowP1.v2; 00:1031–1054; P3:3234–3240; S3a FS8.
DC Generic/Properties:124–129 PersistsFrom, Generic/Claims:79–80:
INTENTIONAL: ServedOn is restricted to [b₀,b₁), and separate duty and
F-compatibility clauses implement the blueprint's finite outage contract. -/
def P1Concl (pt : PtOut) : Prop :=
  (∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
    ∀ x B, x ∈ rho.honest → Block.Preceq B (V2.D.outputAt E rho g x pt.T) →
      ServedOn (· ∈ rho.honest) (fun t y => V2.D.outputAt E rho g y t) B
        (fun t => pt.b₀ ≤ t ∧ t < pt.b₁)) ∧
  (∀ x B, x ∈ rho.honest →
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
    DutiesExtendOn p c E rho B pt.b₀ pt.b₁ ∧ FCompatBefore p c E rho B pt.b₁)

/-- bp.outageCompatibility.v2 / bp.slowP1.v2; 00:1009–1029, 1043–1054;
03 §§6–8; S3a FS8. DC Generic/Claims.lean:79–80:
INTENTIONAL: the FG-SA lease starts at the pending gate, not the outage
cut; it preserves B in the full domain or below Z until F covers B. -/
def LeaseOrFFrom (B : Block) (d b₁ : Time) : Prop :=
  ∀ t y, d ≤ t → t < b₁ → y ∈ rho.honest →
    let st := storeAt p c E rho (timeIdx rho t) y
    Block.Preceq B (eraseFG st.fg.F) ∨
      ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧ d + L p ≤ dl ∧
        ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
          Block.Preceq B (eraseFG (FGSA.controls p st).Z))

/-- bp.outageCompatibility.v2; 00:1009–1029; S3a FS8:2027–2031.
DC Generic/Claims.lean:79–80: INTENTIONAL: the finite outage carries a
pending-gate lease guarantee in addition to DC's persistence (03 §§6–8). -/
def OutageCompatAt (pt : PtOut) : Prop :=
  P1Concl p c E rho pt ∧
  ∀ x B, x ∈ rho.honest →
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x pt.T) →
    B ≠ .genesis →
    LeaseOrFFrom p c E rho B
      (SA.gateTime p.toParams (((pt.b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat + 1)) pt.b₁

/-- bp.outageCompatibility.v2; 00:1009–1029; P3:3914–3930; S3a FS8.
DC Generic/Claims.lean:79–80: INTENTIONAL: both finite OutageSet alternatives
carry the additional duty, F, and pending-gate lease clauses (03 §§6–8). -/
def OutageCompatClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (pt : PtOut) (ΔF : Time),
    OutagePrem p c fast E rho pt ΔF → OutageCompatAt p c E rho pt

/-- bp.fastP1.v2; 00:1031–1041; 03 §9.1; P3:3929–3930.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: fast OutageSet fixes lag 4Δ and the high participation
premise; P1Concl adds the blueprint's duty and F clauses. -/
def FastP1Claim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtOut) (ΔF : Time),
    OutagePrem p c true E rho pt ΔF → P1Concl p c E rho pt

/-- bp.slowP1.v2; 00:1043–1054; 03 §9.2; P3:3929–3930.
DC Generic/Claims.lean:79–80 Consensus.stableAsynchronyResilient:
INTENTIONAL: slow OutageSet fixes lag L−3Δ without fast participation,
and includes the pending-gate lease guarantee of 00:887–889. -/
def SlowP1Claim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtOut) (ΔF : Time),
    OutagePrem p c false E rho pt ΔF → OutageCompatAt p c E rho pt

end AvailableChain.FGSA.Run
end
