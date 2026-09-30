module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Shared
public import AvailableChainFGSAClaims.Claims.Clean

@[expose] public section

/-! P3 §4.8: the exported safety claims. Only the Claims root imports this module.
The zero and positive Clean lane Props are not exported claims. The receipt
and suffix-walk rows cite their existing statements in their claim homes. -/

namespace AvailableChain.FGSA.Run

/-- The complete exported safety-claim aggregate, frozen at G-F0a. -/
structure FGSASafetyClaims (p : FGSA.Params) : Prop where
  carrier : CarrierClaim p
  chainCertificates : ChainCertificatesClaim p
  store : StoreClaim p
  activeView : ActiveViewClaim p
  leaseOrigins : LeaseOriginsClaim p
  reconcile : ReconcileClaim p
  outputNesting : OutputNestingClaim p
  frame : FrameClaim p
  clientSafety : ClientSafetyClaim p
  clientSafetyBase : ClientSafetyBaseClaim p
  sourceDisciplineBase : SourceDisciplineBaseClaim p
  sourceDiscipline : SourceDisciplineClaim p
  sameLabel : SameLabelClaim p
  releaseStore : ReleaseStoreClaim p
  release : ReleaseClaim p
  headReachesLo : HeadReachesLoClaim p
  cleanCut : CleanCutClaim p
  cleanHistory : CleanHistoryClaim p
  cleanPrefixTruncation : CleanPrefixTruncationClaim p
  cleanSafety : CleanSafetyClaim p

/-- The complete safety interface aggregate (L48, IF1), frozen whole at G-F0a (R5-64). -/
structure FGSASafetyInterfaces (p : FGSA.Params) : Prop where
  -- consumer: F2 positive Clean, Assembly/CleanCut; producer: F1.1–F1.5 (P3 :7820–7836)
  -- strat is filled by the same RStrat producer as timingContract.certLag.
  fgFoundation : FGFoundationClaim p
  -- consumer: F2/F3/F4/F5 lane proofs, Assembly/<Claim>; producer: F1.5 (P3 :7858–7870)
  srcFrameAbove : SrcFrameAboveClaim p
  -- consumer: Clean (F2), inclusion/proposal/suffix/gate;
  -- producer: F2.2 (Shared/Channels) (P3 :7311–7330)
  cpPrefix : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → CPPrefix p c E rho
  -- consumer: P1 (F3); producer: F2.2 (Shared/Channels) (P3 :7331–7341)
  cpCompat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → CPCompat p c E rho
  -- consumer: 02 §5.4, 03 §8, 21 H.11, 22 kernel; producer: F1.5 (a) (P3 :7423–7438)
  -- Same Prop as SourceDisciplineBaseAt's first conjunct.
  tSrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → TSrc p c E rho
  -- consumer: TimingContract.label, BelowLabel; producer: F1.5 (d) (P3 :7439–7444)
  -- Same Prop as SourceDisciplineBaseAt's second conjunct.
  labelBound : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → LabelBound p c E rho
  -- consumer: every AG instance; producer: F1 (F1.5 (b–d) + the T7.5/clock facts
  -- for atomic/tickFG) (P3 :7203–7229; IF1)
  -- certLag and fgFoundation.strat are the same Prop RStrat;
  -- both are filled by the ONE RStrat producer lemma (F1.5); no second proof.
  timingContract : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → TimingContract p c E rho

end AvailableChain.FGSA.Run
end
