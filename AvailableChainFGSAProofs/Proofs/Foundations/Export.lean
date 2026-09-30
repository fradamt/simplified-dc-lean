module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Certificates
public import AvailableChainFGSAProofs.Proofs.Foundations.Reconcile -- shake: keep (L42 run reconcile export)

public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier

public import AvailableChainFGSAProofs.Proofs.Foundations.Client

public import AvailableChainFGSAProofs.Proofs.Foundations.Leases -- shake: keep (F1.3 claim exports)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources
public import AvailableChainFGSAProofs.Proofs.Foundations.Timing -- shake: keep (timing interface exports)


public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- bp.store.v1, with its frozen local schedule premise.
The frozen read-length premise is unused: stateBefore is reachable at every index.
The frozen node-honesty premise is unused for the snapshot invariant.
The frozen schedule premise is unused by the two temporal producers. -/
theorem fgsa_storeAt : StoreAt p c E rho :=
  ⟨fun i x _ _ => cstoreInv_stateBefore E rho i x,
    fun _ => ⟨fgsa_rStoreCumul p c E rho, fgsa_rMono p c E rho⟩⟩

theorem fgsa_storeClaim : StoreClaim p :=
  fun c E rho => fgsa_storeAt p c E rho

theorem fgsa_activeViewAt : ActiveViewAt p c E rho :=
  ⟨fgsa_rStore p c E rho, fgsa_rActive p c E rho⟩

theorem fgsa_activeViewClaim : ActiveViewClaim p :=
  fun c E rho => fgsa_activeViewAt p c E rho

theorem fgsa_frameAt : FrameAt p c E rho :=
  ⟨fgsa_rFrameExact p c E rho, fgsa_rFrame p c E rho⟩

theorem fgsa_frameClaim : FrameClaim p :=
  fun c E rho => fgsa_frameAt p c E rho

theorem fgsa_chainCertificatesAt : ChainCertificatesAt p c E rho :=
  ⟨fgsa_rGeo p c E rho, fgsa_rCert p c E rho⟩

theorem fgsa_chainCertificatesClaim : ChainCertificatesClaim p :=
  fun c E rho => fgsa_chainCertificatesAt p c E rho

/-- bp.reconcile.v1 at every reachable store, including due lease rows.
K1 uses reconcile_harmless_origin; its block form is admitBlock_reconcile_harmless.
The frozen _h reachability premise is unused by these general reconcile identities. -/
theorem fgsa_reconcileAt (st : State p.n) (_h : Reachable p st) : ReconcileAt p st :=
  ⟨reconcile_eq st, reconcile_idem st, reconcile_harmless_origin st⟩

theorem fgsa_reconcileClaim : ReconcileClaim p :=
  fun st h => fgsa_reconcileAt p st h

/-- The run carrier uses the general FG geometry and the F1.1 view theorem.
The frozen run-block premises for X and Y are unused by general FG geometry. -/
theorem fgsa_carrierAt : CarrierAt p c E rho :=
  ⟨fun X Y _ _ => ⟨(fgsa_carrier_geometry X Y).1, (fgsa_carrier_geometry X Y).2.1⟩,
    fun X _ => (fgsa_carrier_geometry X X).2.2, fgsa_rCarrierView p c E rho⟩

/-- The frozen all-runs carrier claim. -/
theorem fgsa_carrierClaim : CarrierClaim p :=
  fun c E rho => fgsa_carrierAt p c E rho

/-- bp.clientSafety.v1, from T7.9 A under Linked. -/
theorem fgsa_clientSafetyClaim : ClientSafetyClaim p :=
  fun c E rho hL => fgsa_clientSafeAll p c E rho hL

/-- Family (0), through Base₂.linked. -/
theorem fgsa_clientSafetyBaseClaim : ClientSafetyBaseClaim p :=
  fun c E rho _ hb => fgsa_clientSafeAll p c E rho hb.set.linked

/-- All four clauses of the frozen lease-origin statement.
The frozen read-length premise is unused: the producers cover every index.
The frozen node-honesty premise is unused: the producers cover every node. -/
theorem fgsa_leaseOriginsAt (hs : V2.ScheduleWellFormed E rho) :
    LeaseOriginsAt p c E rho :=
  fun i x _ _ => ⟨fgsa_leaseOrigins_origins p c E rho i x,
    fgsa_leaseOrigins_chain p c E rho i x,
    fgsa_leaseOrigins_ancestorDeadlines p c E rho i x,
    fgsa_leaseOrigins_fastWrites p c E rho hs i x⟩

/-- The frozen lease-origin claim for scheduled runs. -/
theorem fgsa_leaseOriginsClaim : LeaseOriginsClaim p :=
  fun c E rho hs => fgsa_leaseOriginsAt p c E rho hs

/-- Source discipline without the quorum clauses, with the frozen F1.3 input. -/
theorem sourceDiscipline_base {Pt : Type} {pt : Pt}
    (hb : BasePrem p c E rho pt) :
    SourceDisciplineBaseAt p c E rho := by
  have hs := hb.set.valid.toScheduleWellFormed
  exact ⟨sourceDiscipline_tSrc p c E rho hs,
    sourceDiscipline_labelBound p c E rho hs,
    fun _ _ _ _ _ ha he => sourceDiscipline_emittedName p c E rho hs ha he⟩

/-- The source-discipline conclusion, with the frozen F1.1 and F1.3 inputs. -/
theorem sourceDiscipline_at [Fintype V] {Pt : Type} {pt : Pt}
    (hb : SourceDisciplinePrem p c E rho pt)
    (hS : RStore p c E rho) :
    SourceDisciplineAt p c E rho :=
  ⟨sourceDiscipline_base p c E rho (pt := pt) ⟨hb.set⟩,
    sourceDiscipline_strat p c E rho hb hS,
    sourceDiscipline_qcOrigin p c E rho hb hS⟩

/-- F1.5 base claim, with the F1.3 lease input discharged. -/
theorem fgsa_sourceDisciplineBaseClaim : SourceDisciplineBaseClaim p :=
  fun c E rho pt hb => sourceDiscipline_base p c E rho (pt := pt) hb

/-- F1.5 claim, with the F1.1 store and F1.3 lease inputs discharged. -/
theorem fgsa_sourceDisciplineClaim : SourceDisciplineClaim p :=
  fun c E rho pt hb => sourceDiscipline_at p c E rho (pt := pt) hb
    (fgsa_rStore p c E rho)

/-- F1.5 source-frame claim, with both foundation inputs discharged. -/
theorem fgsa_srcFrameAboveClaim : SrcFrameAboveClaim p :=
  fun c E rho pt hb => sourceDiscipline_srcFrameAbove p c E rho (pt := pt) hb
    (fgsa_rStore p c E rho)

/-- The foundation package, with the F1.5 source input discharged. -/
theorem fgsa_fgFoundationClaim : FGFoundationClaim p :=
  fun c E rho pt hb =>
    ⟨fgsa_rStore p c E rho, fgsa_rStoreCumul p c E rho,
      fgsa_rMono p c E rho, fgsa_rFrameExact p c E rho, fgsa_rGeo p c E rho,
      sourceDiscipline_strat p c E rho (pt := pt) hb (fgsa_rStore p c E rho),
      fgsa_rRec p c E rho⟩

/-- The frozen read-length premise is unused: stateBefore is always reachable.
The frozen node-honesty premise is unused by the reachable-store nesting theorem. -/
theorem fgsa_outputNestingAt : OutputNestingAt p c E rho :=
  fun i x _ _ => (FGSA.outputNesting_stored p _ (reachable_stateBefore E rho i x)).1

theorem fgsa_outputNestingClaim : OutputNestingClaim p :=
  fun c E rho => fgsa_outputNestingAt p c E rho


end AvailableChain.FGSA.Run
end
