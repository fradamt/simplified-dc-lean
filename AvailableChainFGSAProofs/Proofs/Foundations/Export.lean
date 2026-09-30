module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Certificates
public import AvailableChainFGSAProofs.Proofs.Foundations.Reconcile -- shake: keep (L42 run reconcile export)

public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier

public import AvailableChainFGSAProofs.Proofs.Foundations.Client

public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- bp.store.v1, with its frozen local schedule premise. -/
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
K1 uses reconcile_harmless_origin; its block form is admitBlock_reconcile_harmless. -/
theorem fgsa_reconcileAt (st : State p.n) (_h : Reachable p st) : ReconcileAt p st :=
  ⟨reconcile_eq st, reconcile_idem st, reconcile_harmless_origin st⟩

theorem fgsa_reconcileClaim : ReconcileClaim p :=
  fun st h => fgsa_reconcileAt p st h

/-- The run carrier uses the general FG geometry and the F1.1 view theorem. -/
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

end AvailableChain.FGSA.Run
end
