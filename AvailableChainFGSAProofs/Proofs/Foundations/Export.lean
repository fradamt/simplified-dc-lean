module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAProofs.Proofs.Foundations.Store
public import AvailableChainFGSAProofs.Proofs.Foundations.Certificates

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

end AvailableChain.FGSA.Run
end
