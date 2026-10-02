module
public import AvailableChainFGSA.Proofs.StoreLaws
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- DC `finalized_preceq_of_height_lt` shape: the agreement form of R-XING
over run blocks under the all-run bound.
DC DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50.
INTENTIONAL: FG-SA content roots are injective, so no hroot premise is needed. -/
theorem fgsa_finalLock_of_bound (hb : FGSASlashableBound p c E rho) (K W : FGBlock (Fin p.n))
    (hK : FinalityRunBlock p c E rho K) (hW : FinalityRunBlock p c E rho W)
    (hh : (derive p.E p.cfg K).h_F < (derive p.E p.cfg W).h) :
    FGBlock.Preceq (derive p.E p.cfg K).F W :=
  (KitFG.slashableWeight_or_finalized_preceq_of_certificate
    p.E (heightView p) (finalityView p) (fgCertificateLaws p) K W hh).resolve_left
    ((FGSASlashableBound_def p c E rho).mp hb K W hK hW)


/-- Strict R-XING (01 §1.3), the run form of `fg.finalLock.v2`.
The height is that of an accepted certificate: `h_F` of a carrier `K` held by
`x` at `e` whose finalized checkpoint is the store's F (01:212). The claim holds
for EVERY such carrier; one F can have carriers of different `h_F` (genesis at
0 and at 1). The store invariant (`Fcar`) supplies one carrier. The held block
can be outside the active view. Identity transport precedes `FaultX`.
The retained _hee binder is unused: the proof compares any two event prefixes. -/
theorem fgsa_finalLock [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (_hee : e ≤ e')
    (K : FGBlock (Fin p.n)) (hKe : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F)
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hheight : (derive p.E p.cfg K).h_F < hOf p.E p.cfg W) :
    FGBlock.Preceq (storeAt p c E rho e x).fg.F W := by
  rcases fgsa_finalLock_ev p c E rho e e' x y hx K W hKe hKF hW hheight with h | hev
  · exact h
  · have hc := fgsa_slashable_faulty_count p c E rho hL hU e e' x y K W ⟨hx, hKe⟩ hW hev
    have ht := hX.lt
    omega

/-- Erasure of strict R-XING to the base block order. -/
theorem fgsa_finalLock_erased [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho)
    (x : V) (hx : x ∈ rho.honest) (e e' : Nat) (hee : e ≤ e')
    (K : FGBlock (Fin p.n)) (hKe : K ∈ (storeAt p c E rho e x).fg.TF)
    (hKF : (derive p.E p.cfg K).F = (storeAt p c E rho e x).fg.F)
    (y : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e' y W)
    (hheight : (derive p.E p.cfg K).h_F < hOf p.E p.cfg W) :
    Block.Preceq (eraseFG (storeAt p c E rho e x).fg.F) (eraseFG W) :=
  eraseFG_preceq
    (fgsa_finalLock p c E rho hL hX hU x hx e e' hee K hKe hKF y W hW hheight)

end AvailableChain.FGSA.Run
end
