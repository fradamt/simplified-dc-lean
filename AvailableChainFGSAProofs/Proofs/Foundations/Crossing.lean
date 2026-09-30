module
public import AvailableChainFGSAProofs.Proofs.Foundations.Accountable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))

/-- Strict R-XING (01 §1.3), the run form of `fg.finalLock.v2`.
The height is that of an accepted certificate: `h_F` of a carrier `K` held by
`x` at `e` whose finalized checkpoint is the store's F (01:212). The claim holds
for EVERY such carrier; one F can have carriers of different `h_F` (genesis at
0 and at 1). The store invariant (`Fcar`) supplies one carrier. The held block
can be outside the active view. Identity transport precedes `FaultX`. -/
theorem fgsa_finalLock [Fintype V]
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hU : V2.UnforgeableSignatures E rho)
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
    (hL : V2.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.faulty rho).card)
    (hU : V2.UnforgeableSignatures E rho)
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
