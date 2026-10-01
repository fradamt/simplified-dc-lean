module
public import AvailableChainFGSAClaims.Statements.Packages.Safety

@[expose] public section

namespace AvailableChain.FGSA.Run
open Gen.Pure
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Local FF5/FF6 budget (22:1166–1170,1191–1227), P3 §4.4.2 D41.
Consumers: FirstFinalityPrem, ProposalFinalPrem. Strong forms use γ, not g+2. -/
def finalityWindow (form : FinForm) (g : Nat) : Time :=
  match form with
  | .strongW | .lit | .recC => (γ form g : Time) * P p + 9 * p.Δ
  | _ => W_F p g
/-- FF5 from GST (00:1147–1152), family (3), P3 §4.4.2.
Consumer: first-finality claim. The form-specific parameter premises stay on claims. -/
structure FirstFinalityPrem (G : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G form g
  hhor : E.t_GST + B_H p G + finalityWindow p form g ≤ rho.horizon
/-- FF5 trigger (22:1166–1170,1191–1213), family (3), P3 §4.4.2.
Consumer: FinalityLivenessConcl. -/
structure FinalityLivenessPrem (G : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtT) : Prop where
  set : FinalitySet p c E rho G form g
  late : E.t_GST + B_H p G ≤ pt.t
  hhor : pt.t + finalityWindow p form g ≤ rho.horizon
/-- FF6 (22:1216–1227), family (3), P3 §4.4.2 D41.
Consumer: ProposalFinalConcl. X can be arbitrarily late; its deadline is local. -/
structure ProposalFinalPrem (G : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtSX) : Prop where
  set : FinalitySet p c E rho G form g
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.X
  late : E.t_GST + B_H p G ≤ V2.proposalTime (fgsaInterface p c) pt.s
  hhor : V2.proposalTime (fgsaInterface p c) pt.s + finalityWindow p form g ≤ rho.horizon
/-- FF7 (22:1229–1245), family (3), P3 §4.4.2 D41.
Consumer: AboveFrontierConcl. Two forward windows give 2(g+2)P + 18Δ. -/
structure AboveFrontierPrem (G : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (pt : PtT) : Prop where
  set : FinalitySet p c E rho G form g
  late : E.t_GST + B_H p G ≤ pt.t
  hhor : pt.t + 2 * finalityWindow p form g ≤ rho.horizon
/-- QF2 (22:1481–1489; 00:1289–1293), family (3), P3 §4.7.
Consumer: qualified first finality. No kernel window or start is assumed. -/
structure QualifiedFinalityPrem (G : Time) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G .recS g
  hhor : E.t_GST + B_Q p G g ≤ rho.horizon
/-- QF4 (22:1581–1593; 00:1295–1300), family (3), P3 §4.7.
Consumer: skip first finality. -/
structure SkipFinalityPrem (G : Time) (g : Nat)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G .recSkip g
  hhor : E.t_GST + B_skip p G g ≤ rho.horizon

end AvailableChain.FGSA.Run
end
