module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Healed

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
structure FirstFinalityPrem (G : Time) (ΔF : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G ΔF form g
  hhor : E.t_GST + B_H p G + finalityWindow p form g ≤ rho.horizon
/-- FF5 trigger (22:1166–1170,1191–1213), family (3), P3 §4.4.2.
Consumer: FinalityLivenessConcl. -/
structure FinalityLivenessPrem (G : Time) (ΔF : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT) : Prop where
  set : FinalitySet p c E rho G ΔF form g
  late : E.t_GST + B_H p G ≤ pt.t
  hhor : pt.t + finalityWindow p form g ≤ rho.horizon
/-- FF6 (22:1216–1227), family (3), P3 §4.4.2 D41.
Consumer: ProposalFinalConcl. X can be arbitrarily late; its deadline is local. -/
structure ProposalFinalPrem (G : Time) (ΔF : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSX) : Prop where
  set : FinalitySet p c E rho G ΔF form g
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.X
  late : E.t_GST + B_H p G ≤ V2.D.proposalTime (fgsaInterface p c) pt.s
  hhor : V2.D.proposalTime (fgsaInterface p c) pt.s + finalityWindow p form g ≤ rho.horizon
/-- FF7 (22:1229–1245), family (3), P3 §4.4.2 D41.
Consumer: AboveFrontierConcl. Two forward windows give 2(g+2)P + 18Δ. -/
structure AboveFrontierPrem (G : Time) (ΔF : Time) (form : FinForm) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtT) : Prop where
  set : FinalitySet p c E rho G ΔF form g
  late : E.t_GST + B_H p G ≤ pt.t
  hhor : pt.t + 2 * finalityWindow p form g ≤ rho.horizon
/-- QF2 (22:1481–1489; 00:1289–1293), family (3), P3 §4.7.
Consumer: qualified first finality. No kernel window or start is assumed. -/
structure QualifiedFinalityPrem (G : Time) (ΔF : Time) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G ΔF .recS g
  hhor : E.t_GST + B_Q p G g ≤ rho.horizon
/-- QF4 (22:1581–1593; 00:1295–1300), family (3), P3 §4.7.
Consumer: skip first finality. -/
structure SkipFinalityPrem (G : Time) (ΔF : Time) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet p c E rho G ΔF .recSkip g
  hhor : E.t_GST + B_skip p G g ≤ rho.horizon

/-- Plan §1.7. DC: INTENTIONAL W recurrence forms; no strong dispatch. -/
inductive FinFormW | recFE | recF4

/-- Blueprint 22:1371–1448. DC: INTENTIONAL full receipt guards. -/
def FinFormW.holdsW (form : FinFormW) (ΔF : Time) (H : Slot → Prop)
    (GST horizon : Time) (g : Nat) : Prop :=
  match form with
  | .recFE => FE_W p ΔF H GST horizon g
  | .recF4 => F4_W p ΔF H GST horizon g

theorem FinFormW.holdsW_def (form : FinFormW) (ΔF : Time) (H : Slot → Prop)
    (GST horizon : Time) (g : Nat) :
    FinFormW.holdsW p form ΔF H GST horizon g =
  (match form with
  | .recFE => FE_W p ΔF H GST horizon g
  | .recF4 => F4_W p ΔF H GST horizon g) := rfl

/-- Plan §1.7. DC: INTENTIONAL explicit ΔF, κ bound and W recurrence.
The existing Recovery₂ supplies validity, row delivery and finite proposer gap. -/
structure FinalitySet_W (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (form : FinFormW) (g : Nat) : Prop where
  core : Recovery₂ p c E rho G ΔF
  bound : LivenessBoundW p ΔF
  recur : form.holdsW p ΔF (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    E.t_GST rho.horizon g

/-- Plan §1.7. DC: INTENTIONAL FE/F4 share W_W; no strong dispatch. -/
def finalityWindow_W (ΔF : Time) (_form : FinFormW) (g : Nat) : Time := W_W p ΔF g

theorem finalityWindow_W_def (ΔF : Time) (form : FinFormW) (g : Nat) :
    finalityWindow_W p ΔF form g = W_W p ΔF g := rfl

/-- FF5 GST composition (22:1382–1384). DC: INTENTIONAL supplied H-time witness.
HTime supplies input and start. This package does not use best/search healing. -/
structure FirstFinalityPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (_pt : Unit) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  start : tstar p w < E.t_GST + B_HF p ΔF G
  hhor : E.t_GST + B_HF p ΔF G + W_W p ΔF g ≤ rho.horizon

/-- Local FF5 (22:1371–1401). DC: INTENTIONAL common input and receipt horizon.
The trigger is at or after t*, with no GST healing-bound restriction. -/
structure FinalityLivenessPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  start : tstar p w ≤ pt.t
  hhor : pt.t + W_W p ΔF g ≤ rho.horizon

/-- Local FF6 (22:1421–1430). DC: INTENTIONAL common input; local proposal deadline. -/
structure ProposalFinalPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSX) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.X
  start : tstar p w ≤ V2.D.proposalTime (fgsaInterface p c) pt.s
  hhor : V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g ≤ rho.horizon

/-- Local FF7 (22:1434–1451). DC: INTENTIONAL two complete forward searches.
The first guard and the second guard include their carrier receipt tails. -/
structure AboveFrontierPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  start : tstar p w ≤ pt.t
  firstHorizon : pt.t + W_W p ΔF g ≤ rho.horizon
  hhor : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon

end AvailableChain.FGSA.Run
end
