module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedContinuation
public import AvailableChainFGSAProofs.Proofs.Foundations.Store

public section

namespace AvailableChain.FGSA.Run.Tests.OutageLaterHeads

open AvailableChain.SimplexFG Gen.Pure

/-- Restart at 9 permits the label-3 gate but suppresses its label-3 HEAD.
An enabled gate therefore does not supply a joined batch at the earlier vote. -/
theorem wake_nine_guard (p : Params) (hd : p.Δ = 1) :
    joinedAtTime p (some 9) (SA.voteTime p.toParams 3) = false ∧
      joinedAtTime p (some 9) (SA.gateTime p.toParams 3) = true := by
  norm_num [joinedAtTime, Params.slotOf, arming_vote_eq, arming_gate_eq, slotStartZ, hd]

/-- The label-3 marker read cannot use a time-12 transport anchor when GST is 20. -/
theorem pre_gst_marker_anchor (p : Params) (hd : p.Δ = 1) :
    ¬ (20 ≤ SA.proposalTime p.toParams 3) := by
  norm_num [arming_proposal_eq, hd]

/-- A later label-6 reader can use the time-24 anchor after the same GST. -/
theorem post_gst_marker_anchor (p : Params) (hd : p.Δ = 1) :
    20 ≤ SA.proposalTime p.toParams 6 := by
  norm_num [arming_proposal_eq, hd]

/-- With r=2 and k=2, label 6 is beyond E's fixed count window. -/
theorem post_e_count_window (p : Params) (hk : p.k = 2) :
    ¬ ((6 : Slot) ≤ 2 + p.k + 1) := by
  norm_num [hk]

/-- The marker service consumes the actual Foundation monotonicity producer.
The remaining facts name this source marker and this joined read only. -/
theorem marker_service_from_foundation {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {k i : Nat} {y x : V} {m s : Slot} {B P : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hms : m ≤ s) (hGST : E.t_GST ≤ SA.voteTime p.toParams m)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF) (hBP : FGBlock.Preceq B P)
    (hF : Block.Compatible (F_at p c E rho i x) (eraseFG B)) :
    Block.Preceq (eraseFG B) (F_at p c E rho i x) ∨
      P ∈ (storeAt p c E rho i x).fg.TF :=
  outage_later_marker_receipt hBase hSync (fgsa_rMonoAll p c E rho)
    hk hi hy hx hJ hms hGST hP hBP hF

end AvailableChain.FGSA.Run.Tests.OutageLaterHeads

#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.wake_nine_guard
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.pre_gst_marker_anchor
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.post_gst_marker_anchor
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.post_e_count_window
#print axioms AvailableChain.FGSA.Run.Tests.OutageLaterHeads.marker_service_from_foundation
