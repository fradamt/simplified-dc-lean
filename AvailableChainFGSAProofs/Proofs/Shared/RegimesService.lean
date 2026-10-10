module
public import AvailableChainFGSAProofs.Proofs.Shared.ExactService
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.ExactHead

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.V2.Duty (faulty)
variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
variable {ΔF : Time}

/-- Exact service on a Clean prefix uses joined participation and local gate receipts. -/
theorem exactService_of_head_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hcut : SA.gateTime p.toParams v ≤ b₀)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun _ => Gen.V2.Duty.LabelSyncOn.of_cleanCutBy E rho
      (fun o => ¬ isRowObject o) b₀ _ _ h.healthy
    (fgsaDelay_nonrow E.Δ _) hvd hcut h.cut.2)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. P3 A.9 and blueprint 21 H.22 H3, conditional Recovery exact service.
DC: Generic/Conditions.lean:110–132; UserConfirmationRecovery.lean:235.
INTENTIONAL: post-GST waking and the one-third fault bound supply the SA
fast count. Cardinality uses only the fresh HEAD-seat bijection.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
theorem exactService_of_head_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (v : Slot) (Q : Block) (hne : Q ≠ .genesis)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams v)
    (hhead : SA.voteTime p.toParams v ≤ rho.horizon →
      ∀ x ∈ rho.honest, joinedAt p E rho x v (SA.voteTime p.toParams v) →
        headAtLabel p c E rho x v = some Q)
    (hfast : SA.releaseThreshold p.toParams ≤
      (joinedHonest p E rho (SA.voteTime p.toParams v)).card)
    (hbatch : Gen.Pure.Batch (joinedHonest p E rho (SA.voteTime p.toParams v)).card
      (faulty rho).card)
    (hgeometry : ∀ i x, x ∈ rho.honest → IsGateTick p c rho i x v →
      ExactServiceGateGeometry E rho i x v Q)
    (hScopes : ∀ i x,
      confirmedReaderAtIdx p c E rho x (afterTicksIdx rho (SA.gateTime p.toParams v))
        (SA.gateTime p.toParams v) → IsGateTick p c rho i x v →
      GateReceiptScope E rho i x v) : ExactService p c E rho v Q := by
  have hvd : SA.voteTime p.toParams v + E.Δ ≤ SA.gateTime p.toParams v := by
    rw [h.base.delta]
    change 4 * p.Δ * (v : Int) + p.Δ + p.Δ ≤ 4 * p.Δ * (v : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  apply exactService_of_head_and_gate_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta
    h.base.cstar v Q hne hhead
    (fun hh => Gen.V2.Duty.LabelSyncOn.of_recoveryBy E rho (fun o => ¬ isRowObject o) _ _ h.sync
    (fgsaDelay_nonrow E.Δ _) hGST hvd hh)
    (fun _ => exactService_participation_of_card_joined E rho h.base.cstar v
      hbatch hfast) hgeometry hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem exactService_head_of_proposal_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  exact exactService_head_of_proposal_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta s hx hip hseat N hem D hgeom hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem exactService_head_of_proposal_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip : Nat} {x : V} (hx : x ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (D : FGBlock (Fin p.n)) (hgeom : ExactHeadRunGeometry E rho ip x s D N.erase)
    (hScopes : ∀ y ∈ rho.honest, ∀ ih,
      rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)) →
      joinedAt p E rho y s (SA.voteTime p.toParams s) →
      ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    SA.voteTime p.toParams s ≤ rho.horizon →
      ∀ y ∈ rho.honest, joinedAt p E rho y s (SA.voteTime p.toParams s) →
        headAtLabel p c E rho y s = some N.erase := by
  exact exactService_head_of_proposal_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid h.base.delta s hx hip hseat N hem D hgeom hScopes

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_score_eq_on_clean_of_retained_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  exact fgsa_score_eq_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm hFN D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_score_eq_on_recovery_of_retained_proposal_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (hFN : Block.Preceq (eraseFG (clock p (V2.D.Run.stateBefore E rho ih y).st
      (SA.voteTime p.toParams s)).fg.F) N.erase)
    (D : Block)
    (hgeom : ScoreRunGeometry
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) D)
    (hScope : ScoreServiceScope E rho ip ih x y s D) :
    let src := clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s)
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    let U := proposerVotes src s
    let U' := headVotes p dst s
    (GridCO.seats p.n U).toFinset = (GridCO.seats p.n U').toFinset ∧
    (∀ i, GridCO.equivocates U i = GridCO.equivocates U' i) ∧
    GridCO.voterCount U = GridCO.voterCount U' ∧
    (∀ X, Block.Preceq D X →
      GridCO.goldfishScore src.base.blocks U (proposerSupport src s) X =
        GridCO.goldfishScore dst.base.blocks U' (headSupport p dst s) X) := by
  exact fgsa_score_eq_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm hFN D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_ghost_transfer_sfx_on_clean_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (b₀ : Time) (h : CleanCut₂ p c E rho b₀ ΔF)
    (s : Slot) (_hcut : SA.voteTime p.toParams s ≤ b₀)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  exact fgsa_ghost_transfer_sfx_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm D hgeom hScope

/-- Local receiver services compose with the regime's base at the actual reads. -/
theorem fgsa_ghost_transfer_sfx_on_recovery_on
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G : Time) (h : Recovery₂ p c E rho G ΔF)
    (s : Slot) (_hGST : E.t_GST ≤ SA.proposalTime p.toParams s - p.Δ)
    {ip ih : Nat} {x y : V} (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hip : rho.events[ip]? = some (.tick x (SA.proposalTime p.toParams s)))
    (hih : rho.events[ih]? = some (.tick y (SA.voteTime p.toParams s)))
    (hseat : rho.seatOf (.prop s) ⟨0, Nat.one_pos⟩ = x)
    (N : NamedProposal p.n)
    (hem : (⟨.seat (.prop s) ⟨0, Nat.one_pos⟩, .proposal N⟩ : Obj p) ∈
      V2.D.Run.emitsAt E rho ip)
    (hadm : N.erase ∈ (V2.D.Run.stateBefore E rho ih y).st.base.blocks)
    (D : FGBlock (Fin p.n))
    (hgeom : WalkRunGeometry p
      (clock p (V2.D.Run.stateBefore E rho ip x).st (SA.proposalTime p.toParams s))
      (clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)) s D)
    (hScope : ScoreServiceScope E rho ip ih x y s (eraseFG D)) :
    let dst := clock p (V2.D.Run.stateBefore E rho ih y).st (SA.voteTime p.toParams s)
    Block.Preceq N.erase.parent (headVote p dst s) := by
  exact fgsa_ghost_transfer_sfx_on_run_on (hroots := h.base.receiptIdealization)
    E rho h.base.valid s hx hy hip hih hseat N hem hadm D hgeom hScope

end AvailableChain.FGSA.Run
end
