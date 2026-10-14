module
public import AvailableChainFGCompose.Statements.Population.FinalityKernel
public import AvailableChainFGCompose.Proofs.Finality.Rows
public import AvailableChainFGCompose.Proofs.Finality.RowsRecords

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {I : V2.D.Interface P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)}

variable {decodeProposal : P.Object → Option (Slot × Body)}
variable {bodyErase : Body → Block} {bodyRows : Body → List Wire}
variable {blockWireRows : P.State → List Wire}
variable {parentFG : P.State → Block → Option (FGBlock (Fin n))}
variable {parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId}
variable {validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool}
variable {makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n)}
variable {valid : Wire → Bool} {ac : FGACServiceReads V}
variable {cfg : FGConfig} {K : Nat} {ΔF : Time} {sp : FGServicePoint} {pt : KernelPt} {A : Block}
variable (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)


/-- The selected action head consumes the exact walk and the middle's held caps. -/
theorem rowsPrem_pending_head_holder (height : FGHeightLaws Ef O.height)
    (bridge : HeightBridge Ef cfg O.height)
    (read : ∀ x nd, postClock E rho x (T.action (pt.r + 2)) = some nd →
      (R.core (V2.D.Run.stateBefore E rho (afterTicksIdx rho (T.action (pt.r + 2))) x)).fg =
        (R.core nd).fg)
    (head : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∃ H, R.finalityHead nd = some H ∧ H ∈ (R.core nd).fg.TF)
    (walk : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∀ H, R.finalityHead nd = some H → Block.Preceq (R.erase m.X_D) (R.erase H))
    (reflect : ∀ nd A B, A ∈ (R.core nd).fg.TF → B ∈ (R.core nd).fg.TF →
      Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B) :
    ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      ∃ H, R.finalityHead nd = some H ∧ FGBlock.Preceq m.X_D H ∧
        (O.height H).h = m.d + 2 ∧ (O.height H).J = m.U ∧
        (O.height H).h_j = m.d + 1 ∧ (O.finality H).h_F < m.d + 1 ∧
        (O.height H).T_h = (O.height m.X_D).T_h := by
  intro x nd hx hnd
  have hread := read x nd hnd
  have hi : afterTicksIdx rho (T.action (pt.r + 2)) ≤ rho.events.length :=
    List.length_filter_le _ _
  apply pending_action_head_capped R O Ef cfg height bridge (m.d + 1) m.X_D m.U nd
    (head x nd hx hnd) (walk x nd hx hnd) (reflect nd)
  · rw [← hread]
    exact m.heldDAtFinalAction x hx
  · exact m.heightD
  · exact m.justifiedD
  · exact m.justifiedHeightD
  · intro B hB
    exact m.capThroughFinalAction _ x B hi le_rfl ⟨hx, by rw [hread]; exact hB⟩
  · intro B hB
    exact m.finalityThroughFinalAction _ x B hi le_rfl ⟨hx, by rw [hread]; exact hB⟩

end AvailableChain.FGCompose
end
