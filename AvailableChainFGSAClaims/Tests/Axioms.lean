module
import AvailableChainFGSAClaims.Statements.Reads -- shake: keep (axiom audit commands)
import AvailableChainFGSAClaims.Statements.Bounds -- shake: keep (axiom audit commands)

/-! Axiom audit. Add one `#print axioms` for each new public theorem.
The guard scans all compiled constants. -/

#print axioms AvailableChain.FGSA.Run.L
#print axioms AvailableChain.FGSA.Run.P
#print axioms AvailableChain.FGSA.Run.Γ
#print axioms AvailableChain.FGSA.Run.ρΓ
#print axioms AvailableChain.FGSA.Run.ρ₁
#print axioms AvailableChain.FGSA.Run.ρ
#print axioms AvailableChain.FGSA.Run.E_g
#print axioms AvailableChain.FGSA.Run.E_j
#print axioms AvailableChain.FGSA.Run.B_c
#print axioms AvailableChain.FGSA.Run.D_c
#print axioms AvailableChain.FGSA.Run.B_reset
#print axioms AvailableChain.FGSA.Run.B
#print axioms AvailableChain.FGSA.Run.B_H2
#print axioms AvailableChain.FGSA.Run.B_H1
#print axioms AvailableChain.FGSA.Run.B_H
#print axioms AvailableChain.FGSA.Run.W_F
#print axioms AvailableChain.FGSA.Run.B_F
#print axioms AvailableChain.FGSA.Run.B_heal
#print axioms AvailableChain.FGSA.Run.B_best
#print axioms AvailableChain.FGSA.Run.B_Q
#print axioms AvailableChain.FGSA.Run.B_skip
#print axioms AvailableChain.FGSA.Run.γ
#print axioms AvailableChain.FGSA.Run.carrierTime2
#print axioms AvailableChain.FGSA.Run.kernelDeadline
#print axioms AvailableChain.FGSA.Run.ActionDeliveryBounds
#print axioms AvailableChain.FGSA.Run.KernelBeforeNextAction
#print axioms AvailableChain.FGSA.Run.VoteBeforeAction
#print axioms AvailableChain.FGSA.Run.GateAfterCarrier2
#print axioms AvailableChain.FGSA.Run.GateActionOrder
#print axioms AvailableChain.FGSA.Run.FourteenBeforeTwoRounds

#print axioms AvailableChain.FGSA.Run.storeAt
#print axioms AvailableChain.FGSA.Run.S_at
#print axioms AvailableChain.FGSA.Run.F_at
#print axioms AvailableChain.FGSA.Run.J_at
#print axioms AvailableChain.FGSA.Run.gateIn
#print axioms AvailableChain.FGSA.Run.gateResult
#print axioms AvailableChain.FGSA.Run.isGateTime
#print axioms AvailableChain.FGSA.Run.IsGateTick
#print axioms AvailableChain.FGSA.Run.gateResultAt
#print axioms AvailableChain.FGSA.Run.gatePassedAt
#print axioms AvailableChain.FGSA.Run.fastAt
#print axioms AvailableChain.FGSA.Run.headAtIdx
#print axioms AvailableChain.FGSA.Run.vHead
#print axioms AvailableChain.FGSA.Run.actionSourceFG
#print axioms AvailableChain.FGSA.Run.actionSource
#print axioms AvailableChain.FGSA.Run.labelBoundAt
#print axioms AvailableChain.FGSA.Run.DeliveredAt
#print axioms AvailableChain.FGSA.Run.HandlesRowAt
#print axioms AvailableChain.FGSA.Run.AcceptsFinalBefore
#print axioms AvailableChain.FGSA.Run.cleanResults
#print axioms AvailableChain.FGSA.Run.BelowLabel

#print axioms AvailableChain.FGSA.Run.preTick_def
#print axioms AvailableChain.FGSA.Run.postClock_def
#print axioms AvailableChain.FGSA.Run.gateIn_def
#print axioms AvailableChain.FGSA.Run.gateResult_def
#print axioms AvailableChain.FGSA.Run.isGateTime_def
#print axioms AvailableChain.FGSA.Run.vHead_def
#print axioms AvailableChain.FGSA.Run.actionSourceFG_def
