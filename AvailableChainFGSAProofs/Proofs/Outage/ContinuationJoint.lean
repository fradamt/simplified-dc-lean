module
public import AvailableChainFGSAProofs.Proofs.Outage.ScopedJoint
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationInduction
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationReceipt

/-! The scoped continuation body is supplied by ScopedJoint. The old
all-honest body has no current production caller and does not compile under
sleep. Its source remains in Git at de637290 and in the Round 13 evidence. -/
