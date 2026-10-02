module
public import AvailableChainFGSAClaims.Statements.Windows
public import AvailableChainFGSA.Proofs.WindowTerminal

public section

namespace AvailableChain.FGSA.Run

/-- The named terminal-retention contract (f07w item 12, F8-W) holds: its body is
the pure window theorem `Window.terminalRetentionW`. -/
theorem fgsa_terminalRetentionW (p : Params) : TerminalRetention_W p := by
  rw [TerminalRetention_W_def]
  exact Window.terminalRetentionW p

end AvailableChain.FGSA.Run
end
