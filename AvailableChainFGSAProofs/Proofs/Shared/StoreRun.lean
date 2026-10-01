module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainKitV2.DutyStable

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Fixed store data persist through a restart-free interval. The KitV2 core
uses the E-16 own-record fold; FG-SA clock/process supply all six fields. -/
theorem fgsa_store_cumulative (hnr : V2.D.NoRestart rho) {i j : Nat} (hij : i ≤ j) (x : V) :
    let a := storeAt p c E rho i x
    let b := storeAt p c E rho j x
    a.fg.TF ⊆ b.fg.TF ∧ a.base.blocks <+: b.base.blocks ∧
    a.base.blockStamp <+: b.base.blockStamp ∧ a.base.voteStamp <+: b.base.voteStamp ∧
    a.proposals <+: b.proposals ∧ a.rowPool <+: b.rowPool := by
  let a := storeAt p c E rho i x
  apply V2.D.Engine.stateBefore_stable (P := fgsa p c)
    (fun nd => a.fg.TF ⊆ nd.st.fg.TF ∧ a.base.blocks <+: nd.st.base.blocks ∧
      a.base.blockStamp <+: nd.st.base.blockStamp ∧ a.base.voteStamp <+: nd.st.base.voteStamp ∧
      a.proposals <+: nd.st.proposals ∧ a.rowPool <+: nd.st.rowPool)
    ?_ ?_ (fun _ _ h => h) E rho hij x (hnr.restartFree x i j)
    ⟨subset_rfl, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
      List.prefix_refl _, List.prefix_refl _⟩
  · intro nd t h
    change a.fg.TF ⊆ (clock p nd.st t).fg.TF ∧
      a.base.blocks <+: (clock p nd.st t).base.blocks ∧
      a.base.blockStamp <+: (clock p nd.st t).base.blockStamp ∧
      a.base.voteStamp <+: (clock p nd.st t).base.voteStamp ∧
      a.proposals <+: (clock p nd.st t).proposals ∧ a.rowPool <+: (clock p nd.st t).rowPool
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := clock_cumulative p nd.st t
    rw [h1, h2, h3, h4, h5, h6]
    exact h
  · intro nd o h
    have hc := process_cumulative p nd.st (toWire p o)
    exact ⟨Finset.Subset.trans h.1 hc.1, h.2.1.trans hc.2.1,
      h.2.2.1.trans hc.2.2.1, h.2.2.2.1.trans hc.2.2.2.1,
      h.2.2.2.2.1.trans hc.2.2.2.2.1, h.2.2.2.2.2.trans hc.2.2.2.2.2⟩

end AvailableChain.FGSA.Run
end
