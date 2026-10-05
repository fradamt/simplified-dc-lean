module
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC `ReviewTheorem.lean:298` uses authentic stored rows for honestNeverSlashed.
Port of the d35bac1 read-chain route to W and fixed FG seats (F-H).
Replay the inclusive time filter to find a delivery in the original run.
Unforgeability then gives each honest signer's emission. No event order,
horizon, or execution-validity premise is needed. -/
theorem readAt_chain_row_origin (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (V2.D.Run.readAt E rho t x).st.fg.TF)
    (u : Row (Fin p.n)) (hu : u ∈ chainRows W) :
    ∃ a : RowWire p.n,
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a := by
  let rho' := { rho with events := rho.events.filter (fun e => decide (e.time ≤ t)) }
  have hs : V2.D.World.step E rho' = V2.D.World.step E rho := by
    funext w e
    cases e <;> rfl
  have hr : V2.D.Run.stateBefore E rho' rho'.events.length = V2.D.Run.readAt E rho t := by
    change (rho'.events.take rho'.events.length).foldl (V2.D.World.step E rho')
      V2.D.World.init = _
    rw [List.take_length, hs]
    rfl
  have hb := storeBundle_readAt E rho t x
  induction W with
  | genesis => exact (Finset.notMem_empty u hu).elim
  | node P s root body rows ih =>
      change u ∈ rows.toFinset ∪ chainRows P at hu
      rcases (Finset.mem_union.mp hu).symm with hu | hu
      · exact ih (hb.cstore.fg.closed _ hW) hu
      · have held : FGBlock.node P s root body rows ∈
            (storeAt p c E rho' rho'.events.length x).fg.TF := by
          change FGBlock.node P s root body rows ∈ (V2.D.Run.stateBefore E rho' _ x).st.fg.TF
          rw [hr]
          exact hW
        obtain ⟨slot, N, _, heRows, j, o, td, _, hd, he⟩ :=
          stored_block_wire_delivery p c E rho' rho'.events.length x _ held
            (by intro h; cases h)
        change rows = N.rows.filterMap RowWire.toRow? at heRows
        have hur : u ∈ rows := List.mem_toFinset.mp hu
        rw [heRows] at hur
        obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp hur
        have har := row_auth_of_toRow a u hau
        have hm : V2.Event.deliver x o td ∈ rho.events :=
          (List.mem_filter.mp (List.mem_of_getElem? hd)).1
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hm
        have hc : (fgsa p c).carries o (ofRow p a) := by
          rw [he]
          exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
        refine ⟨a, hau, har, ?_⟩
        intro z hz hzh
        obtain ⟨t', _, i, hi, hem⟩ := fgsa_carried_row E rho hU x z o td
          ⟨k, hk⟩ a hc hzh ((rowSigner_iff_holder p c rho a z).mp hz).2
        exact ⟨i, t', hi, hem⟩

end AvailableChain.FGSA.Run
end
