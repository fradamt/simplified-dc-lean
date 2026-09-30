module
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSAProofs.Proofs.Shared.Channels
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSARun.Proofs.Emission

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- Erasure preserves identity and order on all FG blocks, hence on run blocks.
This uses the existing derived-root carrier lemmas. -/
theorem fgsa_carrier_geometry {n : Nat} (X Y : FGBlock (Fin n)) :
    (eraseFG X = eraseFG Y → X = Y) ∧
    (FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y)) ∧
    eraseFG X.parent = (eraseFG X).parent ∧
    (eraseFG X).slot = X.slot ∧ (eraseFG X).root = X.root := by
  refine ⟨fun h => eraseFG_injective h, ⟨eraseFG_preceq, ?_⟩,
    (eraseFG_parent X).symm, eraseFG_slot X, eraseFG_root X⟩
  intro h
  exact preceq_of_eraseFG_preceq (Vw := ({X, Y} : Finset (FGBlock (Fin n))))
    (fun A B _ _ he => FGBlock.root_injective he)
    ⟨X, by simp, KitFG.preceq_refl X⟩ ⟨Y, by simp, KitFG.preceq_refl Y⟩ h

/-- Every held-chain row has an authenticated wire from a delivered proposal.
T7.5 supplies the stored wire and its delivery; unforgeability supplies the
honest holder's emission. No schedule or execution-validity premise is needed. -/
theorem held_chain_row_origin (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.Run V (fgsa p c))
    (hU : V2.UnforgeableSignatures E rho)
    (e : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho e x W) :
    ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
      RowWire.toRow? a = some u ∧ a.auth = .seat (.fg r) u.signer ∧
      ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a := by
  have hs := storeBundle_stateBefore E rho e x
  have held := hW.2
  clear hW
  induction W with
  | genesis => intro u hu; exact (Finset.notMem_empty u hu).elim
  | node P s body rows ih =>
      intro u hu
      change u ∈ rows.toFinset ∪ chainRows P at hu
      rcases (Finset.mem_union.mp hu).symm with hu | hu
      · exact ih (hs.cstore.fg.closed _ held) u hu
      · obtain ⟨slot, raw, sup, wires, hw, hr⟩ :=
          stored_wire_of_block p _ hs.cstore hs.«meta» held (by intro h; cases h)
        change rows = wires.filterMap RowWire.toRow? at hr
        have hur : u ∈ rows := List.mem_toFinset.mp hu
        rw [hr] at hur
        obtain ⟨a, ha, hau⟩ := List.mem_filterMap.mp hur
        have auth : ∃ r, a.auth = .seat (.fg r) u.signer := by
          rcases a with ⟨auth, payload⟩
          cases auth with
          | none => cases hau
          | proposer s => cases hau
          | seat label i =>
              cases label with
              | head s => cases hau
              | fg r =>
                  have he : (⟨i, payload.height_pair, payload.finality_pair⟩ : Row (Fin p.n)) = u :=
                    Option.some.inj hau
                  exact ⟨r, by rw [← he]⟩
        obtain ⟨r, har⟩ := auth
        refine ⟨a, r, hau, har, ?_⟩
        intro z hz hzh
        obtain ⟨j, o, t, _, hd, ho, _, _⟩ := stored_proposal_delivered E rho e x _ hw
        have he : o = ofWire p ⟨.proposer slot,
            .proposal (eraseFG (.node P s body rows)) raw sup wires⟩ := by
          apply toWire_injective
          rw [toWire_ofWire, ho]
        have hc : (fgsa p c).carries o (ofRow p a) := by
          rw [he]
          exact Or.inr (Or.inr (List.mem_map.mpr ⟨a, ha, rfl⟩))
        obtain ⟨t', _, k, hk, hem⟩ := fgsa_carried_row E rho hU x z o t ⟨j, hd⟩ a hc hzh
          ((rowSigner_iff_holder p c rho a z).mp hz).2
        exact ⟨k, t', hk, hem⟩

end AvailableChain.FGSA.Run
end
