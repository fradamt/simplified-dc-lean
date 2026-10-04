module
public import AvailableChainFGSARun.Statements.Roots
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]

/-- [ROOT-DIGEST W1; DC NamedReceiptCalls] A proposal call is a direct delivery. -/
theorem proposal_handlesS_direct (st : State p.n) (parent o : Obj p)
    (s : Slot) (b : Block) (raw sup : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (hd : (toWire p o).decode = some (.block s b raw sup rows))
    (hh : handlesS p st parent o) : parent = o := by
  rcases hh with h | h
  · exact h
  · cases hp : (toWire p parent).decode with
    | none => simp only [hp] at h
    | some m =>
      cases m with
      | vote r i B => simp only [hp] at h
      | row i body => simp only [hp] at h
      | block r B raw' sup' rows' =>
        rw [hp] at h
        rcases h.2 with hm | hm
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofHead, ofWire, ofAuth,
            toAuth, Wire.decode] at hd
        · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
          rcases a with ⟨⟨(_ | _), _⟩ | _ | _, _⟩ <;> simp [toWire, ofRow, ofWire, ofAuth, toAuth,
            Wire.decode] at hd

/-- [ROOT-DIGEST W1; DC NamedRun.blockInRun] A proposal handler scopes its body. -/
theorem proposal_handle_in_scope (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o = ofWire p ⟨.proposer s, .proposal b raw support rows⟩)
    (j : Nat) (w : V) (t : Time) (hh : V2.D.Run.handlesAt E rho j w o t) :
    RootBlockInRun p c E rho b := by
  obtain ⟨parent, hevent, hcall⟩ := hh
  have hd : (toWire p o).decode = some (.block s b raw support rows) := by
    rw [ho]
    rfl
  have hp := proposal_handlesS_direct _ parent o s b raw support rows hd hcall
  subst parent
  refine ⟨b, Or.inl ⟨w, o, t, raw, support, rows, ?_, ?_⟩, ?_⟩
  · exact List.mem_of_getElem? hevent
  · rw [ho]
    rfl
  · cases b <;> simp [Block.Preceq, Block.preceq]

/-- [ROOT-DIGEST W1; DC NamedReceiptCalls] Broadcast or source acceptance scopes a trigger.
This proof uses no root idealization or processed-to-body inference. -/
theorem proposal_trigger_in_scope
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (o : Obj p) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n))
    (ho : o = ofWire p ⟨.proposer s, .proposal b raw support rows⟩)
    (dl : Time → Time) (cut t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t) (hw : w ∈ rho.honest)
    (hcut : dl t ≤ cut)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    RootBlockInRun p c E rho b := by
  rcases hT with ⟨v, hv, hemit⟩ | ⟨v, _, i, haccept⟩
  · have hQ : ¬ isRowObject o := by
      rw [ho]
      simp [isRowObject, ofWire]
    obtain ⟨t', _, _, j, hh⟩ := hD.broadcast v hv o hQ t hemit w hw hcut hNX
    exact proposal_handle_in_scope E rho o s b raw support rows ho j w t' hh
  · exact proposal_handle_in_scope E rho o s b raw support rows ho i v t haccept.1

/-- [ROOT-DIGEST W1; DC NamedRootCollisionFree] Stored content agrees on scoped roots.
Signed rows follow from BODY validity. This does not equate raw or support lists. -/
theorem stored_content_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hr : NamedRootCollisionFree p c E rho)
    {b b' : Block} {raw support raw' support' : List (HeadWire p.n)}
    {rows rows' : List (RowWire p.n)}
    (hb : RootBlockInRun p c E rho b) (hb' : RootBlockInRun p c E rho b')
    (hc : contentOk p b raw support rows = true)
    (hc' : contentOk p b' raw' support' rows' = true)
    (he : b.root = b'.root) : b = b' ∧ rows = rows' := by
  have hbb := hr.root_injective b b' hb hb' b b'
    (Or.inl (block_preceq_refl b)) (Or.inr (block_preceq_refl b')) he
  subst b'
  exact ⟨rfl, rows_eq_of_rowsOk (contentOk_rowsOk hc) (contentOk_rowsOk hc')⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks] An app update recomputes the full content digest. -/
theorem contentOk_withApp (H : Block) (s : Slot) (r : BlockId) (body app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p app (.proposal (.node H s r body) raw support rows) =
      .proposal (proposalBlock p H s app raw support rows) raw support rows ∧
    contentOk p (proposalBlock p H s app raw support rows) raw support rows = true :=
  ⟨rfl, contentOk_proposalBlock p H s app raw support rows⟩

/-- [ROOT-DIGEST W1; DC NamedBlocks] A zero app update preserves the zero-app proposal. -/
theorem withApp_zero_proposalBlock (H : Block) (s : Slot)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    withApp p 0 (.proposal (proposalBlock p H s 0 raw support rows) raw support rows) =
      .proposal (proposalBlock p H s 0 raw support rows) raw support rows := rfl

/-- [ROOT-DIGEST W1; DC NamedBlocks] An app update preserves BODY validity. -/
theorem rowsOk_withApp_proposalBlock (H : Block) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    rowsOk (proposalBlock p H s app raw support rows) rows = true :=
  contentOk_rowsOk (contentOk_proposalBlock p H s app raw support rows)

end AvailableChain.FGSA.Run
end
