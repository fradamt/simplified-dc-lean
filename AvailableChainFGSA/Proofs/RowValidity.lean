module
public import AvailableChainFGSA.Model.RowValidity
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainKitFG.RowBits

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- R6 preserves every parent field except the slot. -/
@[simp] theorem parentFoldState_slot (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    (parentFoldState p s P).s = s := rfl

/-- R6 is exactly a decoded, nonempty pair at the parent's height and entry. -/
theorem rowValidFor_iff {n : Nat} (σ : ChainState (Fin n)) (a : RowWire n) :
    rowValidFor σ a = true ↔ ∃ b, a.toRow? = some b ∧
      ∃ timeout, b.height_pair = .vote σ.h σ.T_h.root timeout := by
  delta rowValidFor
  cases hd : a.toRow? with
  | none => simp
  | some b =>
      cases hp : b.height_pair with
      | empty => simp [NamedHeightPair.matchesEntry, hp]
      | vote h e t => cases t <;> simp [NamedHeightPair.matchesEntry, hp]

/-- Changing the finality pair cannot change the R6 result. -/
theorem rowValidFor_finality_irrel {n : Nat} (σ : ChainState (Fin n))
    (auth : Auth Label n) (hp : NamedHeightPair) (fp gp : Option FinalityPair) :
    rowValidFor σ ⟨auth, ⟨hp, fp⟩⟩ = rowValidFor σ ⟨auth, ⟨hp, gp⟩⟩ := by
  cases auth with
  | seat l i => cases l <;> rfl
  | proposer | none => rfl

/-- All rows use the same parent state. -/
theorem rowsValidForParent_iff (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    (rows : List (RowWire p.n)) :
    rowsValidForParent p P s rows = true ↔
      ∀ a ∈ rows, rowValidFor (parentFoldState p s P) a = true := by
  change rows.all (rowValidFor (parentFoldState p s P)) = true ↔ _
  simp only [List.all_eq_true]

/-- The slot is set before the fold but cannot change the R6 height test. -/
theorem rowsValidForParent_slot_irrel (p : Params) (P : FGBlock (Fin p.n))
    (s t : Slot) (rows : List (RowWire p.n)) :
    rowsValidForParent p P s rows = rowsValidForParent p P t rows := rfl

/-- A permutation keeps the common-parent validity test. -/
theorem rowsValidForParent_perm (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    {rows rows' : List (RowWire p.n)} (h : rows.Perm rows') :
    rowsValidForParent p P s rows = rowsValidForParent p P s rows' := by
  rw [Bool.eq_iff_iff, rowsValidForParent_iff, rowsValidForParent_iff]
  simp only [h.mem_iff]

/-- The initial store has no carried-row obligation. -/
theorem rowsValidStored_initial (p : Params) : RowsValidStored p (initial p.n) := by
  intro o ho
  exact (List.not_mem_nil ho).elim

/-- The payload sum preserves the full vote body. -/
theorem encRowPayload_inj : Function.Injective encRowPayload := by
  rintro ⟨a⟩ ⟨b⟩ h
  have hab := encRowBody_inj (epair_inj h).2
  exact congrArg RowPayload.vote hab

/-- Converting a vote and restoring its body is exact. -/
theorem RowPayload.ofRow_toRow {V : Type} (a : RowPayload) (i : V) :
    RowPayload.vote (RowBody.ofRow (a.toRow i)) = a := by
  cases a with | vote b => cases b; rfl

/-- R6 supplies the progress bit at the first carried occurrence. -/
theorem rowValidFor_progress_first (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    (rows : List (RowWire p.n)) (a : RowWire p.n) (b : Row (Fin p.n))
    (ha : a ∈ rows) (hd : a.toRow? = some b)
    (hv : rowValidFor (parentFoldState p s P) a = true) :
    b.signer ∈ ((rows.filterMap RowWire.toRow?).foldl process_row
      (parentFoldState p s P)).progress := by
  apply KitFG.progress_first_inclusion _ _ b
  · exact List.mem_filterMap.mpr ⟨a, ha, hd⟩
  · delta rowValidFor at hv
    rw [hd] at hv
    exact hv

/-- Target, progress, and finality bits have the same persistence interface.
Finality requires its own match; R6 alone does not supply that premise. -/
theorem row_bit_persist (p : Params) (kind : KitFG.ChainBit)
    (P W : FGBlock (Fin p.n)) (s : Slot) (app : Nat)
    (rows : List (RowWire p.n)) (a : RowWire p.n) (b : Row (Fin p.n))
    (ha : a ∈ rows) (hd : a.toRow? = some b)
    (hCW : FGBlock.Preceq
      (.node P s (packInner app rows) (rows.filterMap RowWire.toRow?)) W)
    (hm : KitFG.rowMatchesBit kind (parentFoldState p s P) b)
    (hk : KitFG.sameBitState kind (derive p.E p.cfg P) (derive p.E p.cfg W)) :
    b.signer ∈ KitFG.chainBits kind (derive p.E p.cfg W) :=
  KitFG.bit_first_inclusion_persist p.E p.cfg kind P W s (packInner app rows)
    (rows.filterMap RowWire.toRow?) b (List.mem_filterMap.mpr ⟨a, ha, hd⟩) hCW hm hk

/-- Row processing keeps the R6 keys. Validation against the common pre-fold
state therefore does not depend on the row order. -/
theorem rowValidFor_fold {n : Nat} (σ : ChainState (Fin n))
    (rows : List (Row (Fin n))) (a : RowWire n) :
    rowValidFor (rows.foldl process_row σ) a = rowValidFor σ a := by
  obtain ⟨_, hh, hT, _⟩ := KitFG.foldl_process_row_fields rows σ
  delta rowValidFor
  cases a.toRow? <;> simp only [hh, hT]

/-- [R3/R6/R7] If a previously carried row matches finality later, its first
inclusion already supplied the bit. R3 is explicit until wire activation. -/
theorem rowValidFor_finality_persist (p : Params) (P W : FGBlock (Fin p.n))
    (s : Slot) (app : Nat) (rows : List (RowWire p.n))
    (a : RowWire p.n) (b : Row (Fin p.n))
    (ha : a ∈ rows) (hd : a.toRow? = some b)
    (hv : rowValidFor (parentFoldState p s P) a = true)
    (hR3 : ∀ h T χ fp, b.height_pair = .vote h T χ →
      b.finality_pair = some fp → fp.height < h)
    (hCW : FGBlock.Preceq
      (.node P s (packInner app rows) (rows.filterMap RowWire.toRow?)) W)
    (fp : FinalityPair) (hfp : b.finality_pair = some fp)
    (hm : KitFG.rowMatchesBit .finality (derive p.E p.cfg W) b) :
    b.signer ∈ (derive p.E p.cfg W).finalize := by
  obtain ⟨c, hc, χ, hp⟩ := (rowValidFor_iff (parentFoldState p s P) a).mp hv
  have hcb : c = b := Option.some.inj (hc.symm.trans hd)
  subst c
  exact KitFG.finality_first_inclusion_persist p.E p.cfg P W s (packInner app rows)
    (rows.filterMap RowWire.toRow?) b (List.mem_filterMap.mpr ⟨a, ha, hd⟩) hCW
    fp hfp (hR3 _ _ χ fp hp hfp) hm

end AvailableChain.FGSA
end
