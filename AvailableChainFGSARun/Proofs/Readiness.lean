module
public import AvailableChainFGSARun.Proofs.Hooks
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt
public import AvailableChainGeneric.Statements.V2.Duty.Receipt

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}

/-- An object that does not decode as a block has no dependencies. -/
theorem depsS_of_not_block (st : State p.n) (o : Obj p)
    (hNotBlock : ∀ s b raw sup rows,
      (toWire p o).decode ≠ some (.block s b raw sup rows)) :
    depsS p st o = true := by
  change (match (toWire p o).decode with
    | some (.block _ b _ _ _) => (parentFG st b).isSome
    | _ => true) = true
  cases hd : (toWire p o).decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body => rfl
    | block s b raw sup rows => exact False.elim (hNotBlock s b raw sup rows hd)

/-- A non-proposal payload has no dependencies, for any authentication. -/
theorem depsS_of_not_proposal (st : State p.n) (o : Obj p)
    (hNotProposal : ∀ b raw sup rows, o.payload ≠ .proposal b raw sup rows) :
    depsS p st o = true := by
  apply depsS_of_not_block st o
  intro s b raw sup rows hd
  have hp := congrArg Signed.payload (decode_eq_block.mp hd)
  exact hNotProposal b raw sup rows hp

variable {V : Type} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {dl : Time → Time} {t : Time} {w : V} {o : Obj p}

/-- The delivery wire check supplies well-formedness of each handled child. -/
theorem fgsa_hWF_of_delivery
    (hWire : ∀ (i : Nat) (v : V) (o' : Obj p) (t' : Time),
      rho.events[i]? = some (.deliver v o' t') →
      (fgsa p c).wellFormed o' = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true := by
  intro i t' _ hh
  obtain ⟨o', he, hh⟩ := hh
  exact handles_wellFormed p c _ o' o hh (hWire i w o' t' he)

/-- Readiness before the deadline for an object that does not decode as a block. -/
theorem fgsa_hReady_of_not_block
    (hNotBlock : ∀ s b raw sup rows,
      (toWire p o).decode ≠ some (.block s b raw sup rows))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i w) o = true := by
  intro i t' hi hh
  exact ⟨hWF i t' hi hh, depsS_of_not_block _ o hNotBlock⟩

/-- Proposal readiness reduces to its FG parent being stored at each handled event. -/
theorem fgsa_hReady_of_parentStored
    {s : Slot} {b : Block} {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hBlock : (toWire p o).decode = some (.block s b raw sup rows))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true)
    (hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
      V2.D.Run.handlesAt E rho i w o t' →
      (parentFG (V2.D.Run.stateBefore E rho i w).st b).isSome = true) :
    ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho i w) o = true := by
  intro i t' hi hh
  refine ⟨hWF i t' hi hh, ?_⟩
  change (match (toWire p o).decode with
    | some (.block _ b' _ _ _) => (parentFG (V2.D.Run.stateBefore E rho i w).st b').isSome
    | _ => true) = true
  rw [hBlock]
  exact hParent i t' hi hh

/-- [T7.12 input; lead decision (c)+(iii)] `accepted_by_deadline` for an FG-SA proposal,
with `hReady` discharged from `hWF` and the named parent hypothesis `hParent`
(the K8 dependency-ordering fact). The frozen Gen boundary is used unchanged. -/
theorem fgsa_accepted_by_deadline_of_parentStored
    {p : Params} {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {Timely : (fgsa p c).State → (fgsa p c).Object → Prop}
    {Inv : (fgsa p c).State → Prop}
    (dl : Time → Time) (cut : Time) (o : Obj p) (t : Time) (w : V)
    {s : Slot} {b : Block} {raw sup : List (HeadWire p.n)} {rows : List (RowWire p.n)}
    (hBlock : (toWire p o).decode = some (.block s b raw sup rows))
    (hWF : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) → V2.D.Run.handlesAt E rho i w o t' →
      (fgsa p c).wellFormed o = true)
    (hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
      V2.D.Run.handlesAt E rho i w o t' →
      (parentFG (V2.D.Run.stateBefore E rho i w).st b).isSome = true)
    (hD : Gen.V2.Duty.DeliveryWithin E rho dl cut)
    (hT : Gen.V2.Duty.Trigger E rho o t)
    (hw : w ∈ rho.honest) (hcut : dl t ≤ cut) (hlt : t < dl t)
    (hS : V2.D.ScheduleWellFormed E rho)
    (hES : ∀ v o i j, i ≤ j → V2.D.restartFree rho v i j →
      (fgsa p c).excludes (V2.D.Run.stateBefore E rho i v) o = true →
      (fgsa p c).excludes (V2.D.Run.stateBefore E rho j v) o = true)
    (hPS : ∀ v o i j, i ≤ j → V2.D.restartFree rho v i j →
      (fgsa p c).processed (V2.D.Run.stateBefore E rho i v) o = true →
      (fgsa p c).processed (V2.D.Run.stateBefore E rho j v) o = true)
    (hA : Gen.V2.Duty.AcceptanceLaw (fgsa p c) Timely Inv)
    (C : Gen.V2.Duty.TimelyClock (fgsa p c) Timely)
    (hInv : ∀ i, Inv (V2.D.Run.stateBefore E rho i w))
    (hAdm : C.actTime o ≤ Gen.V2.Duty.pubFloor E t)
    (j : Nat) (hj : rho.events[j]? = some (.tick w (Gen.V2.Duty.pubFloor E t)))
    (hrf : V2.D.restartFree rho w j (V2.D.Run.idxBefore rho (dl t)))
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho (dl t) w) o = true :=
  Gen.V2.Duty.accepted_by_deadline (P := fgsa p c) E rho dl cut o t w hD hT hw hcut hlt
    hS hES hPS (hReady := fgsa_hReady_of_parentStored hBlock hWF hParent)
    hA C hInv hAdm j hj hrf hNX

end AvailableChain.FGSA.Run
end
