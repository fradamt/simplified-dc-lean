module
public import AvailableChainFGSARun.Statements.AC
public import AvailableChainGeneric.Statements.V2.Duty.Receipt

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- K8 inputs (bp00:707–708; bp01:858–930).

`required o t` names an object and its original trigger time. `paths K d`
names a required authentic support path, from genesis to `K`, with cutoff
`d`. The `deadline` field assigns every non-genesis vertex its own proposal
receipt. It does not add a delay for each edge. A required carried HEAD has
its own trigger; receipt of its containing proposal is not that trigger.

The transport index range is `first .. idxBefore rho D`, including the final
read. Slot windows concern only the required objects and their receipt
intervals. The endpoint bound prevents old-label exclusion at the receipt
read; the handler bounds give the current/previous-slot HEAD vote window.
Proposals use the trigger's admission threshold (T7.8).

There is no store premise. `ExecutionValid`, stated separately below,
supplies the checked wire and dependency conditions of base receipt. -/
structure ReceiptCoveragePremises {p : Params} {In V : Type} [DecidableEq V]
    {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop) : Prop where
  within : Gen.V2.Duty.DeliveryWithin E rho dl cut
  slotWindow : ∀ o t, required o t →
    Gen.V2.Duty.Trigger E rho o t ∧ (fgsa p c).wellFormed o = true ∧
    (∀ s a K, (toWire p o).decode = some (.vote s a K) →
      ((V2.D.Run.stateBeforeTime E rho (dl t) x).st.slot p ≤ s + 1) ∧
      ∀ i t', first ≤ i → i < V2.D.Run.idxBefore rho (dl t) → t ≤ t' →
        V2.D.Run.handlesAt E rho i x o t' →
        s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
          (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1)
  compat : ∀ i, first ≤ i → i ≤ V2.D.Run.idxBefore rho D →
    Block.Compatible B (eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F)
  deadline : Monotone dl ∧ D ≤ cut ∧ cut ≤ rho.horizon ∧
    first ≤ V2.D.Run.idxBefore rho D ∧
    (∀ o t, required o t → first ≤ V2.D.Run.idxBefore rho t ∧
      0 ≤ t ∧ t < dl t ∧ dl t ≤ D) ∧
    (∀ K d, paths K d → Block.Preceq B K ∧ d ≤ D ∧
      ∀ b, Block.Preceq b K → b ≠ .genesis →
        ∃ o t s raw sup rows, required o t ∧
          (toWire p o).decode = some (.block s b raw sup rows) ∧ dl t ≤ d) ∧
    (∀ o t s b raw sup rows, required o t →
      (toWire p o).decode = some (.block s b raw sup rows) →
      ∃ K d, paths K d ∧ Block.Preceq b K)

/-- `bp.receiptCoverage.v1` (K8), one statement for Clean, P1 and Recovery.
Source: bp00:700–713; bp01 §10:858–930; plan T7.12a.

The split is at the strict deadline read. Coverage includes the output,
all positive-slot HEAD votes, every `getHead` view, the finality head, and
absence of conflicting leases. Otherwise each required proposal is stored
at its original receipt deadline, and each required path is stored at its
specified cutoff. This includes vertices already stored or below finality.
Vote retention or stamped same-seat evidence holds in both branches, at
the final read, with stamps strictly before the vote's original deadline.

Readiness check for T7.12 (no extra premise):

* `hWF` is `fgsa_hWF_of_delivery hExecution.wire`.
* HEAD/row: their decoders cannot be `.block`; use
  `fgsa_hReady_of_not_block` with `hWF`.
* Proposal decoded as `.block s b raw sup rows`: use
  `fgsa_hReady_of_parentStored` with `hWF` and EXACTLY

  `hParent : ∀ i t', i < V2.D.Run.idxBefore rho (dl t) →
    V2.D.Run.handlesAt E rho i w o t' →
    (parentFG (V2.D.Run.stateBefore E rho i w).st b).isSome = true`.

  T7.12 derives this from the checked dependencies of base receipt:
  a proposal cannot be a carried child in `handlesS` (children are only
  HEADs/rows). Thus its handler call is a direct delivery; `hExecution.deps`
  gives `depsS`, which the block decoder identifies with `parentFG.isSome`.
  This applies to ALL earlier handler calls, including those before `t`;
  no restriction to a selected delivery witness is needed. Path admission
  in parent order uses the vertex receipts named in `deadline`. Neither
  `hParent` nor the reconciliation store premise `hL` is a field here.

`hNoRestart` supplies every `restartFree` interval. `hDelta` aligns the
generic clock with the instance clock. No bound `dl t ≤ t + p.Δ` is used. -/
def ReceiptCoverageStatement : Prop :=
  ∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
    (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
    E.Δ = p.Δ → V2.D.ExecutionValid E rho → V2.D.NoRestart rho → x ∈ rho.honest →
    ReceiptCoveragePremises E rho dl cut D first x B required paths →
    let st := (V2.D.Run.stateBeforeTime E rho D x).st
    ((Block.Preceq B (eraseFG st.fg.F) ∧
      Block.Preceq B st.base.stableRecord ∧
      (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
      (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
      Block.Preceq B (fgHead p st) ∧
      (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
     (Block.Preceq (eraseFG st.fg.F) B ∧
      (∀ o t s b raw sup rows, required o t →
        (toWire p o).decode = some (.block s b raw sup rows) →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = b) ∧
      (∀ K d, paths K d → ∀ b, Block.Preceq b K →
        ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
    (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
      let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
      (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
      ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
        v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
        GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
        GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t)

theorem ReceiptCoverageStatement_def :
    ReceiptCoverageStatement =
      (∀ {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
        (dl : Time → Time) (cut D : Time) (first : Nat) (x : V) (B : Block)
        (required : Obj p → Time → Prop) (paths : Block → Time → Prop),
        E.Δ = p.Δ → V2.D.ExecutionValid E rho → V2.D.NoRestart rho → x ∈ rho.honest →
        ReceiptCoveragePremises E rho dl cut D first x B required paths →
        let st := (V2.D.Run.stateBeforeTime E rho D x).st
        ((Block.Preceq B (eraseFG st.fg.F) ∧
          Block.Preceq B st.base.stableRecord ∧
          (∀ s, 0 < s → Block.Preceq B (headVote p st s)) ∧
          (∀ raw sup, Block.Preceq B (getHead p st raw sup)) ∧
          Block.Preceq B (fgHead p st) ∧
          (∀ lease ∈ st.base.obligations, Block.Compatible B lease.1)) ∨
         (Block.Preceq (eraseFG st.fg.F) B ∧
          (∀ o t s b raw sup rows, required o t →
            (toWire p o).decode = some (.block s b raw sup rows) →
            ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho (dl t) x).st.fg.TF, eraseFG Y = b) ∧
          (∀ K d, paths K d → ∀ b, Block.Preceq b K →
            ∃ Y ∈ (V2.D.Run.stateBeforeTime E rho d x).st.fg.TF, eraseFG Y = b))) ∧
        (∀ o t s a K, required o t → (toWire p o).decode = some (.vote s a K) →
          let v := baseVote (⟨.seat (.head s) a, K⟩ : HeadWire p.n)
          (v ∈ st.base.votes ∧ GridCO.stampVote st.base v < dl t) ∨
          ∃ v₁ ∈ st.base.votes, ∃ v₂ ∈ st.base.votes,
            v₁ ≠ v₂ ∧ GridCO.headLabel? v₁ = some s ∧ GridCO.headLabel? v₂ = some s ∧
            GridCO.headSeat? v₁ = some a ∧ GridCO.headSeat? v₂ = some a ∧
            GridCO.stampVote st.base v₁ < dl t ∧ GridCO.stampVote st.base v₂ < dl t)) := by
  rw [ReceiptCoverageStatement]

end AvailableChain.FGSA.Run
end
