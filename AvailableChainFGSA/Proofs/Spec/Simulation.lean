module
public import AvailableChainFGSA.Proofs.Spec.Clock
public import AvailableChainFGSA.Proofs.Spec.Handlers
public import AvailableChainFGSARun.Model.Protocol

public section

namespace AvailableChain.FGSA.Spec

/-! WP12b STOP: the all-wire recursive erasure does not preserve exact-parent refusal.
The checked local trace below starts at initialization, ticks at every public time,
and immediately delivers the receiver's own votes and FG rows. Validator 1 is awake;
validator 0 is the assigned proposer in every slot. The two received proposals are
adversarial. The spec refuses the second one because its full parent is absent.
No full run simulation is asserted. -/

/-- The last-tick cutoff can be removed at a gate when all stored votes precede it. -/
theorem spec_lateVotes_eq_pool (p : Params) (st : GridCO.State p.n .root) (s : Slot)
    (h : ∀ o ∈ GridCO.votesAt st s, GridCO.stampVote st o < SA.gateTime p.toParams s) :
    GridCO.lateVotes p.toParams.engine st s = GridCO.votesAt st s := by
  apply List.filter_eq_self.mpr
  intro o ho
  exact decide_eq_true (h o ho)

/-- The run adapter preserves the existing all-wire boundary check. -/
theorem spec_run_wire_check (p : Params) (assigned : Slot → Fin p.n) (o : Wire p.n) :
    (Run.fgsa p Run.unitCodec).wellFormed (Run.ofWire p (deliveryWire assigned o)) =
      (wellFormed p o && admissionValid assigned o) := by
  change FGSA.wellFormed p (Run.toWire p (Run.ofWire p (deliveryWire assigned o))) = _
  have hw : Run.toWire p (Run.ofWire p (deliveryWire assigned o)) =
      deliveryWire assigned o := (Run.toWireEquiv p).right_inv _
  rw [hw]
  exact delivery_check_embedding p assigned o

/-- Restart preserves the durable anti-slashing record and resets the Lean store. -/
theorem spec_restart_durable (p : Params) (nd : Run.Node p) :
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd)).record =
      nd.record ∧
    ((Run.fgsa p Run.unitCodec).restore ((Run.fgsa p Run.unitCodec).durable nd)).st.base.now =
      0 := ⟨rfl, rfl⟩

/-- The pinned spec keeps the clock at restart; raw clock equality cannot cover that cut. -/
theorem spec_restart_clock_mismatch (p : Params) (nd : Run.Node p) (t : Time) (ht : t ≠ 0) :
    ((Run.fgsa p Run.unitCodec).restore nd.record).st.base.now ≠ t := Ne.symm ht

/-- A small parameter set with distinct parent and child roots. -/
abbrev parentIdentityParams : Params :=
  { Δ := 1, n := 2, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide, R := 2, δt := 0,
    RLarge := by decide, digest := fun d => ⟨d.slot + 6⟩ }

def parentIdentityAssigned (_ : Slot) : Fin 2 := 0

def parentIdentityHeld : Block 2 := .node .genesis 1 0 ⟨7⟩ [] [] []

def parentIdentityAbsent : Block 2 := .node .genesis 1 1 ⟨7⟩ [] [] []

def parentIdentityChild : Block 2 := .node parentIdentityAbsent 2 0 ⟨8⟩ [] [] []

def parentIdentityGoodChild : Block 2 := .node parentIdentityHeld 2 0 ⟨8⟩ [] [] []

abbrev parentIdentityWire : Wire 2 := ⟨.proposer 2, .proposal parentIdentityChild⟩

/-- One awake local tick for validator 1, with immediate self-delivery.
Validator 1 has no proposal duty under the fixed assignment. -/
def parentIdentityTick (nd : Run.Node parentIdentityParams) (t : Nat) :
    Run.Node parentIdentityParams := Id.run do
  let p := parentIdentityParams
  let mut nd := { nd with st := FGSA.clock p nd.st t }
  let s := p.slotOf t
  if (t : Time) = SA.voteTime p.toParams s then
    let H := Next.headVoteNext p nd.st s
    nd := { nd with st := process p nd.st ⟨.seat (.head s) 1, .head H.root⟩ }
  if (t : Time) = p.actionTime ((s - 1) / p.R) then
    let (row, record) := Next.attestNext p nd.st nd.record 1
    nd := { nd with record := record }
    if let some a := row then
      nd := { nd with st := process p nd.st ⟨.seat .fg 1, .row a⟩ }
  return nd

/-- Public ticks 0 through 4, the valid parent delivery at 4, then ticks 5 through 8. -/
def parentIdentityBefore : Run.Node parentIdentityParams :=
  let nd := (List.range 5).foldl parentIdentityTick
    ⟨FGSA.initial 2, SimplexFG.RecordOnce.initial⟩
  let nd := { nd with
    st := process parentIdentityParams nd.st
      (Wire.embed ⟨.proposer 1, .proposal parentIdentityHeld⟩) }
  ([5, 6, 7, 8] : List Nat).foldl parentIdentityTick nd

/-- The all-wire erasure loses an ancestor identity even with a valid top proposer. -/
theorem spec_parent_identity_erasure :
    parentIdentityAbsent ≠ parentIdentityHeld ∧
    parentIdentityChild.parent ∉ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityGoodChild.parent ∈ ([.genesis, parentIdentityHeld] : List (Block 2)) ∧
    parentIdentityChild.embed = parentIdentityGoodChild.embed ∧
    deliveryWire parentIdentityAssigned parentIdentityWire =
      deliveryWire parentIdentityAssigned
        ⟨.proposer 2, .proposal parentIdentityGoodChild⟩ := by decide

set_option maxRecDepth 4096 in
/-- Concrete refusal mismatch at time 8, after every earlier public tick.
The checked parent set is exactly genesis and the first received proposal. -/
theorem spec_parent_identity_trace :
    parentIdentityBefore.st.namedBodies = [.genesis, parentIdentityHeld.embed] ∧
    parentIdentityBefore.st.base.now = 8 ∧
    wellFormed parentIdentityParams parentIdentityWire = true ∧
    admissionValid parentIdentityAssigned parentIdentityWire = true ∧
    FGSA.wellFormed parentIdentityParams
      (deliveryWire parentIdentityAssigned parentIdentityWire) = true ∧
    namedParentHeld parentIdentityBefore.st parentIdentityChild.embed = true ∧
    (process parentIdentityParams parentIdentityBefore.st
      (deliveryWire parentIdentityAssigned parentIdentityWire)).proposals.length = 2 := by
  decide

end AvailableChain.FGSA.Spec
end
